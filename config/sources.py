#!/usr/bin/env python3
import argparse
import csv
import json
import sys
from collections import defaultdict
from dataclasses import dataclass
from enum import Enum, auto
from itertools import chain, count
from json import JSONEncoder
from pathlib import Path
from typing import (
    DefaultDict,
    Dict,
    Iterable,
    Iterator,
    List,
    Optional,
    Tuple,
    Union,
    Any,
    Protocol,
)

import z3


BANDWIDTH: int = 12500
HALFWIDTH: int = BANDWIDTH // 2


@dataclass
class Device:
    sample_rates: List[Union[int, Tuple[int, int]]]
    ppm: int
    driver: str
    device: str
    gain: int

    @property
    def min_sample_rate(self) -> int:
        x = sys.maxsize
        for s in self.sample_rates:
            if isinstance(s, tuple):
                x = min(x, s[0])
            elif isinstance(s, int):
                x = min(x, s)
            else:
                raise AssertionError()
        return x


DEVICES = {
    "rtlsdr": Device(
        sample_rates=[(225001, 300000), (900001, 2560000)],
        ppm=1,
        driver="osmosdr",
        device="rtl={}",
        gain=24,
    ),
    "airspy": Device(
        sample_rates=[2500000, 10000000],
        ppm=1,
        driver="osmosdr",
        device="airspy={}",
        gain=24,
    ),
}


class Signal(Enum):
    analog = auto()
    digital = auto()


class Tag(Enum):
    primary = auto()
    alternate = auto()


@dataclass
class Channel:
    frequency: int
    signal: Signal
    tag: Optional[Tag] = None
    system: Optional[int] = None


@dataclass
class Problem:
    ranges: List[z3.ArithRef]
    lower_freq: List[z3.ArithRef]
    upper_freq: List[z3.ArithRef]
    devices: List[Device]


@dataclass
class Source:
    center: int
    rate: int
    gain: int
    driver: str
    device: str
    error: Optional[int] = None
    analog_recorders: Optional[int] = None
    debug_recorders: Optional[int] = None
    digital_recorders: Optional[int] = None


@dataclass
class System:
    control_channels: List[int]
    type: str
    short_name: str
    min_duration: int
    talkgroups_file: Path
    modulation: str


@dataclass
class Config:
    sources: List[Source]
    systems: List[System]
    capture_dir: Path


def _strip(x):
    if isinstance(x, dict):
        return {k.strip(): _strip(v) for k, v in x.items()}
    elif isinstance(x, str):
        return x.strip()
    elif isinstance(x, list):
        x = (_strip(y) for y in x)
        return [y for y in x if y not in {"", None}]
    else:
        raise ValueError()


def _parse_digital(row: Dict[str, str], system: int) -> Iterator[Channel]:
    for x in row.get("Freqs", []):
        tag: Optional[Tag]
        if "c" in x:
            tag = Tag.primary
        elif "a" in x:
            tag = Tag.alternate
        else:
            tag = None

        yield Channel(
            signal=Signal.digital,
            frequency=_hz(x),
            tag=tag,
            system=system,
        )


def _digital_multiline(source: Path) -> Iterator[Dict[str, str]]:
    with source.open("rt") as h:
        header = [
            x for x in h.readline().strip().split("\t") if x not in {" ", "Freqs"}
        ]
        reader = csv.DictReader(h, fieldnames=header, delimiter="\t", restkey="Freqs")
        # RFSS	Site	Name	Freqs
        last: Dict[str, str] = {}
        for i, row in enumerate(reader):
            row = _strip(row)

            # funny business to deal with multiline TSVs
            if len(row["Name"].strip()) > 0:
                if len(last) > 0:
                    yield last

                last = row
            else:
                last["Freqs"] += row["Freqs"]

        yield last


def _digital(source: Path) -> Iterator[Channel]:
    for i, row in enumerate(_digital_multiline(source)):
        for x in _parse_digital(row, i):
            yield x


def _parse_analog(row: Dict[str, str]) -> Optional[Channel]:
    if "Frequency" in row:
        return Channel(
            signal=Signal.analog,
            frequency=_hz(row["Frequency"]),
        )
    else:
        return None


def _analog(source: Path) -> Iterator[Channel]:
    with source.open("rt") as h:
        reader = csv.DictReader(h, delimiter="\t")
        # Frequency 	License 	Type 	Tone 	Alpha Tag 	Description 	Mode 	Tag
        for row in reader:
            row = _strip(row)
            parsed_row = _parse_analog(row)
            if parsed_row is not None:
                yield parsed_row


def _hz(x: str) -> int:
    return int(float(x.replace("c", "").replace("a", "")) * 1000000)


class CreateConstraint(Protocol):
    def __call__(self, rate: z3.AstRef) -> z3.AstRef:
        ...


def _rate_constraint(
    rates: List[Union[int, Tuple[int, int]]]
) -> Iterator[CreateConstraint]:
    for rate in rates:
        if isinstance(rate, tuple):
            l, h = rate
            yield lambda r: z3.And(r >= l, r <= h)
        elif isinstance(rate, int):
            yield lambda r: r == rate
        else:
            raise AssertionError()


def _problem(
    solver: Union[z3.Optimize, z3.Solver],
    freqs: Iterable[int],
    devices: List[Device],
) -> Problem:
    """
    :param solver: a Z3 solver
    :param freqs: list of frequencies in hertz
    :param devices: maximum number of radios to solve for
    :param sample_rates: list of supported sample rates ranges
    :return:
    """

    # define a frequency range per device
    lower_freq = [z3.Int(f"lower_{i}") for i in range(len(devices))]
    upper_freq = [z3.Int(f"upper_{i}") for i in range(len(devices))]

    # order the frequencies so the model is nicer to look at when debugging
    for x, y in zip(lower_freq, lower_freq[1:]):
        solver.add(x < y)

    ranges = [upper - lower for lower, upper in zip(lower_freq, upper_freq)]

    for i, r, device in zip(count(), ranges, devices):
        solver.add(
            z3.Or(
                # sample rates of 0 exclude a device from the solution
                r == 0,
                # if not zero, the sample rate must be in a valid range
                *[c(r) for c in _rate_constraint(device.sample_rates)],
            )
        )

        # arbitrarily constrain the sample rate to a multiple of channel bandwidth
        # this is not necessary but it makes for a cleaner looking config file
        solver.add(r == BANDWIDTH * z3.Int(f"mult_{i}"))

    for freq in freqs:
        # ensure that the device frequency range covers each channel frequency
        in_range = [
            z3.And(
                freq >= lower + HALFWIDTH,
                freq <= upper - HALFWIDTH,
                # ensure the center frequency isn't directly on an in-use frequency
                z3.Or(
                    freq - HALFWIDTH >= (upper + lower) / 2,
                    freq + HALFWIDTH <= (upper + lower) / 2,
                ),
            )
            for lower, upper in zip(lower_freq, upper_freq)
        ]

        # and that at least one device covers this frequency...
        # this is a bit faster when solving for a large number of devices
        # compared to PbEq and a unique assignment will still be found by
        # minimizing the frequency range of each device
        solver.add(z3.Or(*in_range))

        # this is the equivalent unique assertion, do not use:
        # solver.add(z3.PbEq([(x, 1) for x in in_range], 1))

    return Problem(
        ranges=ranges,
        lower_freq=lower_freq,
        upper_freq=upper_freq,
        devices=devices,
    )


def _solve(
    solver: z3.Optimize, channels: List[Channel], devices: List[Device]
) -> Tuple[Problem, z3.Model]:
    problem = _problem(solver, freqs=[c.frequency for c in channels], devices=devices)
    if solver.check() != z3.sat:
        # TODO: consider getting an unsat core
        raise ValueError(f"No valid assignment possible, add more devices")

    # find the minimal number of devices that cover all frequencies
    # it is faster to do this iteratively than to offload these to
    # smt constraints. do this in reverse so we end up assigning
    # the lowest numbered devices
    for r in problem.ranges[::-1]:
        # to control the device placements adjust the order they're eliminated from
        # the solution. for example, this will prefer devices that have a smaller
        # minimum sample rate over devices with a larger one:
        # for r, _ in zip(problem.ranges, problem.devices), key=lambda x: -x[1].min_sample_rate
        solver.push()
        solver.add(r == 0)
        if solver.check() != z3.sat:
            solver.pop()
            break

    devices_required = z3.Sum([z3.If(r > 0, 1, 0) for r in problem.ranges])

    # minimize the sum of frequency ranges
    solver.minimize(z3.Sum(*problem.ranges))
    # and the frequency, just to produce deterministic results
    solver.minimize(z3.Sum(*problem.lower_freq))

    assert solver.check() == z3.sat

    model = solver.model()
    print(f"Devices required: {model.eval(devices_required)}", file=sys.stderr)

    return problem, model


def _get_sources(
    model: z3.Model,
    problem: Problem,
    channels: List[Channel],
) -> List[Source]:
    sources: List[Source] = []
    for i, lower, upper, device in zip(
        count(), problem.lower_freq, problem.upper_freq, problem.devices
    ):
        lower = model.eval(lower).as_long()
        upper = model.eval(upper).as_long()

        if lower != upper:
            analog_recorders = sum(
                lower <= x.frequency <= upper
                for x in channels
                if x.signal == Signal.analog
            )

            # count digital frequencies that are not control channels
            digital_recorders = sum(
                lower <= x.frequency <= upper
                for x in channels
                if x.signal == Signal.digital and x.tag is None
            )

            sources.append(
                Source(
                    center=(upper + lower) // 2,
                    rate=upper - lower,
                    analog_recorders=analog_recorders,
                    digital_recorders=digital_recorders,
                    gain=24,
                    driver=device.driver,
                    device=device.device.format(i),
                )
            )

    return sources


def _get_digital_systems(channels: List[Channel]) -> List[System]:
    channels = [c for c in channels if c.signal == Signal.digital]
    control_channels: DefaultDict[int, List[Channel]] = defaultdict(list)
    for c in channels:
        if c.tag is None:
            continue

        assert c.system is not None
        control_channels[c.system].append(c)

    # order the control channels so the primary is first followed by alternates
    sorted_control_channels = {
        k: sorted(
            v, key=lambda x: -x.frequency if x.tag == Tag.primary else x.frequency
        )
        for k, v in control_channels.items()
    }

    # update the config systems
    systems: List[System] = []
    for k in control_channels.keys():
        systems.append(
            System(
                control_channels=[c.frequency for c in sorted_control_channels[k]],
                modulation="qpsk",
                type="p25",
                short_name="...",
                talkgroups_file=Path("...-talkgroups.csv"),
                min_duration=0,
            )
        )

    return systems


def _get_analog_systems(channels: List[Channel]) -> List[System]:
    return []


def _config(model: z3.Model, problem: Problem, channels: List[Channel]) -> Config:
    return Config(
        sources=_get_sources(model, problem, channels),
        systems=_get_digital_systems(channels) + _get_analog_systems(channels),
        capture_dir=Path("/media"),
    )


class ConfigEncoder(JSONEncoder):
    def default(self, o: Any) -> Any:
        if isinstance(o, Config):
            return {
                "sources": o.sources,
                "systems": o.systems,
                "captureDir": o.capture_dir,
            }
        elif isinstance(o, Source):
            return {
                "center": o.center,
                "rate": o.rate,
                "gain": o.gain,
                "error": o.error or 0,
                "ppm": 0,
                "driver": o.driver,
                "device": o.device,
                "debugRecorders": o.debug_recorders or 0,
                "digitalRecorders": o.digital_recorders or 0,
                "analogRecorders": o.analog_recorders or 0,
            }
        elif isinstance(o, System):
            return {
                "control_channels": o.control_channels,
                "type": o.type,
                "shortName": o.short_name,
                "minDuration": o.min_duration,
                "talkgroupsFile": o.talkgroups_file,
                "modulation": o.modulation,
            }
        elif isinstance(o, Path):
            return str(o)
        else:
            return super().default(o)


def _main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "device",
        type=lambda x: DEVICES[x],
        nargs="+",
        action="append",
    )
    # parser.add_argument("--max_msps", metavar="RATE", type=float, default=None)
    parser.add_argument("--analog", metavar="FILE", type=Path)
    parser.add_argument("--digital", metavar="FILE", type=Path)
    parser.add_argument("--devices", metavar="COUNT", type=int, default=1)
    args = parser.parse_args()

    devices = list(chain.from_iterable(args.device))
    if len(devices) > 1 and args.devices > 1:
        print("--devices is only supported for a single device type", file=sys.stderr)
        sys.exit(1)
    devices *= args.devices

    if args.analog is None and args.digital is None:
        print("Please specify at least one source file")
        sys.exit(1)

    channels = []
    if args.analog is not None:
        print(f"Parsing {args.analog}", file=sys.stderr)
        channels.extend(_analog(args.analog))
    if args.digital is not None:
        print(f"Parsing {args.digital}", file=sys.stderr)
        channels.extend(_digital(args.digital))

    if len(channels) == 0:
        print("No channels found", file=sys.stderr)
        sys.exit(1)

    print("Solving for these frequencies:", file=sys.stderr)
    for c in channels:
        print(f"  {c.frequency} {c.signal.name}", file=sys.stderr)

    solver = z3.Optimize()
    problem, model = _solve(solver, channels, devices)
    config = _config(model, problem, channels)
    config_json = json.dumps(config, cls=ConfigEncoder, indent=2)
    print(config_json)


if __name__ == "__main__":
    _main()
