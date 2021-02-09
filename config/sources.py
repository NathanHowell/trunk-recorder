import csv
import json
from collections import defaultdict
from dataclasses import dataclass
from enum import Enum, auto
from itertools import chain
from pathlib import Path
from typing import DefaultDict, Dict, Iterable, Iterator, List, Optional, Tuple, Union

import z3


BANDWIDTH: int = 12500
HALFWIDTH: int = BANDWIDTH // 2


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
    ranges: List[z3.ExprRef]
    lower_freq: List[z3.ArithRef]
    upper_freq: List[z3.ArithRef]


@dataclass
class Source:
    center: int
    rate: int
    analog_recorders: int
    digital_recorders: int


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
        last = {}
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
            row = _parse_analog(row)
            if row is not None:
                yield row


def _hz(x: str) -> int:
    return int(float(x.replace("c", "").replace("a", "")) * 1000000)


def _problem(
    solver: Union[z3.Optimize, z3.Solver],
    freqs: Iterable[int],
    devices: int = 16,
    sample_rates: Optional[List[Tuple[int, int]]] = None,
) -> Problem:
    """
    :param solver: a Z3 solver
    :param freqs: list of frequencies in hertz
    :param devices: maximum number of radios to solve for
    :param sample_rates: list of supported sample rates ranges
    :return:
    """

    if sample_rates is None:
        # default to rtl-sdr dongle ranges
        # sample_rates = [(225001, 300000), (900001, 3200000)]
        sample_rates = [(225001, 300000), (900001, 2560000)]

    # define a frequency range per device
    lower_freq = [z3.Int(f"lower_{i}") for i in range(devices)]
    upper_freq = [z3.Int(f"upper_{i}") for i in range(devices)]

    # order the frequencies so the model is nicer to look at when debugging
    for x, y in zip(lower_freq, lower_freq[1:]):
        solver.add(x < y)

    ranges = [upper - lower for lower, upper in zip(lower_freq, upper_freq)]

    for i, r in enumerate(ranges):
        # not sure if this is the right amount but it works for me
        padded_r = r + BANDWIDTH

        solver.add(
            z3.Or(
                # sample rates of 0 exclude a device from the solution
                r == 0,
                # if not zero, the sample rate must be in a valid range
                *[z3.And(padded_r >= l, padded_r <= h) for l, h in sample_rates],
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

        # and that at least one device covers the range
        # this is a bit when solving for a large number of devices
        # and we still get a unique assignment by minimizing the frequency range
        solver.add(z3.Or(*in_range))

        # this is the equivalent unique assertion, do not use:
        # solver.add(z3.PbEq([(x, 1) for x in in_range], 1))

    return Problem(
        ranges=ranges,
        lower_freq=lower_freq,
        upper_freq=upper_freq,
    )


def _solve(solver: z3.Optimize, channels: List[Channel]) -> Tuple[Problem, z3.Model]:
    problem = _problem(solver, [c.frequency for c in channels])
    if solver.check() != z3.sat:
        # TODO: consider getting an unsat core
        raise ValueError(f"No valid assignment possible")

    # find the minimal number of devices that cover all frequencies
    # it is faster to do this iteratively than to offload these to
    # smt constraints
    for r in problem.ranges:
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
    print(f"Devices required: {model.eval(devices_required)}")

    return problem, model


def _main():
    channels = list(chain(_analog(Path("analog.tsv")), _digital(Path("digital.tsv"))))

    solver = z3.Optimize()
    problem, model = _solve(solver, channels)
    sources: List[Source] = []
    for lower, upper in zip(problem.lower_freq, problem.upper_freq):
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
                )
            )

    with open("config.json", "rb") as h:
        config = json.load(h)

    for i, x in enumerate(sources):
        source = config["sources"][i]
        source["center"] = x.center
        source["rate"] = x.rate
        source["digitalRecorders"] = x.digital_recorders
        source["analogRecorders"] = x.analog_recorders

    control_channels: DefaultDict[int, List[Channel]] = defaultdict(list)
    for c in channels:
        if c.signal != Signal.digital:
            continue
        elif c.tag is None:
            continue

        assert c.system is not None
        control_channels[c.system].append(c)

    # order the control channels so primaries are first
    # followed by alternates in frequency order
    sorted_control_channels = {
        k: sorted(
            v, key=lambda x: -x.frequency if x.tag == Tag.primary else x.frequency
        )
        for k, v in control_channels.items()
    }

    # update the config systems
    systems = config["systems"]
    for k in control_channels.keys():
        systems[k]["control_channels"] = [
            c.frequency for c in sorted_control_channels[k]
        ]

    print(json.dumps(config, indent=2))


if __name__ == "__main__":
    _main()
