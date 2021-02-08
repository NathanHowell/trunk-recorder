import csv
import itertools
from dataclasses import dataclass
from typing import Dict, Iterator, Iterable, List, Union

import z3


MAX_MSP: int = 2560000
BANDWIDTH: int = 12500
HALFWIDTH: int = BANDWIDTH // 2
DEVICES: int = 16


def strip(x):
    if isinstance(x, dict):
        return {k.strip(): strip(v) for k, v in x.items()}
    elif isinstance(x, str):
        return x.strip()
    elif isinstance(x, list):
        x = (strip(y) for y in x)
        return [y for y in x if y not in {"", None}]
    else:
        raise ValueError()


def digital() -> Iterator[Dict[str, object]]:
    with open("digital.tsv", "rt") as h:
        header = [x for x in h.readline().strip().split("\t") if x not in {" ", "Freqs"}]
        reader = csv.DictReader(h, fieldnames=header, delimiter="\t", restkey="Freqs")
        # RFSS	Site	Name	Freqs
        last = {}
        for row in reader:
            row = strip(row)

            if len(row["Name"].strip()) > 0:
                if len(last) > 0:
                    yield last
                last = row
            else:
                last["Freqs"] += row["Freqs"]

        yield last


def analog() -> Iterator[Dict[str, object]]:
    with open("analog.tsv", "rt") as h:
        reader = csv.DictReader(h, delimiter="\t")
        # Frequency 	License 	Type 	Tone 	Alpha Tag 	Description 	Mode 	Tag
        for row in reader:
            row = strip(row)

            yield(row)


def _hz(x: str) -> int:
    return int(float(x.replace("c", "").replace("a", "")) * 1000000)


@dataclass
class Problem:
    ranges: List[z3.ExprRef]
    lower_freq: List[z3.ArithRef]
    upper_freq: List[z3.ArithRef]


def _problem(solver: Union[z3.Optimize, z3.Solver], freqs: Iterable[int]) -> Problem:
    lower_freq = [z3.Int(f"lower_{i}") for i in range(DEVICES)]
    upper_freq = [z3.Int(f"upper_{i}") for i in range(DEVICES)]
    # order the frequencies to make it nicer to look at the resulting model
    for x, y in zip(lower_freq, lower_freq[1:]):
        solver.add(x < y)

    ranges = [upper - lower for lower, upper in zip(lower_freq, upper_freq)]
    for i, r in enumerate(ranges):
        solver.add(r + BANDWIDTH < MAX_MSP)
        solver.add(r >= 0)
        # this is slower than dividing the constant frequencies by bandwidth
        # but it's easier to reason about
        solver.add(r == BANDWIDTH * z3.Int(f"mult_{i}"))

    # # find the smallest range that satisfies the device count
    # solver.minimize(r)

    for freq in freqs:
        in_range = [
            z3.And(
                freq - HALFWIDTH >= lower,
                freq + HALFWIDTH <= upper,
                # ensure the center frequency isn't directly on an in-use frequency
                z3.Or(
                    freq - HALFWIDTH >= (upper + lower) / 2,
                    freq + HALFWIDTH <= (upper + lower) / 2,
                    ),
                )
            for lower, upper in zip(lower_freq, upper_freq)
        ]

        solver.add(z3.AtLeast(*in_range, 1))

    return Problem(
        ranges=ranges,
        lower_freq=lower_freq,
        upper_freq=upper_freq,
    )


def _main():
    freqs = set()
    for row in itertools.chain(analog(), digital()):
        freqs.update(_hz(x) for x in row.get("Freqs", []))
        if "Frequency" in row:
            freqs.add(_hz(row["Frequency"]))

    solver = z3.Optimize()
    problem = _problem(solver, freqs)
    assert solver.check() == z3.sat

    # find the minimal number of devices that cover all frequencies
    for r in problem.ranges:
        solver.push()
        solver.add(r == 0)
        if solver.check() != z3.sat:
            solver.pop()
            break

    # minimize the frequency ranges
    solver.minimize(z3.Sum(*problem.ranges))
    # and the frequency to produce deterministic results
    solver.minimize(z3.Sum(*problem.lower_freq))
    assert solver.check() == z3.sat

    model = solver.model()
    for lower, upper in zip(problem.lower_freq, problem.upper_freq):
        lower = model.eval(lower).as_long()
        upper = model.eval(upper).as_long()
        if lower != upper:
            print(lower, upper, upper - lower, (upper + lower) // 2)


if __name__ == '__main__':
    _main()
