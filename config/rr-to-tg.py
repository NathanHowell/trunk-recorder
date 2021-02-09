#!/usr/bin/env python3
import csv
import sys

with open("svrcs-rr.tsv", "rt", newline="") as h:
    r = csv.reader(h, delimiter="\t")

    table = []
    for rw in r:
        rw = [x.strip().replace(",", "").replace("  ", " ") for x in rw]
        # print(rw)
        # dec, hex, mode, alpha, description, tag, group, priority
        if rw[6] == "Palo Alto":
            priority = 1
        elif rw[6] == "Los Altos":
            priority = 2
        elif rw[6] == "Mountain View":
            priority = 3
        elif rw[6] == "Santa Clara County Sheriff":
            priority = 4
        else:
            priority = 20

        if "Police" in rw[4]:
            priority *= 1
        elif "Fire" in rw[4]:
            priority *= 10
        elif "Public Works" in rw[5]:
            priority *= 20
        else:
            priority *= 30

        table.append(rw[:7] + [priority])

priorities = {row[7] for row in table}
lookup = {v: k for k, v in enumerate(sorted(priorities))}
table = [row[:7] + [lookup[row[7]]] for row in table]


with open("svrcs-talkgroups.csv", "wt") as h:
    w = csv.writer(h)
    for row in table:
        w.writerow(row)


if __name__ == "__main__":
    pass
