#!/usr/bin/env python3
"""Longest path through the proof build, weighted by measured compile times.

Reads the dependency graph coqdep wrote to .Makefile.rocq.d and the per-file
<file>.v.timing data a TIMING=1 build leaves behind, then prints the chain of
files that bounds the wall time of any parallel build. Files without timing
data count as zero and are listed so the gap is visible.

Usage, from proof/: python3 doc/critical_path.py [--top N]
"""

import argparse
import os
import re
import sys

DEPS_FILE = ".Makefile.rocq.d"
SECS = re.compile(r" ([0-9.]+) secs ")


def read_graph():
    graph = {}
    with open(DEPS_FILE) as handle:
        for line in handle:
            targets, _, deps = line.partition(":")
            target = targets.split()[0]
            if not target.endswith(".vo"):
                continue
            graph[target] = [dep for dep in deps.split() if dep.endswith(".vo")]
    return graph


def read_time(vo):
    timing = vo[: -len(".vo")] + ".v.timing"
    if not os.path.exists(timing):
        return None
    total = 0.0
    with open(timing) as handle:
        for line in handle:
            match = SECS.search(line)
            if match:
                total += float(match.group(1))
    return total


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=15, help="files to list by own time")
    args = parser.parse_args()

    graph = read_graph()
    times = {}
    missing = []
    for vo in graph:
        measured = read_time(vo)
        if measured is None:
            missing.append(vo)
            measured = 0.0
        times[vo] = measured

    # Longest path ending at each file; the graph is a DAG so memoised recursion is safe.
    finish = {}
    via = {}

    def longest(vo):
        if vo in finish:
            return finish[vo]
        best, best_dep = 0.0, None
        for dep in graph.get(vo, []):
            candidate = longest(dep)
            if candidate > best:
                best, best_dep = candidate, dep
        finish[vo] = best + times[vo]
        via[vo] = best_dep
        return finish[vo]

    sys.setrecursionlimit(10000)
    for vo in graph:
        longest(vo)

    total = sum(times.values())
    end = max(finish, key=finish.get)
    chain = []
    cursor = end
    while cursor is not None:
        chain.append(cursor)
        cursor = via[cursor]
    chain.reverse()

    print(f"files: {len(graph)}, with timing data: {len(graph) - len(missing)}")
    print(f"sum of compile times: {total:.0f} s")
    print(f"critical path: {finish[end]:.0f} s, so the parallel floor is {finish[end] / max(total, 1e-9) * 100:.0f}% of the serial time")
    print()
    print("critical path chain (own time, finish time):")
    for vo in chain:
        print(f"  {times[vo]:9.1f}  {finish[vo]:9.1f}  {vo}")
    print()
    print(f"top {args.top} files by own time:")
    for vo in sorted(times, key=times.get, reverse=True)[: args.top]:
        print(f"  {times[vo]:9.1f}  {vo}")
    if missing:
        print()
        print(f"{len(missing)} files without .v.timing data, counted as 0 s:")
        for vo in missing:
            print(f"  {vo}")


if __name__ == "__main__":
    main()
