"""Independent induced-cycle classification for the n<=6 literal census."""

from __future__ import annotations

import json
from itertools import combinations, permutations
from pathlib import Path


HERE = Path(__file__).resolve().parents[1]


def patterns(n):
    edge_index = {e: i for i, e in enumerate(combinations(range(n), 2))}
    patterns_found = set()
    for size in range(4, n + 1):
        for vertices in combinations(range(n), size):
            all_bits = sum(1 << edge_index[e] for e in combinations(vertices, 2))
            start = vertices[0]
            for tail in permutations(vertices[1:]):
                order = (start,) + tail
                cycle_edges = {tuple(sorted((order[i], order[(i + 1) % size])))
                               for i in range(size)}
                cycle_bits = sum(1 << edge_index[e] for e in cycle_edges)
                patterns_found.add((all_bits, cycle_bits))
    return sorted(patterns_found)


def chordal_by_cycles(mask, forbidden):
    return not any(mask & all_bits == cycle_bits for all_bits, cycle_bits in forbidden)


def chordal_by_peeling(n, mask):
    edge_index = {e: i for i, e in enumerate(combinations(range(n), 2))}

    def adjacent(u, v):
        return bool(mask & (1 << edge_index[tuple(sorted((u, v)))]))

    def peel(vertices):
        if not vertices:
            return True
        for v in vertices:
            neighbors = [u for u in vertices if u != v and adjacent(u, v)]
            if all(adjacent(u, w) for u, w in combinations(neighbors, 2)):
                if peel(vertices - {v}):
                    return True
        return False

    return peel(set(range(n)))


def main():
    total = 0
    chordal_count = 0
    pattern_counts = {}
    for n in range(7):
        forbidden = patterns(n)
        pattern_counts[str(n)] = len(forbidden)
        for mask in range(1 << (n * (n - 1) // 2)):
            by_cycles = chordal_by_cycles(mask, forbidden)
            by_peeling = chordal_by_peeling(n, mask)
            if by_cycles != by_peeling:
                raise AssertionError((n, mask, by_cycles, by_peeling))
            total += 1
            chordal_count += by_cycles
    if chordal_count != 19049 or total != 33868:
        raise AssertionError((total, chordal_count))
    # A square is rejected; adding either diagonal destroys that witness.
    square = {(0, 1), (1, 2), (2, 3), (0, 3)}
    order = list(combinations(range(4), 2))
    square_mask = sum(1 << i for i, e in enumerate(order) if e in square)
    if chordal_by_cycles(square_mask, patterns(4)):
        raise AssertionError("induced C4 accepted")
    for diagonal in ((0, 2), (1, 3)):
        fixed = square_mask | (1 << order.index(diagonal))
        if not chordal_by_cycles(fixed, patterns(4)):
            raise AssertionError("chorded square rejected")
    result = {"domain": "all 33868 labelled graphs n=0..6",
              "cycle_patterns_by_n": pattern_counts,
              "chordal_graphs": chordal_count,
              "independent_classifiers_agree": True,
              "negative_control": "induced C4 rejected; either diagonal repairs it",
              "limit": "Finite regression. PEO and induced-cycle characterizations are formal/theoretical inputs, not proved here."}
    path = HERE / "results" / "cycle_chordality.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
