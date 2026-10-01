"""Exact small split partitions and integer parabola regression.

The finite dynamic program is independent of the closed split formula.
"""

from __future__ import annotations

import json
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path


HERE = Path(__file__).resolve().parents[1]


def split_edges(k: int, h: int) -> set[tuple[int, int]]:
    return set(combinations(range(k), 2)) | {
        (u, v) for u in range(k) for v in range(k, k + h)
    }


def exact_clique_partition(k: int, h: int, max_piece: int) -> int:
    n = k + h
    edges = sorted(split_edges(k, h))
    index = {e: i for i, e in enumerate(edges)}
    per_edge = [[] for _ in edges]
    for size in range(2, min(max_piece, n) + 1):
        for vertices in combinations(range(n), size):
            induced = list(combinations(vertices, 2))
            if all(e in index for e in induced):
                bits = sum(1 << index[e] for e in induced)
                for e in induced:
                    per_edge[index[e]].append(bits)

    @lru_cache(None)
    def minimum(remaining: int) -> int:
        if not remaining:
            return 0
        i = (remaining & -remaining).bit_length() - 1
        return 1 + min(minimum(remaining ^ bits) for bits in per_edge[i]
                       if bits & remaining == bits)

    return minimum((1 << len(edges)) - 1)


def baseline(n: int, k: int) -> int:
    return k * (n - k) - comb(k, 2)


def main() -> None:
    cases = []
    for n in range(4, 8):
        for k in range(2, n // 2 + 1):
            h = n - k
            unrestricted = exact_clique_partition(k, h, n)
            at_most_four = exact_clique_partition(k, h, 4)
            expected = baseline(n, k)
            if unrestricted != expected or at_most_four != expected:
                raise AssertionError((n, k, unrestricted, at_most_four, expected))
            cases.append({"n": n, "core": k, "hosts": h,
                          "cp": unrestricted, "c4": at_most_four,
                          "baseline": expected})

    parabola_count = 0
    double_maxima = []
    for n in range(6, 301):
        target = n * (n + 1) // 6
        values = [baseline(n, k) for k in range(n + 1)]
        maxima = [k for k, v in enumerate(values) if v == max(values)]
        expected = [n // 3, n // 3 + 1] if n % 3 == 1 else [n // 3] if n % 3 == 0 else [n // 3 + 1]
        if maxima != expected or max(values) != target:
            raise AssertionError((n, maxima, expected, target))
        if len(maxima) == 2:
            double_maxima.append(n)
        for k, value in enumerate(values):
            if 6 * value + (n - 3 * k) * (n - 3 * k + 1) != n * (n + 1):
                raise AssertionError((n, k, "parabola"))
            parabola_count += 1

    result = {"small_split_domain": "2<=core<=hosts, 4<=n<=7",
              "small_split_cases": cases, "parabola_domain": "6<=n<=300, 0<=k<=n",
              "parabola_checks": parabola_count,
              "double_maxima_orders": double_maxima,
              "limit": "Exact finite regression; neither the asymptotic lower bound nor the universal theorem is proved by enumeration."}
    path = HERE / "results" / "split_values.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"small_split_count": len(cases), "parabola_checks": parabola_count,
                      "double_maxima_count": len(double_maxima)}, indent=2))


if __name__ == "__main__":
    main()
