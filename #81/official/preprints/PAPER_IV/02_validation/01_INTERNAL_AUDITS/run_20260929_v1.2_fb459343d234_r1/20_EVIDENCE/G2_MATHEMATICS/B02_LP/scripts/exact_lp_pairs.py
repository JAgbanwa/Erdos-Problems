"""Finite mixed primal/dual LP regression with exact rational replay.

SciPy is only a candidate generator. The acceptance tests below use Fraction.
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import combinations
from pathlib import Path

from scipy.optimize import linprog


HERE = Path(__file__).resolve().parents[1]


def edge_set(n: int, mask: int) -> tuple[tuple[int, int], ...]:
    return tuple(e for i, e in enumerate(combinations(range(n), 2)) if mask & (1 << i))


def items(n: int, edges: tuple[tuple[int, int], ...]) -> list[tuple[tuple[int, ...], int]]:
    e_set = set(edges)
    return [(vertices, 2 if size == 3 else 5)
            for size in (3, 4) for vertices in combinations(range(n), size)
            if set(combinations(vertices, 2)) <= e_set]


def rational(x: float) -> Fraction:
    q = Fraction(float(x)).limit_denominator(10000)
    if abs(float(q) - x) > 1e-8:
        raise AssertionError((x, q, "rational reconstruction not justified"))
    return q


def verify(edges: tuple[tuple[int, int], ...],
           ks: list[tuple[tuple[int, ...], int]],
           x: list[Fraction], y: list[Fraction]) -> tuple[bool, str]:
    if len(x) != len(ks) or len(y) != len(edges):
        return False, "dimension"
    if any(a < 0 for a in x) or any(b < 0 for b in y):
        return False, "negative_coordinate"
    for e in edges:
        if sum((x[j] for j, (vs, _) in enumerate(ks)
                if e in combinations(vs, 2)), Fraction()) > 1:
            return False, "primal_overload"
    for j, (vs, gain) in enumerate(ks):
        if sum((y[i] for i, e in enumerate(edges) if e in combinations(vs, 2)),
               Fraction()) < gain:
            return False, "dual_underprice"
    primal = sum((gain * x[j] for j, (_, gain) in enumerate(ks)), Fraction())
    dual = sum(y, Fraction())
    if primal != dual:
        return False, "objectives_differ"
    return True, "equal_feasible_pair"


def solve(n: int, edges: tuple[tuple[int, int], ...]):
    ks = items(n, edges)
    if not ks:
        x, y = [], [Fraction() for _ in edges]
    else:
        matrix = [[int(e in combinations(vs, 2)) for vs, _ in ks] for e in edges]
        gains = [gain for _, gain in ks]
        primal = linprog([-g for g in gains], A_ub=matrix,
                         b_ub=[1] * len(edges), bounds=(0, None), method="highs")
        dual = linprog([1] * len(edges),
                       A_ub=[[-row[j] for row in matrix] for j in range(len(ks))],
                       b_ub=[-g for g in gains], bounds=(0, None), method="highs")
        if not primal.success or not dual.success:
            raise AssertionError((primal.message, dual.message))
        x = [rational(float(v)) for v in primal.x]
        y = [rational(float(v)) for v in dual.x]
    good, reason = verify(edges, ks, x, y)
    if not good:
        raise AssertionError((n, edges, reason, x, y))
    value = sum((gain * x[j] for j, (_, gain) in enumerate(ks)), Fraction())
    return ks, x, y, value


def main() -> None:
    count = 0
    mixed = 0
    noninteger = 0
    sample = []
    for n in range(5):
        for mask in range(1 << (n * (n - 1) // 2)):
            edges = edge_set(n, mask)
            ks, x, y, value = solve(n, edges)
            count += 1
            if any(len(vs) == 4 for vs, _ in ks):
                mixed += 1
            if value.denominator > 1:
                noninteger += 1
            if n == 4 and mask == 63:
                sample.append({"graph": "K4", "primal": [str(z) for z in x],
                               "dual": [str(z) for z in y], "value": str(value),
                               "items": [(list(v), g) for v, g in ks]})

    # Independent checker must reject arithmetic and capacity mutations.
    k4 = edge_set(4, 63)
    ks, x, y, _ = solve(4, k4)
    negatives = {}
    variants = {
        "primal_overload": ([Fraction(2)] * len(ks), y),
        "dual_underprice": (x, [Fraction()] * len(y)),
        "objectives_differ": ([Fraction()] * len(x), y),
        "negative_coordinate": ([-Fraction(1)] + x[1:], y),
    }
    for expected, (px, py) in variants.items():
        ok, reason = verify(k4, ks, px, py)
        if ok or reason != expected:
            raise AssertionError((expected, reason))
        negatives[expected] = reason

    output = {"domain": "all labelled graphs n=0..4", "graphs": count,
              "graphs_with_K4_item": mixed, "fractional_value_noninteger": noninteger,
              "sample": sample, "negative_controls": negatives,
              "checker": "Fraction exact arithmetic after floating-point candidate generation",
              "limit": "Finite LP pairs do not prove general duality or the mixed-model bridge."}
    path = HERE / "results" / "exact_lp_pairs.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in output.items() if k != "sample"}, indent=2))


if __name__ == "__main__":
    main()
