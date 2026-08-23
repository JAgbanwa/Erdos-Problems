from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp
from scipy.optimize import linprog


TOL = 1e-8


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def clique_edges(p: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(p) for j in range(i + 1, p)]


def split_lp(p: int, neighborhoods: tuple[tuple[int, ...], ...]) -> tuple[float, int]:
    independent = list(range(p, p + len(neighborhoods)))
    edges = set(clique_edges(p))
    triangles: list[tuple[tuple[int, int], ...]] = []
    for i, j, k in itertools.combinations(range(p), 3):
        triangles.append(((i, j), (i, k), (j, k)))
    for vertex, neighborhood in zip(independent, neighborhoods):
        for x in neighborhood:
            edges.add((x, vertex))
        for x, y in itertools.combinations(neighborhood, 2):
            triangles.append(((x, y), (x, vertex), (y, vertex)))
    if not triangles:
        return 0.0, len(edges)
    edge_list = sorted(edges)
    edge_index = {edge: index for index, edge in enumerate(edge_list)}
    matrix = np.zeros((len(edge_list), len(triangles)))
    for column, triangle in enumerate(triangles):
        for edge in triangle:
            matrix[edge_index[edge], column] = 1.0
    result = linprog(
        -np.ones(len(triangles)),
        A_ub=matrix,
        b_ub=np.ones(len(edge_list)),
        bounds=[(0, None)] * len(triangles),
        method="highs",
    )
    if not result.success:
        raise AssertionError(result.message)
    return float(-result.fun), len(edge_list)


def orbit_lp(p: int, s: int, q: int) -> float:
    o = p - s
    a_weight = s * (s - 1 - q) / 2
    b_weight = s * o
    g_weight = o * (o - 1) / 2
    rows: list[list[float]] = []
    rhs: list[float] = []

    def constraint(a: float, b: float, g: float) -> None:
        rows.append([-a, -b, -g])
        rhs.append(-1.0)

    if s >= 3:
        constraint(3, 0, 0)
    if o >= 1:
        constraint(1, 2, 0)
    if o >= 2:
        constraint(0, 2, 1)
    if o >= 3:
        constraint(0, 0, 3)
    result = linprog(
        np.array([a_weight, b_weight, g_weight]),
        A_ub=np.array(rows) if rows else None,
        b_ub=np.array(rhs) if rhs else None,
        bounds=[(0, 1)] * 3,
        method="highs",
    )
    if not result.success:
        raise AssertionError(result.message)
    return float(result.fun)


def orbit_closed(p: int, s: int, q: int) -> float:
    o = p - s
    a = s * (s - 1 - q) / 2
    b = s * o
    c = o * (o - 1) / 2
    uniform = (a + b + c) / 3
    separated = a + c
    hybrid = a + (b + c) / 3
    return min(uniform, separated) if o <= 2 else min(uniform, separated, hybrid)


def orbit_closed_fraction(p: int, s: int, q: int) -> Fraction:
    o = p - s
    a = Fraction(s * (s - 1 - q), 2)
    b = Fraction(s * o)
    c = Fraction(o * (o - 1), 2)
    uniform = (a + b + c) / 3
    separated = a + c
    hybrid = a + (b + c) / 3
    return min(uniform, separated) if o <= 2 else min(uniform, separated, hybrid)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manuscript", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    args = parser.parse_args()

    p, q, s = sp.symbols("p q s", nonnegative=True)
    o = p - s
    A = s * (s - 1 - q) / 2
    B = s * o
    C = o * (o - 1) / 2
    U = (A + B + C) / 3
    D = A + C
    H = A + (B + C) / 3
    R = (2 * p**2 - 2 * p * q - q**2) / 12
    identities = [
        (12 * (U - R), q * (2 * o + q) - 2 * p),
        (12 * (D - R), 12 * o**2 - 6 * o * (2 * p - q) + (2 * p - q) ** 2 - 6 * p),
        (12 * (H - R), (2 * s - q) ** 2 + 2 * q * (p - s) - 2 * p - 4 * s),
        (p * (p - 1) / 2 - 2 * R + p, (p + q) ** 2 / 6 + p / 2),
    ]
    u, v = sp.symbols("u v")
    identities.append((12 * u**2 - 6 * u * v + v**2, 12 * (u - v / 4) ** 2 + v**2 / 4))
    exact_pass = sum(sp.simplify(lhs - rhs) == 0 for lhs, rhs in identities)
    if exact_pass != len(identities):
        raise AssertionError("symbolic identity failure")

    # Regression for the corrected boundary wording in the tightness remark.
    # The s=2 lower bound of 1/4 is asserted only when o=p-s is positive;
    # (p,q,s)=(2,4,2) is the explicit zero-slack equality case.
    boundary_count = 0
    for p_value in range(3, 17):
        s_value = 2
        for q_value in range(1, 41):
            r_value = Fraction(2 * p_value**2 - 2 * p_value * q_value - q_value**2, 12)
            slack = orbit_closed_fraction(p_value, s_value, q_value) - (r_value - Fraction(p_value, 2))
            if slack < Fraction(1, 4):
                raise AssertionError(("tightness boundary", p_value, q_value, s_value, slack))
            boundary_count += 1
    equality_r = Fraction(2 * 2**2 - 2 * 2 * 4 - 4**2, 12)
    equality_slack = orbit_closed_fraction(2, 2, 4) - (equality_r - 1)
    if equality_slack != 0:
        raise AssertionError(("tightness equality", equality_slack))

    orbit_count = 0
    for p_value in range(2, 10):
        for q_value in range(1, 2 * p_value + 1):
            for s_value in range(2, p_value + 1):
                actual = orbit_lp(p_value, s_value, q_value)
                expected = orbit_closed(p_value, s_value, q_value)
                if abs(actual - expected) > TOL:
                    raise AssertionError((p_value, q_value, s_value, actual, expected))
                orbit_count += 1

    assembly_count = 0
    for p_value in range(0, 21):
        for q_value in range(0, 41):
            for b1 in range(0, 11):
                for isolated in range(0, 11):
                    if b1 > 0 and p_value == 0:
                        continue
                    n = p_value + q_value + b1 + isolated
                    difference = Fraction(n * n, 6) + Fraction(n, 2) - (
                        Fraction((p_value + q_value) ** 2, 6) + Fraction(p_value, 2) + b1
                    )
                    if difference < 0:
                        raise AssertionError((p_value, q_value, b1, isolated, difference))
                    assembly_count += 1

    falsification_count = 0
    for p_value in range(1, 5):
        subsets = [tuple(x for x in range(p_value) if mask & (1 << x)) for mask in range(1 << p_value)]
        for independent_count in range(0, 4):
            for neighborhoods in itertools.combinations_with_replacement(subsets, independent_count):
                nu_star, edge_count = split_lp(p_value, neighborhoods)
                n = p_value + independent_count
                bound = n * n / 6 + n / 2
                if edge_count - 2 * nu_star > bound + TOL:
                    raise AssertionError((p_value, neighborhoods, edge_count, nu_star, bound))
                falsification_count += 1

    benchmark_count = 0
    for p_value in range(2, 11):
        neighborhoods = (tuple(range(p_value)),) * (2 * p_value)
        nu_star, edge_count = split_lp(p_value, neighborhoods)
        n = 3 * p_value
        expected = n * n / 6 + n / 6
        if abs((edge_count - 2 * nu_star) - expected) > TOL:
            raise AssertionError((p_value, edge_count, nu_star, expected))
        benchmark_count += 1

    summary = {
        "paper": "PAPER_I",
        "claim_gate": "G2_MATHEMATICS",
        "target_sha256": sha256(args.manuscript),
        "status": "PASS",
        "exact_symbolic_identities": {"passed": exact_pass, "total": len(identities)},
        "tightness_boundary_regression_instances": boundary_count + 1,
        "orbit_program_instances": orbit_count,
        "final_assembly_exact_grid_instances": assembly_count,
        "split_graph_lp_falsification_instances": falsification_count,
        "complete_split_sharpness_instances": benchmark_count,
        "scope": "Exact identities and exact-rational assembly checks; bounded LP falsification is corroborating evidence, not an unbounded proof.",
    }
    rendered = json.dumps(summary, indent=2) + "\n"
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(rendered, encoding="utf-8")
    args.log.write_text(rendered + "EXIT_CODE=0\n", encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
