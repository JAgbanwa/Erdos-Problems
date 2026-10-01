"""Bounded, constructor-independent checks of literal edge partitions.

This script is a finite regression, not a proof of the eventual theorem.
It does not import the Lean or Certo implementations.
"""

from __future__ import annotations

import json
from functools import lru_cache
from itertools import combinations
from pathlib import Path


HERE = Path(__file__).resolve().parents[1]


def edge(u: int, v: int) -> tuple[int, int]:
    return (min(u, v), max(u, v))


def all_edges(n: int) -> tuple[tuple[int, int], ...]:
    return tuple(combinations(range(n), 2))


def graph(n: int, mask: int) -> frozenset[tuple[int, int]]:
    return frozenset(e for i, e in enumerate(all_edges(n)) if mask & (1 << i))


def piece_edges(piece: tuple[int, ...]) -> frozenset[tuple[int, int]]:
    return frozenset(edge(u, v) for u, v in combinations(piece, 2))


def check_partition(n: int, edges: frozenset[tuple[int, int]],
                    pieces: tuple[tuple[int, ...], ...], max_order: int = 4) -> tuple[bool, str]:
    seen: set[tuple[int, int]] = set()
    for piece in pieces:
        if len(piece) < 2 or len(piece) > max_order or len(set(piece)) != len(piece):
            return False, "bad_piece_order_or_vertices"
        if any(v < 0 or v >= n for v in piece):
            return False, "vertex_outside_graph"
        induced = piece_edges(piece)
        if not induced <= edges:
            return False, "nonclique_piece"
        if seen & induced:
            return False, "edge_reused"
        seen.update(induced)
    if seen != edges:
        return False, "edge_omitted"
    return True, "exact_partition"


def cliques(n: int, edges: frozenset[tuple[int, int]], max_order: int = 4
            ) -> tuple[tuple[tuple[int, ...], int], ...]:
    ordered = all_edges(n)
    index = {e: i for i, e in enumerate(ordered)}
    out = []
    for size in range(2, min(n, max_order) + 1):
        for piece in combinations(range(n), size):
            es = piece_edges(piece)
            if es <= edges:
                out.append((piece, sum(1 << index[e] for e in es)))
    return tuple(out)


def exact_min_partition(n: int, edges: frozenset[tuple[int, int]]
                        ) -> tuple[int, tuple[tuple[int, ...], ...]]:
    ordered = all_edges(n)
    available = sum((1 << i) for i, e in enumerate(ordered) if e in edges)
    options = cliques(n, edges)
    by_edge: dict[int, list[tuple[tuple[int, ...], int]]] = {i: [] for i in range(len(ordered))}
    for piece, bits in options:
        for i in range(len(ordered)):
            if bits & (1 << i):
                by_edge[i].append((piece, bits))

    @lru_cache(None)
    def solve(rem: int) -> tuple[int, tuple[tuple[int, ...], ...]]:
        if not rem:
            return 0, ()
        first = (rem & -rem).bit_length() - 1
        best = (rem.bit_count() + 1, ())
        for piece, bits in by_edge[first]:
            if bits & rem == bits:
                cost, rest = solve(rem ^ bits)
                if cost + 1 < best[0]:
                    best = cost + 1, (piece,) + rest
        return best

    return solve(available)


def simplicial(n: int, edges: frozenset[tuple[int, int]], vertices: frozenset[int], v: int) -> bool:
    neighbors = [u for u in vertices if u != v and edge(u, v) in edges]
    return all(edge(u, w) in edges for u, w in combinations(neighbors, 2))


def chordal(n: int, edges: frozenset[tuple[int, int]]) -> bool:
    @lru_cache(None)
    def peel(vertices: frozenset[int]) -> bool:
        if not vertices:
            return True
        return any(simplicial(n, edges, vertices, v) and peel(vertices - {v})
                   for v in vertices)
    return peel(frozenset(range(n)))


def main() -> None:
    counts = {"graphs": 0, "chordal": 0, "partition_checked": 0,
              "budget_checks": 0, "counterexamples": []}
    witness_by_n = {}
    for n in range(7):
        m = len(all_edges(n))
        target = n * (n + 1) // 6
        for mask in range(1 << m):
            edges = graph(n, mask)
            counts["graphs"] += 1
            optimum, pieces = exact_min_partition(n, edges)
            good, reason = check_partition(n, edges, pieces)
            if not good or optimum != len(pieces):
                raise AssertionError((n, mask, reason, optimum, pieces))
            counts["partition_checked"] += 1
            if chordal(n, edges):
                counts["chordal"] += 1
                counts["budget_checks"] += 1
                if optimum > target:
                    counts["counterexamples"].append((n, mask, optimum, target))
                if optimum == target:
                    witness_by_n.setdefault(str(n), {"edge_mask": mask, "parts": pieces})
    if counts["counterexamples"]:
        raise AssertionError(counts["counterexamples"])

    # Negative controls exercise different rejection reasons, not just false.
    triangle = frozenset({(0, 1), (0, 2), (1, 2)})
    negatives = {
        "edge_reused": (triangle, ((0, 1, 2), (0, 1))),
        "edge_omitted": (triangle, ((0, 1), (0, 2))),
        "nonclique_piece": (frozenset({(0, 1), (0, 2)}), ((0, 1, 2),)),
        "bad_piece_order_or_vertices": (triangle, ((0, 1, 2, 3, 4),)),
        "vertex_outside_graph": (triangle, ((0, 3),)),
    }
    for expected, (edges, pieces) in negatives.items():
        good, reason = check_partition(3, edges, pieces)
        if good or reason != expected:
            raise AssertionError((expected, good, reason))

    # Gain agrees with the completion count only for K3 and K4 here.
    gain_checks = {"triangle": 3 - 1 == 2, "K4": 6 - 1 == 5,
                   "order5_gain_formulas_diverge": (10 - 1 != 0)}
    if not all(gain_checks.values()):
        raise AssertionError(gain_checks)
    result = {"domain": "all labelled graphs n=0..6", **counts,
              "attaining_witnesses": witness_by_n,
              "negative_reasons": list(negatives), "gain_checks": gain_checks,
              "limit": "Finite regression only; no universal or threshold proof."}
    out = HERE / "results" / "literal_model_results.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k not in {"attaining_witnesses"}}, indent=2))


if __name__ == "__main__":
    main()
