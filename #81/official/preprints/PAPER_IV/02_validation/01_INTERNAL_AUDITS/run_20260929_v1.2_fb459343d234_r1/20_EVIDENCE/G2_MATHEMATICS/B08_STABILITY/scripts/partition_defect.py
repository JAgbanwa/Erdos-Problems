"""Finite checks of the unrestricted root-defect ledger (6.7a,b)."""

from __future__ import annotations

import json
from itertools import combinations
from math import comb
from pathlib import Path


HERE = Path(__file__).resolve().parents[1]


def pieces_for(n, edges, large=None):
    occupied = set(combinations(large, 2)) if large else set()
    return ([large] if large else []) + [e for e in edges if e not in occupied]


def defect(piece, root):
    a = len(set(piece) & root)
    b = len(piece) - a
    return 1 + comb(a, 2) + 3 * comb(b, 2) - a * b


def main():
    checks = 0
    noncanonical = 0
    for n in range(2, 6):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = {e for i, e in enumerate(possible) if mask & (1 << i)}
            for r in range(n + 1):
                for root_tuple in combinations(range(n), r):
                    root = set(root_tuple)
                    if not set(combinations(root_tuple, 2)) <= edges:
                        continue
                    outside = set(range(n)) - root
                    m = sum(u in outside and v in outside for u, v in edges)
                    missing = sum((min(u, v), max(u, v)) not in edges
                                  for u in root for v in outside)
                    baseline = r * (n - r) - comb(r, 2)
                    variants = [pieces_for(n, edges)]
                    for size in range(3, n + 1):
                        for piece in combinations(range(n), size):
                            if set(combinations(piece, 2)) <= edges:
                                variants.append(pieces_for(n, edges, piece))
                    for parts in variants:
                        total = sum(defect(piece, root) for piece in parts)
                        rhs = len(parts) - baseline + missing + 3 * m
                        if total != rhs:
                            raise AssertionError((n, mask, root_tuple, parts, total, rhs))
                        for piece in parts:
                            a = len(set(piece) & root)
                            b = len(piece) - a
                            canonical = (a, b) in {(1, 1), (2, 1)}
                            if (defect(piece, root) == 0) != canonical:
                                raise AssertionError((piece, root_tuple, "zero defect"))
                            if not canonical:
                                noncanonical += 1
                        checks += 1
    result = {"domain": "all labelled graphs n=2..5, all clique roots, edge-only and one-large-piece partitions",
              "ledger_checks": checks, "noncanonical_piece_checks": noncanonical,
              "failures": 0,
              "limit": "The identity is checked finitely; integral stability is certified by the Lean theorem, not this census."}
    path = HERE / "results" / "partition_defect.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
