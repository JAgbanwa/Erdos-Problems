"""Finite exact-arithmetic regression of ConstructorBudget.cancel_budget.

This tests the numerical interface; it does not construct an AllInput graph.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import comb
from pathlib import Path
from random import Random


HERE = Path(__file__).resolve().parents[1]


def premise_and_conclusion(pieces, c, b, s, t, dg, mn, length, ec):
    physical = pieces + ec + 2 * mn <= c * b + dg + 2 * t * (length + t)
    budget = (Fraction(dg + 2 * t * (length + t) + comb(c, 2) + comb(s + 1, 2))
              <= Fraction(ec + 2 * mn + s * c) + Fraction(t * (c + b + s), 3))
    conclusion = (Fraction(pieces + comb(c, 2) + comb(s + 1, 2))
                  <= Fraction(c * (b + s)) + Fraction(t * (c + b + s), 3))
    return physical, budget, conclusion


def main():
    random = Random(8104)
    accepted = 0
    for _ in range(100000):
        args = [random.randrange(0, 15) for _ in range(9)]
        physical, budget, conclusion = premise_and_conclusion(*args)
        if physical and budget:
            accepted += 1
            if not conclusion:
                raise AssertionError(args)
    if accepted < 100:
        raise AssertionError((accepted, "too few satisfied antecedents"))

    # The premises are essential; a bare conclusion is not valid for all naturals.
    witness = None
    for pieces in range(1, 15):
        for c in range(1, 8):
            args = (pieces, c, 0, 0, 0, 0, 0, 0, 0)
            physical, budget, conclusion = premise_and_conclusion(*args)
            if not conclusion and not (physical and budget):
                witness = {"args": args, "physical": physical, "budget": budget,
                           "conclusion": conclusion}
                break
        if witness:
            break
    if witness is None:
        raise AssertionError("negative witness not found")
    result = {"seed": 8104, "draws": 100000,
              "satisfying_both_premises": accepted, "failures": 0,
              "negative_bare_conclusion": witness,
              "limit": "Finite rational arithmetic only; the Lean lemma proves the universal cancellation."}
    path = HERE / "results" / "cancel_budget_regression.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
