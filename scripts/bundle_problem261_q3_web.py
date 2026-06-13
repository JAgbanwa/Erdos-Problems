#!/usr/bin/env python3
"""Bundle Problem 261 Q3 into a Mathlib-only file for online Lean compilers."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

IMPORTS = """\
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-!
Self-contained Erdős Problem 261 Q3 for online Lean compilers (e.g. lean4web MathlibDemo).

Paste this entire file into the editor. It imports only Mathlib, not `ErdosProblems`.
-/
"""


def namespace_body(text: str) -> str:
    start = text.index("namespace ErdosProblem261\n") + len("namespace ErdosProblem261\n")
    end = text.rindex("end ErdosProblem261")
    return text[start:end].strip()


def q1_prelude(text: str) -> str:
    body = namespace_body(text)
    body = body.split("theorem familyRepresentation")[0].strip()
    if body.endswith("-/"):
        body = body.rsplit("/--", 1)[0].strip()
    return body


basic = namespace_body((ROOT / "ErdosProblems/Problem261/Basic.lean").read_text())
basic = basic.removeprefix("open scoped BigOperators\n")
telescoping = namespace_body((ROOT / "ErdosProblems/Problem261/Telescoping.lean").read_text())
q1 = q1_prelude((ROOT / "ErdosProblems/Problem261/Q1.lean").read_text())
q3 = namespace_body((ROOT / "ErdosProblems/Problem261/Q3.lean").read_text())
q3 = q3.replace(
    "  · exact (familyRepresentation s hs).2.2",
    "  · exact familySum_eq s hs",
)

out = ROOT / "lean4web/Problem261_Q3.lean"
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(
    IMPORTS
    + "\nnamespace ErdosProblem261\n\nopen scoped BigOperators\nopen Cardinal\n\n"
    + basic
    + "\n\n"
    + telescoping
    + "\n\n"
    + q1
    + "\n\n"
    + q3.replace("open scoped BigOperators\n", "").replace("open Cardinal\n", "")
    + "\n\nend ErdosProblem261\n"
)
print(f"Wrote {out}")
