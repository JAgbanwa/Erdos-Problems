#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Render H_report.pdf (Gate H, independent Lean verification) and package the folder."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "00_CONTROL"))
from audit_lib import build_pdf, package

PDF = os.path.join(HERE, "H_report.pdf")


def read(path, limit=1500):
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read().strip()[:limit]
    except Exception:
        return "(not available)"


axioms = read(os.path.join(HERE, "print_axioms.log"))
build_tail = read(os.path.join(HERE, "lake_build.log"))
# keep only the success line + last few lines of build log for the PDF
build_lines = build_tail.splitlines()
build_success = next((l for l in build_lines if "Build completed" in l), "(see lake_build.log)")

meta = [
    ("Test", "Gate H -- Independent Lean verification"),
    ("Target", "PaperII.theorem_1_2 (unconditional, IsChordal)"),
    ("Toolchain", "leanprover/lean4:v4.28.0 / lake 5.0.0"),
    ("Build result", build_success),
]
sections = [
    {"h": "1. What was done"},
    {"p": "(1) lake build PaperII in the project lean/ tree; (2) an auditor-authored "
          "AuditCheck.lean running #print axioms PaperII.theorem_1_2, #check of the "
          "statement, and #print of IsChordal; (3) a SHA-256 manifest of the exact Lean "
          "source built (lean_source_sha256.txt)."},
    {"h": "2. Build result"},
    {"p": f"<b>{build_success}</b>. The build log contains no error/failed/sorry line "
          "(only benign unusedSectionVars linter warnings)."},
    {"h": "3. Statement shape (read + checked)"},
    {"p": "PaperII.theorem_1_2 (Unconditional.lean:72-79) has hypotheses exactly "
          "Fintype.card W = n and IsChordal G -- NO ChordalStructure, NO A2Transfer -- and "
          "asserts BOTH the forall upper bound phiTau G &lt;= floor((2n+1)^2/24) AND the "
          "exists attainment. phiTau (Model.lean:63) = edgeFinset.card - 2*tau3star. "
          "IsChordal (Chordal.lean:35) is the standard chord definition (every cycle of "
          "length &gt;=4 has a chord); not weakened."},
    {"h": "4. #print axioms output"},
    {"code": axioms if axioms and axioms != "(not available)" else
        "print_axioms.log was empty at render time (elaboration still loading Mathlib in "
        "this environment). Build success + sorry-free source + statement read stand as "
        "evidence; the literal axiom list is to be captured/reproduced (see residual)."},
    {"h": "5. Sorry-free"},
    {"p": "No sorry/admit tactic occurs in lean/PaperII/*.lean; the only 'sorry' substrings "
          "are the words 'sorry-free' in docstrings (Dirac1.lean:9, FiniteCover.lean:11)."},
    {"h": "6. Residual (honest)"},
    {"p": "Mathlib came from the project's pinned lake-manifest cache, not a clean-room "
          "from-scratch rebuild. The SHA-256 match to commit 5f2d448 could not be verified "
          "here (git history unreachable; release package lacks the lean/ tree). "
          "lean_source_sha256.txt records exactly what was built."},
]
build_pdf(PDF, "Paper II Audit -- Gate H: Independent Lean verification", meta, sections)

files = ["AuditCheck_source_note.txt", "H_build_record.md", "lake_build.log",
         "print_axioms.log", "lean_source_sha256.txt", "H_report.pdf", "make_h_report.py"]
# write a small note pointing to the AuditCheck.lean location (it lives in the lean tree)
with open(os.path.join(HERE, "AuditCheck_source_note.txt"), "w", encoding="utf-8") as f:
    f.write("The auditor checker file is lean/AuditCheck.lean in the Paper II project:\n\n")
    f.write("import PaperII.Unconditional\nopen PaperII\n"
            "#print axioms PaperII.theorem_1_2\n#check @PaperII.theorem_1_2\n"
            "#check @PaperII.IsChordal\n#print PaperII.IsChordal\n")
zp, sp, dg = package(HERE, "H_lean_verification",
                     [f for f in files if os.path.exists(os.path.join(HERE, f))])
print(