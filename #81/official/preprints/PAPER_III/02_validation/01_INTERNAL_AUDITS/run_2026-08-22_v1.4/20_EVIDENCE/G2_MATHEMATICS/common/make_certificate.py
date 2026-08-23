"""
Generate a one-page PDF audit certificate (English) for an INTERNAL_AUDIT block.

Usage:
    python make_certificate.py <block_dir> <block_id> <title> <results_file> <verdict> <sha_of_results>

Uses only reportlab (no external assets). Deterministic layout.
"""
import sys
import datetime
from reportlab.lib.pagesizes import LETTER
from reportlab.lib.units import inch
from reportlab.lib import colors
from reportlab.pdfgen import canvas
from reportlab.lib.utils import simpleSplit


def build(pdf_path, block_id, title, results_text, verdict, results_sha, summary_lines):
    c = canvas.Canvas(pdf_path, pagesize=LETTER)
    W, H = LETTER
    m = 0.9 * inch
    y = H - m

    c.setFont("Helvetica-Bold", 16)
    c.drawString(m, y, "Internal Audit Certificate")
    y -= 22
    c.setFont("Helvetica", 11)
    c.drawString(m, y, "Paper III — Linear-Error Clique Partitions of Split Graphs (Erdos #81)")
    y -= 16
    c.drawString(m, y, f"Audit block: {block_id}")
    y -= 26

    # verdict banner
    ok = verdict.upper().startswith("PASS")
    c.setFillColor(colors.HexColor("#1a7f37") if ok else colors.HexColor("#b3261e"))
    c.rect(m, y - 6, W - 2 * m, 26, fill=1, stroke=0)
    c.setFillColor(colors.white)
    c.setFont("Helvetica-Bold", 13)
    c.drawString(m + 8, y + 2, f"VERDICT: {verdict}")
    c.setFillColor(colors.black)
    y -= 40

    c.setFont("Helvetica-Bold", 11)
    c.drawString(m, y, "Scope")
    y -= 16
    c.setFont("Helvetica", 10)
    for line in simpleSplit(title, "Helvetica", 10, W - 2 * m):
        c.drawString(m, y, line); y -= 13
    y -= 8

    c.setFont("Helvetica-Bold", 11)
    c.drawString(m, y, "Summary of evidence")
    y -= 16
    c.setFont("Helvetica", 10)
    for line in summary_lines:
        for sub in simpleSplit(line, "Helvetica", 10, W - 2 * m):
            c.drawString(m, y, sub); y -= 13
    y -= 8

    c.setFont("Helvetica-Bold", 11)
    c.drawString(m, y, "Methodology")
    y -= 16
    c.setFont("Helvetica", 10)
    meth = ("All numeric checks use exact rational arithmetic (Python fractions) or exact "
            "linear/integer programming; symbolic identities are proved with SymPy "
            "(simplify(LHS-RHS)=0 or sum-of-squares certificate). The audit re-derives each "
            "claim independently of the manuscript's own scripts and of the Lean formalization.")
    for line in simpleSplit(meth, "Helvetica", 10, W - 2 * m):
        c.drawString(m, y, line); y -= 13
    y -= 8

    c.setFont("Helvetica-Bold", 11)
    c.drawString(m, y, "Reproducibility")
    y -= 16
    c.setFont("Helvetica", 9)
    c.drawString(m, y, f"Results file: results/{results_text}")
    y -= 12
    c.drawString(m, y, f"SHA-256 (results file): {results_sha}")
    y -= 12
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    c.drawString(m, y, f"Generated: {stamp}   |   Tooling: Python 3.14, SymPy 1.14, SciPy 1.17, PuLP/CBC")
    y -= 12
    c.drawString(m, y, "Auditor: internal automated audit harness (Claude Code)")
    y -= 24

    c.setFont("Helvetica-Oblique", 8)
    note = ("This certificate attests to computational/symbolic verification of the stated "
            "finite/closed-form claims at the audited parameter ranges. It complements, and is "
            "independent of, the machine-checked Lean 4 / Mathlib formalization.")
    for line in simpleSplit(note, "Helvetica-Oblique", 8, W - 2 * m):
        c.drawString(m, y, line); y -= 10

    c.showPage()
    c.save()


if __name__ == "__main__":
    import json
    cfg = json.loads(sys.argv[1])
    build(cfg["pdf"], cfg["block_id"], cfg["title"], cfg["results_name"],
          cfg["verdict"], cfg["results_sha"], cfg["summary"])
    print("wrote", cfg["pdf"])
