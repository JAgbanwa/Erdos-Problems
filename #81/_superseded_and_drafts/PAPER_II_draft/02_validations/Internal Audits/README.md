# Paper II — Internal Controls (computational validation evidence)

Erdős #81, Paper II: *Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs.*
Each folder audits one statement of the paper by exact computation. Every folder contains:
`control.py` (script), `results.txt` (verbatim output), `report.pdf`/`report.tex` (English certificate),
`SHA256SUMS.txt` (file integrity), and a self-contained `CTRL-0x*.zip`.

| Control | Statement | Verdict |
|---|---|---|
| CTRL-01 | Lemma 3.1 — vertex-copy inequality | PASS |
| CTRL-02 | Prop. 6.2 / Cor. 6.3 — complete-split cover value | PASS |
| CTRL-03 | Prop. 7.1 — exact integer maximization | PASS |
| CTRL-04 | Lemma 5.1 — terminal characterization | PASS |

These are finite-instance computational checks supporting the analytic proof; they are not a substitute
for it. Folder-level integrity is recorded in the master `SHA256SUMS.txt`.
