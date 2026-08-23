# R6 -- report QA and sealing procedure

**Verdict:** `PASS`

The internal residual report was generated in Markdown, LaTeX, PDF and JSON.
The PDF was compiled twice from the delivered TeX with LuaLaTeX. The final log
records the expected two-page output, with no fatal error, missing glyph,
overfull box or undefined reference. Both final rendered pages were inspected
at 150 dpi; no clipping, collision, malformed table, blank region or missing
text was found. All fonts are embedded.

One diagnostic compilation used a literal `$dir` output directory outside the
target. Its output was rejected and moved to the recoverable agent-work area.
The report was then compiled twice from the verified report directory and
rendered anew. No compiler scratch remains in the target.

Gate manifests and the package manifest are generated after all gate records
and reports are final. The ZIP is then created and verified member-by-member;
its final summary and SHA-256 sidecar are written after verification.
