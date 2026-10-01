"""One-time, scope-limited notation normalization authorized for the O1–O5 review."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent
p = root / "PAPER_IV_preprint_v1.2_en.md"
text = p.read_text(encoding="utf-8")
start = text.index("### E.1. Constructor and accounting")
end = text.index("### E.2.", start)
section = text[start:end]
assert r"\(r=|W|\)" in section
section = re.sub(r"(?<![A-Za-z])r(?![A-Za-z])", "t_W", section)
section = re.sub(r"(?<![A-Za-z_])t(?![A-Za-z_])", "t_I", section)
section = section.replace("+rz", "+t_W z")
text = text[:start] + section + text[end:]
start = text.index("**Proof.** We first explain the retained estimate")
end = text.index("Substituting the middle bounds", start)
section = text[start:end]
section = section.replace(r"\(w=|W|\)", r"\(t_W=|W|\)")
section = section.replace("nw", "nt_W")
text = text[:start] + section + text[end:]
p.write_text(text, encoding="utf-8")
