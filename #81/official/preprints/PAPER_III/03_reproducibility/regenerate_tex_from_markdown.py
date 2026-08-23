from __future__ import annotations

import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPT = ROOT / "01_manuscript"
STEM = "PAPER_III_preprint_v1.5"
READER = "markdown+tex_math_single_backslash+tex_math_dollars"


def regenerate(language: str) -> None:
    md = MANUSCRIPT / (f"{STEM}.md" if language == "en" else f"{STEM}_es.md")
    tex = MANUSCRIPT / f"{STEM}_{language}.tex"
    existing = tex.read_text(encoding="utf-8")
    marker = "\\maketitle\n"
    if marker not in existing:
        raise RuntimeError(f"template boundary not found in {tex.name}")
    prefix = existing.split(marker, 1)[0] + marker + "\n"

    markdown = md.read_text(encoding="utf-8")
    lines = markdown.splitlines()
    if not lines or not lines[0].startswith("# "):
        raise RuntimeError(f"expected title heading in {md.name}")
    series_marker = (
        "**Paper III in the series**"
        if language == "en"
        else "**Paper III de la serie**"
    )
    try:
        body_start = next(
            index for index, line in enumerate(lines) if line.rstrip() == series_marker
        )
    except StopIteration as exc:
        raise RuntimeError(f"series metadata boundary not found in {md.name}") from exc
    # The Markdown author block remains visible on GitHub.  The LaTeX template
    # already renders the same data through \author and \maketitle, so body
    # conversion begins at the series metadata rather than duplicating it.
    body_source = "\n".join(lines[body_start:]) + "\n"
    proc = subprocess.run(
        ["pandoc", "--from", READER, "--to", "latex", "--wrap=none"],
        input=body_source,
        text=True,
        encoding="utf-8",
        capture_output=True,
        check=True,
    )
    body = proc.stdout.rstrip()
    # Preserve the identifier while permitting a zero-width line break in the
    # narrow formalization tables used by the series template.
    body = body.replace(
        "PaperIII.CanonicalTrianglePackingGate",
        "PaperIII.CanonicalTrianglePacking\\allowbreak{}Gate",
    )
    references_heading = "References" if language == "en" else "Referencias"
    reference_marker = f"\\subsection{{{references_heading}}}"
    if reference_marker not in body:
        raise RuntimeError(f"reference heading not found in generated {language} body")
    body = body.replace(
        reference_marker,
        "\\begingroup\n\\setlength{\\parskip}{2pt plus 1pt minus 1pt}\n" + reference_marker,
        1,
    )
    rendered = prefix + body + "\n\\endgroup\n\n\\end{document}\n"
    tex.write_text(rendered, encoding="utf-8", newline="\n")
    print(f"generated {tex.name}")


for lang in ("en", "es"):
    regenerate(lang)
