from __future__ import annotations

import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPT = ROOT / "01_manuscript"
STEM = "PAPER_III_preprint_draft_v1.4"

FILES = {
    "md_en": MANUSCRIPT / f"{STEM}.md",
    "tex_en": MANUSCRIPT / f"{STEM}_en.tex",
    "pdf_en": MANUSCRIPT / f"{STEM}_en.pdf",
    "md_es": MANUSCRIPT / f"{STEM}_es.md",
    "tex_es": MANUSCRIPT / f"{STEM}_es.tex",
    "pdf_es": MANUSCRIPT / f"{STEM}_es.pdf",
}

REQUIRED_TOKENS = (
    "PaperIII.Theorem_1_1_Final",
    "PaperIII.AX1_holds",
    "PaperIII.AX2_holds",
    "PaperIII.CanonicalTrianglePacking",
    "PaperIII.CanonicalTrianglePackingGate",
    "PAPER_III_lean_v1.4_freeze.zip",
    "79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104",
    "8f9d9cff6bd728b17a24e163c9402775d9e6a365",
    "8455",
    "8444",
    "PASS_CLEAN_ORIGIN_RESUMED",
)


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def pdf_text(path: Path) -> str:
    proc = subprocess.run(
        ["pdftotext", "-layout", str(path), "-"],
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    return proc.stdout


def headings_md(text: str) -> list[str]:
    return re.findall(r"(?m)^#{1,6}\s+(.+?)\s*$", text)


def heading_depths_md(text: str) -> list[int]:
    return [len(m.group(1)) for m in re.finditer(r"(?m)^(#{1,6})\s+.+?\s*$", text)]


def section_block_counts(text: str) -> list[int]:
    headings = list(re.finditer(r"(?m)^#{1,6}\s+.+?\s*$", text))
    counts: list[int] = []
    for index, heading in enumerate(headings):
        end = headings[index + 1].start() if index + 1 < len(headings) else len(text)
        body = text[heading.end():end]
        counts.append(len([block for block in re.split(r"\n\s*\n", body) if block.strip()]))
    return counts


def display_math(text: str) -> list[str]:
    return re.findall(r"\\\[(.*?)\\\]", text, flags=re.DOTALL)


def normalized_math(block: str, language: str) -> str:
    block = re.sub(
        r"\\text\{\s*([^{}]*?)\s*\}",
        lambda match: r"\text{" + re.sub(r"\s+", " ", match.group(1)).strip() + "}",
        block,
    )
    replacements = {
        r"\text{par}": r"\text{even}",
        r"\text{impar}": r"\text{odd}",
        r"\text{para todo}": r"\text{for all}",
        r"\text{es impar}": r"\text{is odd}",
        r"\text{cordal}": r"\text{chordal}",
    }
    if language == "es":
        for source, target in replacements.items():
            block = block.replace(source, target)
    return re.sub(r"\s+", "", block)


def equation_tags(text: str) -> list[str]:
    return re.findall(r"\\tag\{([^}]+)\}", text)


def citations(text: str) -> list[str]:
    return re.findall(r"\[(?:\d+(?:,\d+)*)\]", text)


def lean_identifiers(text: str) -> set[str]:
    return set(re.findall(r"`([A-Za-z][A-Za-z0-9_.]*(?:\.[A-Za-z0-9_]+)+)`", text))


def duplicate_paragraphs(text: str) -> list[tuple[str, int]]:
    blocks = []
    for raw in re.split(r"\n\s*\n", text):
        block = re.sub(r"\s+", " ", raw.strip())
        if len(block) >= 180 and not block.startswith(("|", "```", "$$")):
            blocks.append(block)
    return [(block, count) for block, count in Counter(blocks).items() if count > 1]


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def protected_form(text: str) -> str:
    """Normalize format-level escaping and line wrapping, not semantic content."""
    text = re.sub(r"(?<=\d)[,.](?=\d{3}\b)", "", text)
    text = text.replace("\\allowbreak", "")
    return re.sub(r"\s+", "", text.replace("\\_", "_").replace("{", "").replace("}", ""))


def main() -> int:
    texts = {key: read(path) for key, path in FILES.items() if key.startswith(("md", "tex"))}
    texts["pdf_en"] = pdf_text(FILES["pdf_en"])
    texts["pdf_es"] = pdf_text(FILES["pdf_es"])

    checks: list[dict[str, object]] = []

    for key, path in FILES.items():
        checks.append({"check": f"exists:{key}", "pass": path.is_file(), "detail": str(path)})

    for lang in ("en", "es"):
        md = texts[f"md_{lang}"]
        tex = texts[f"tex_{lang}"]
        pdf = texts[f"pdf_{lang}"]
        for token in REQUIRED_TOKENS:
            normalized_token = protected_form(token)
            checks.append(
                {
                    "check": f"protected-token:{lang}:{token}",
                    "pass": all(normalized_token in protected_form(value) for value in (md, tex, pdf)),
                    "detail": "present in Markdown, TeX, and extracted PDF text",
                }
            )
        dups = duplicate_paragraphs(md)
        checks.append(
            {
                "check": f"duplicate-long-paragraphs:{lang}",
                "pass": not dups,
                "detail": f"{len(dups)} duplicated normalized paragraphs of at least 180 characters",
            }
        )

    en_headings = headings_md(texts["md_en"])
    es_headings = headings_md(texts["md_es"])
    checks.extend(
        [
            {
                "check": "heading-count-en-es",
                "pass": len(en_headings) == len(es_headings),
                "detail": f"EN={len(en_headings)} ES={len(es_headings)}",
            },
            {
                "check": "heading-depth-sequence-en-es",
                "pass": heading_depths_md(texts["md_en"]) == heading_depths_md(texts["md_es"]),
                "detail": "heading hierarchy is aligned",
            },
            {
                "check": "section-block-counts-en-es",
                "pass": section_block_counts(texts["md_en"]) == section_block_counts(texts["md_es"]),
                "detail": "every aligned heading contains the same number of Markdown blocks",
            },
            {
                "check": "equation-tags-en-es",
                "pass": equation_tags(texts["md_en"]) == equation_tags(texts["md_es"]),
                "detail": f"EN={len(equation_tags(texts['md_en']))} ES={len(equation_tags(texts['md_es']))}",
            },
            {
                "check": "display-math-sequence-en-es",
                "pass": [normalized_math(x, "en") for x in display_math(texts["md_en"])]
                == [normalized_math(x, "es") for x in display_math(texts["md_es"])],
                "detail": f"EN={len(display_math(texts['md_en']))} ES={len(display_math(texts['md_es']))}",
            },
            {
                "check": "citation-sequence-en-es",
                "pass": citations(texts["md_en"]) == citations(texts["md_es"]),
                "detail": f"EN={len(citations(texts['md_en']))} ES={len(citations(texts['md_es']))}",
            },
            {
                "check": "lean-identifier-set-en-es",
                "pass": lean_identifiers(texts["md_en"]) == lean_identifiers(texts["md_es"]),
                "detail": f"EN={len(lean_identifiers(texts['md_en']))} ES={len(lean_identifiers(texts['md_es']))}",
            },
        ]
    )

    for lang in ("en", "es"):
        md = texts[f"md_{lang}"]
        tex = texts[f"tex_{lang}"]
        md_figure_count = md.count("![")
        tex_figure_count = tex.count("\\includegraphics")
        checks.extend(
            [
                {
                    "check": f"figure-count:{lang}",
                    "pass": md_figure_count == 2 and tex_figure_count == 2,
                    "detail": f"Markdown={md_figure_count} TeX={tex_figure_count}",
                },
                {
                    "check": f"no-draft-version-cross-reference:{lang}",
                    "pass": not re.search(r"v1\.[0-3]\b|v2\.[0-9]+\b", md),
                    "detail": "manuscript is self-contained and does not refer readers to prior manuscript versions",
                },
            ]
        )

    bilingual_sentinels = {
        "en": (
            "h_i\\ge\\max\\{\\rho,\\,q_J-r_b\\}",
            "The same identity holds for \\(q=0\\)",
            "no standalone polynomial-time theorem is claimed here",
            "has \\(15\\) edges",
            "Other type-specialized theorem forms remain in `PaperIII.PublicAPI`",
        ),
        "es": (
            "h_i\\ge\\max\\{\\rho,\\,q_J-r_b\\}",
            "La misma identidad vale para \\(q=0\\)",
            "no se afirma un teorema polinomial autónomo",
            "tiene \\(15\\) aristas",
            "Otras formas del teorema especializadas por tipos permanecen en `PaperIII.PublicAPI`",
        ),
    }
    for lang, sentinels in bilingual_sentinels.items():
        md = texts[f"md_{lang}"]
        for sentinel in sentinels:
            checks.append(
                {
                    "check": f"translation-loss-sentinel:{lang}:{sentinel[:32]}",
                    "pass": sentinel in md,
                    "detail": "protected or previously omitted content is present",
                }
            )

    summary = {
        "verdict": "PASS" if all(bool(c["pass"]) for c in checks) else "FAIL",
        "checks": len(checks),
        "failed": [c for c in checks if not bool(c["pass"])],
        "heading_counts": {"en": len(en_headings), "es": len(es_headings)},
        "files": {key: {"sha256": sha256(path), "bytes": path.stat().st_size} for key, path in FILES.items()},
    }
    output = ROOT / "03_reproducibility" / "MANUSCRIPT_CONSISTENCY_RESULTS.json"
    output.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0 if summary["verdict"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
