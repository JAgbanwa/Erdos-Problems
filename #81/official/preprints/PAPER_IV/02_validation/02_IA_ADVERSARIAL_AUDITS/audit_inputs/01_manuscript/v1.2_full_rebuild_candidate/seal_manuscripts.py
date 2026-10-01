"""Seal the explicitly selected manuscript artifacts; no build, cache copy or publication."""
from pathlib import Path
import hashlib
import json
import re
import zipfile
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
PAPER = ROOT.parent.parent
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def encode(obj):
    return (json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode()

report = json.loads((ROOT / "ARTIFACT_CHECKS.json").read_text(encoding="utf-8"))
assert report["status"] == "PASS_ARTIFACT_CHECKS"
names = {
    "README.md", "BILINGUAL_FREEZE_REPORT.md", "NEXT_INTERNAL_AUDIT_SCOPE_v1.2.md",
    "ARTIFACT_CHECKS.json", "BILINGUAL_CHECKS.json", "BILINGUAL_APPROVED_EN.diff",
    "V1.2_CLAIM_MAP.md", "build_draft.py", "build_draft_en.py",
    "series_template.tex", "series_template_en.tex", "typeset_helpers.py",
    "check_release_artifacts.py", "check_bilingual.py", "prepare_bilingual.py",
    "assemble_bilingual.py", "seal_manuscripts.py", "VISUAL_QA_RECORD.json",
    "make_stability_figure.py", "make_stability_figure_es.py",
    "compiler_console.log", "compiler_console_en.log",
    "FULL_REBUILD_RESEAL_EN.diff", "FULL_REBUILD_RESEAL_ES.diff",
    "review_history/before-full-rebuild-reseal/PAPER_IV_preprint_v1.2_en.md",
    "review_history/before-full-rebuild-reseal/PAPER_IV_preprint_v1.2_es.md",
    "review_history/before-bilingual-20260929/PAPER_IV_preprint_v1.2_en.md",
}
for lang in ("en", "es"):
    stem = f"PAPER_IV_preprint_v1.2_{lang}"
    names.update(stem + ext for ext in (".md", ".tex", ".pdf", ".log"))
    for ext in ("md", "tex", "pdf"):
        assert sha(ROOT / (stem + "." + ext)) == report["artifacts"][lang][ext + "_sha256"]
    md = (ROOT / (stem + ".md")).read_text(encoding="utf-8")
    for asset in re.findall(r"!\[.*?\]\(([^)]+)\)", md):
        for ext in (".png", ".pdf", ".svg"):
            p = Path(asset).with_suffix(ext)
            if (ROOT / p).is_file():
                names.add(p.as_posix())
    names.update(p.relative_to(ROOT).as_posix() for p in (ROOT / f"qa_{lang}").glob("contact_*.png"))
    names.add(f"qa_{lang}/pdf_sha256.txt")
    names.add(f"qa_{lang}/pdf_text.txt")
qa = json.loads((ROOT / "VISUAL_QA_RECORD.json").read_text(encoding="utf-8"))
for lang in ("en", "es"):
    assert qa[lang]["pdf_sha256"] == report["artifacts"][lang]["pdf_sha256"]
    assert qa[lang]["all_pages_inspected_on_contact_sheets"]
    names.update(f"qa_{lang}/page_{n:02d}.png" for n in qa[lang]["full_resolution_pages"])
names.update(p.relative_to(ROOT).as_posix() for p in (ROOT / "qa_reference").glob("page_*.png"))
assert all((ROOT / name).is_file() for name in names)
rows = [{"path": name, "sha256": sha(ROOT / name), "bytes": (ROOT / name).stat().st_size}
        for name in sorted(names)]
payload = encode({"version": "1.2", "source_freeze": report["source_freeze"], "files": rows})
manifest_hash = hashlib.sha256(payload).hexdigest()
identity = "piv-v12-manuscripts-" + manifest_hash[:12]
manifest = ROOT / "MANUSCRIPT_MANIFEST.json"
manifest.write_bytes(payload)
archives = ROOT.parent / "frozen_manuscripts"
archives.mkdir(exist_ok=True)
archive = archives / (identity + ".zip")
assert not archive.exists(), "Do not overwrite a historical manuscript archive."
with zipfile.ZipFile(archive, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as z:
    z.write(manifest, manifest.name)
    for row in rows:
        z.write(ROOT / row["path"], row["path"])
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    assert set(z.namelist()) == {r["path"] for r in rows} | {manifest.name}
    assert z.read(manifest.name) == payload
    for row in rows:
        assert hashlib.sha256(z.read(row["path"])).hexdigest() == row["sha256"]
record = {
    "freeze_id": identity, "created_at_utc": datetime.now(timezone.utc).isoformat(),
    "status": "LOCAL_BILINGUAL_MANUSCRIPT_FREEZE",
    "version": "1.2", "source_freeze": report["source_freeze"],
    "source_freeze_record": "../../04_integrity/FREEZE_piv-v12-fb459343d234.json",
    "source_manifest_sha256": "fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5",
    "source_archive_sha256": "cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6",
    "author_full_build_evidence_seal": "../../03_reproducibility/full_rebuild_v12_20260929_seal/EVIDENCE_SEAL.json",
    "author_full_build_evidence_seal_sha256": report["full_reconstruction_seal_sha256"],
    "manifest_sha256": manifest_hash, "manifest_files": len(rows),
    "archive": str(archive), "archive_sha256": sha(archive),
    "zip_members": len(rows) + 1, "zip_members_and_hashes_verified": True,
    "manuscripts": report["artifacts"], "internal_audit": "PENDING_NEW_EXECUTION",
    "external_audit": "PENDING_NEW_EXECUTION", "publication": "NOT_PUBLISHED",
}
(ROOT / "MANUSCRIPT_FREEZE.json").write_bytes(encode(record))
integrity = PAPER / "04_integrity" / ("FREEZE_" + identity + ".json")
assert not integrity.exists()
integrity.write_bytes(encode(record))
archive.with_suffix(".zip.sha256").write_text(sha(archive) + "  " + archive.name + "\n", encoding="utf-8")
print(json.dumps(record, ensure_ascii=False, indent=2))
