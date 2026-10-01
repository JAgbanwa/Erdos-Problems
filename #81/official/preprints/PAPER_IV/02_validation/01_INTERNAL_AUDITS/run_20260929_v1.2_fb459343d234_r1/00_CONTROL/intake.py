"""Read and bind frozen inputs; never modify author sources/manuscripts."""
from pathlib import Path
import hashlib
import json
import zipfile
from datetime import datetime, timezone

RUN = Path(__file__).resolve().parents[1]
PAPER = RUN.parents[2]
CONTROL = RUN / "00_CONTROL"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")


def main():
    target_path = PAPER / "02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.2.json"
    target = json.loads(target_path.read_text(encoding="utf-8"))
    failures, checks = [], []

    def check(label, ok):
        checks.append(dict(check=label, passed=bool(ok)))
        if not ok:
            failures.append(label)

    def bound_records(obj):
        if isinstance(obj, dict):
            if "path" in obj and "sha256" in obj:
                yield obj
            else:
                for val in obj.values():
                    yield from bound_records(val)
        elif isinstance(obj, list):
            for val in obj:
                yield from bound_records(val)

    for row in bound_records(target):
        path = (PAPER / row["path"]).resolve()
        check("binding:"+row["path"], path.is_relative_to(PAPER.resolve()) and
              path.is_file() and sha(path)==row["sha256"] and
              ("bytes" not in row or path.stat().st_size==row["bytes"]))

    source = PAPER / "05_formalization/lean_piv-v12-fb459343d234"
    manuscript = PAPER / target["intended_manuscript_directory"]
    evidence = PAPER / "03_reproducibility"
    jobs = [
        (PAPER / "03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json", source,
         PAPER / "05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip"),
        (manuscript / "MANUSCRIPT_MANIFEST.json", manuscript,
         PAPER / target["required_final_bindings"]["manuscript_archive"]["path"]),
        (evidence / "full_rebuild_v12_20260929_seal/EVIDENCE_MANIFEST.json", evidence,
         evidence / "full_rebuild_v12_20260929_seal/FULL_REBUILD_EVIDENCE_v1.2.zip")]
    inventory = []
    for manifest_path, base, archive in jobs:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        rows = manifest if isinstance(manifest, list) else manifest["files"]
        with zipfile.ZipFile(archive) as bundle:
            members = [name for name in bundle.namelist() if not name.endswith("/")]
            check("zip_unique:"+archive.name, len(members)==len(set(members)))
            check("zip_crc:"+archive.name, bundle.testzip() is None)
            for row in rows:
                rel = row["path"]
                path = (base / rel).resolve()
                check("manifest_file:"+str(base.relative_to(PAPER))+"/"+rel,
                      path.is_relative_to(base.resolve()) and path.is_file() and sha(path)==row["sha256"])
                matches = [m for m in members if m==rel]
                check("zip_member:"+archive.name+":"+rel, len(matches)==1)
                if len(matches)==1:
                    check("zip_hash:"+archive.name+":"+rel,
                          hashlib.sha256(bundle.read(matches[0])).hexdigest()==row["sha256"])
            check("no_sensitive_members:"+archive.name, not any(
                part in {".env", ".git", "__pycache__", ".lake"}
                or part.startswith(".env.") for m in members for part in Path(m).parts))
        inventory.append(dict(manifest=str(manifest_path), manifest_sha256=sha(manifest_path),
                              entries=len(rows), archive=str(archive), archive_sha256=sha(archive)))

    now = datetime.now(timezone.utc).isoformat()
    new_target = dict(run_id=RUN.name, version="1.2", audit_class="INTERNAL_AUTHOR_SIDE",
                      source_cut=target["source_cut"], manuscript_freeze=target["manuscript_freeze"],
                      created_at_utc=now, freezeSourceRoot=str(source), manuscriptRoot=str(manuscript),
                      publicationRoot=str(PAPER), external_target_sha256=sha(target_path),
                      expected=target["expected_main_scope"], inventories=inventory,
                      source_target=target, authorization="User goal: complete internal audit and fix problems; no publication.")
    target_out = CONTROL / "TARGET.json"
    if not target_out.exists():
        write(target_out,new_target)
    else:
        old = json.loads(target_out.read_text(encoding="utf-8"))
        check("target_not_changed",old["source_target"]==target)
    out = RUN / "20_EVIDENCE/G0_INTEGRITY/RESULTS.json"
    if out.exists():
        history = out.parent / "attempts"
        history.mkdir(exist_ok=True)
        previous = history / f"attempt_{len(list(history.glob('attempt_*.json')))+1:03}.json"
        previous.write_bytes(out.read_bytes())
    write(out,
          dict(status="PASS_INPUT_INTEGRITY" if not failures else "FAIL", checked_at_utc=now,
               checks=checks, failures=failures, inventories=inventory,
               scope="Files, archives, declared bindings only; no semantic or Lean proof claim."))
    if not (CONTROL / "AUDIT_STATE.json").exists():
        write(CONTROL / "AUDIT_STATE.json",dict(status="RUNNING",updated_at_utc=now,
              gates={"G0":"INPUT_INTEGRITY_PASS" if not failures else "FAIL",
                     **{f"G{i}":"NOT_STARTED" for i in range(1,9)}},
              blocks={f"B{i:02}":"NOT_STARTED" for i in range(1,11)},
              pending="G1/G3/G4 then finite blocks, prose review, bilingual/visual QA, reports/packages"))
    if not (CONTROL / "FINDINGS.json").exists():
        write(CONTROL / "FINDINGS.json",[]) 
    state = json.loads((CONTROL / "AUDIT_STATE.json").read_text(encoding="utf-8"))
    state["gates"]["G0"] = "INPUT_INTEGRITY_PASS" if not failures else "FAIL"
    state["updated_at_utc"] = now
    write(CONTROL / "AUDIT_STATE.json",state)
    print(json.dumps(dict(status="PASS_INPUT_INTEGRITY" if not failures else "FAIL",
                         checks=len(checks),failures=failures,run=str(RUN)),indent=2))
    return bool(failures)


if __name__=="__main__":
    raise SystemExit(main())
