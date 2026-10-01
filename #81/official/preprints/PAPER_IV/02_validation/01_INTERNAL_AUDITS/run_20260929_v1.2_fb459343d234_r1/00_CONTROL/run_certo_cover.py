"""Conserva generación, replay y mutaciones del ejemplo literal K3 join I3."""

import json
import subprocess
import time
from pathlib import Path

RUN = Path(__file__).resolve().parents[1]
BLOCK = RUN / "20_EVIDENCE" / "G2_MATHEMATICS" / "B01_MODEL"
SPEC = BLOCK / "inputs" / "split_k3_h3_cover.py"
CERT = BLOCK / "certificates" / "split_k3_h3_cover_optimal.json"
OUT = BLOCK / "results"


def run(name, arguments):
    start = time.monotonic()
    process = subprocess.run(arguments, cwd=RUN, capture_output=True,
                             text=True, encoding="utf-8", errors="replace", timeout=60)
    (OUT / f"{name}.stdout.txt").write_text(process.stdout, encoding="utf-8")
    (OUT / f"{name}.stderr.txt").write_text(process.stderr, encoding="utf-8")
    return {"command": [str(x) for x in arguments], "exitCode": process.returncode,
            "elapsedSeconds": round(time.monotonic() - start, 3)}


def main():
    records = {
        "generation": run("certo_generation", ["certo", "cover", str(SPEC), "--optimize",
            "--prove-optimal", "--timeout-ms", "60000", "--max-memory-mb", "2048",
            "--cert", str(CERT), "--json", "--brief"]),
        "replay": run("certo_replay", ["certo", "verify", str(CERT),
            "--spec", str(SPEC), "--json", "--brief"]),
        "tamper": run("certo_tamper", ["certo", "verify", str(CERT),
            "--spec", str(SPEC), "--tamper", "--json", "--brief"]),
    }
    records["certificateKind"] = json.loads(CERT.read_text(encoding="utf-8"))["kind"]
    records["scope"] = "Exact-cover certificate proves this partition, not a stored lower-bound certificate. The independent core-edge charge gives the lower bound 6."
    (OUT / "certo_run.json").write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value["exitCode"] for key, value in records.items()
                      if isinstance(value, dict)}, indent=2))
    return 0 if all(record["exitCode"] == 0 for record in records.values() if isinstance(record, dict)) else 1


if __name__ == "__main__":
    raise SystemExit(main())
