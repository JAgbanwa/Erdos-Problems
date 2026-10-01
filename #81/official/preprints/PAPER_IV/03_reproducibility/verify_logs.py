"""Run the audited supplemental verifier after publication-path relocation."""
from pathlib import Path
import hashlib,importlib.util,json,sys
PAPER=Path(__file__).resolve().parents[1]
BASE=PAPER/'02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/01_manuscript/v1.22_editorial_candidate_r4'
script=BASE/'verify_frozen_logs.py'; inventory=BASE/'LOG_INVENTORY.json'
assert hashlib.sha256(script.read_bytes()).hexdigest()=='c55225f35bd60ed624816ab74dd609a83ff5de7480cb2ff32b160b7d45850606'
assert hashlib.sha256(inventory.read_bytes()).hexdigest()=='938dcdcc23c024a53a6167192af9b913f3c625db6091e419c045e06cbec1829a'
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('audited_log_verifier',script)
module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
# Only the package root changes; the audited scanning function is unmodified.
module.PAPER=PAPER
result=module.verify(json.loads(inventory.read_text(encoding='utf-8')))
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['status']=='PASS' else 1)
