"""Read-only intake identity check. NOT a mathematical or external audit."""
import hashlib
import json
import sys
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def checked_path(base, relative):
    path = (base / relative).resolve()
    assert path.is_relative_to(base.resolve()), relative
    return path


def main():
    target = json.loads((HERE / 'AUDIT_TARGET_v1.0.1.json').read_text(encoding='utf-8'))
    errors = []
    checked = 0
    for row in target['files']:
        path = checked_path(ROOT, row['path'])
        if not path.is_file() or digest(path) != row['sha256'] or path.stat().st_size != row['bytes']:
            errors.append('Target mismatch: ' + row['path'])
        elif path.suffix == '.zip':
            with zipfile.ZipFile(path) as z:
                if z.testzip() is not None:
                    errors.append('ZIP CRC failed: ' + row['path'])
        checked += 1
    manifest_path = checked_path(ROOT, target['candidate_manifest'])
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    with zipfile.ZipFile(ROOT / '04_integrity/MANUSCRIPT_CANDIDATE_v1.0.1.zip') as bundle:
        for row in manifest['files']:
            path = checked_path(manifest_path.parent, row['path'])
            if not path.is_file() or digest(path) != row['sha256']:
                errors.append('Candidate mismatch: ' + row['path'])
            data = bundle.read('v1.0.1_candidate/' + row['path'])
            if hashlib.sha256(data).hexdigest() != row['sha256']:
                errors.append('Bundle mismatch: ' + row['path'])
            checked += 1
    print(json.dumps({'status': 'INTAKE_IDENTITY_OK' if not errors else 'INTAKE_FAILED',
                      'checked': checked, 'errors': errors,
                      'external_audit': 'NOT_PERFORMED_BY_THIS_CHECK',
                      'lean_build': 'NOT_RUN', 'dependencies': 'UNTOUCHED'}, indent=2))
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
