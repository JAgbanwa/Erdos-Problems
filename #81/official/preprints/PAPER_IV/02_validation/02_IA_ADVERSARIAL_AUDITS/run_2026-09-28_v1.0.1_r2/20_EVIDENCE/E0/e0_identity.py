"""E0 independent identity check (auditor-written; does not import the author's verifier).

Recomputes SHA-256 of every bound input, ZIP CRC, per-member hashes, path traversal,
duplicate names, symlink bits, encrypted flags, comments, extra fields, and bytes
outside the central-directory-declared ranges (hidden payloads).
Usage: python e0_identity.py <label>   (label = intake | final)
"""
import hashlib, json, struct, sys, zipfile
from pathlib import Path, PurePosixPath

P = Path('C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV')
OUT = Path(__file__).resolve().parent
label = sys.argv[1] if len(sys.argv) > 1 else 'intake'

# Hashes quoted literally in EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.0.1.md section 2
REQUEST_TABLE = {
    '05_formalization/LEAN_SOURCE_SNAPSHOT_v1.0.zip': '0a13c01cc4cf0198d5d138082d45b25df4c5ac0684c0ed85e7cc758575f8a7dd',
    '05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip': '2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d',
    '01_manuscript/v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_en.md': '71417794fef91b2f4a6ad88b9da5734b72b8237fa8c0ec2aa0a00baab588208e',
    '01_manuscript/v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_en.tex': '0b4b116d5644c81837cf4abc8e409857a0747a60fc317adbd07ecfeafe205236',
    '01_manuscript/v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_en.pdf': '0c17c7303419b2c1979133479370bbb475d1febe3f0921737eb50c291caa8d10',
    '01_manuscript/v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_es.md': '8448d14eaf6b3e42cc969ce1d4b66eca309b92cee9d2547da8b354e6dd31d208',
    '01_manuscript/v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_es.tex': '1b4c8be49b54e3663acc4cb080018b0a16f257a464453684ba73b083fa1e5cb3',
    '01_manuscript/v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_es.pdf': '84c49df8964dbe19dc3f07833fb771e31989443199bf1e4af5d9e48f9d4f5ca2',
    '02_validation/01_INTERNAL_AUDITS/run_20260927_v1.0_f1769273dd2c/30_PACKAGE/INTERNAL_AUDIT_piv-v1.0-f1769273dd2c.zip': '1911f29e1072accfe8df4fbec0a3b02d1cd9ef274a06bd1957f9b61034301847',
}


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def zip_audit(path):
    raw = path.read_bytes()
    rep = {'members': [], 'problems': []}
    with zipfile.ZipFile(path) as z:
        bad = z.testzip()
        rep['testzip_first_bad'] = bad
        names = z.namelist()
        rep['member_count'] = len(names)
        rep['duplicate_names'] = sorted({n for n in names if names.count(n) > 1})
        rep['archive_comment_len'] = len(z.comment)
        covered = []
        for zi in z.infolist():
            n = zi.filename
            pp = PurePosixPath(n.replace('\\', '/'))
            if n.startswith('/') or '..' in pp.parts or (len(n) > 1 and n[1] == ':') or '\\' in n:
                rep['problems'].append('traversal_or_abs:' + n)
            if (zi.external_attr >> 16) & 0o170000 == 0o120000:
                rep['problems'].append('symlink:' + n)
            if zi.flag_bits & 1:
                rep['problems'].append('encrypted:' + n)
            if zi.comment:
                rep['problems'].append('member_comment:' + n)
            # local header size
            off = zi.header_offset
            sig, = struct.unpack('<I', raw[off:off + 4])
            if sig != 0x04034b50:
                rep['problems'].append('bad_local_sig:' + n)
            fnl, exl = struct.unpack('<HH', raw[off + 26:off + 30])
            end = off + 30 + fnl + exl + zi.compress_size
            if zi.flag_bits & 8:
                # data descriptor (12 or 16 bytes, optional sig)
                end += 16 if raw[end:end + 4] == b'PK\x07\x08' else 12
            covered.append((off, end))
            data = z.read(n) if not n.endswith('/') else b''
            rep['members'].append({'name': n, 'size': zi.file_size, 'crc': '%08x' % zi.CRC,
                                   'sha256': hashlib.sha256(data).hexdigest(),
                                   'extra_len': len(zi.extra), 'date_time': list(zi.date_time)})
        # central directory start
        eocd = raw.rfind(b'PK\x05\x06')
        cd_size, cd_off = struct.unpack('<II', raw[eocd + 12:eocd + 20])
        covered.sort()
        gaps = []
        pos = 0
        for s, e in covered:
            if s > pos:
                gaps.append((pos, s))
            pos = max(pos, e)
        if cd_off > pos:
            gaps.append((pos, cd_off))
        tail = len(raw) - (eocd + 22 + len(z.comment))
        rep['unaccounted_gaps'] = gaps
        rep['trailing_bytes_after_eocd'] = tail
        if gaps or tail:
            rep['problems'].append('hidden_bytes')
    return rep


def main():
    target = json.loads((P / '02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.0.1.json').read_text(encoding='utf-8'))
    res = {'label': label, 'files': [], 'request_table_check': [], 'zips': {}}
    for row in target['files']:
        p = P / row['path']
        h = sha(p) if p.is_file() else None
        res['files'].append({'path': row['path'], 'expected': row['sha256'], 'actual': h,
                             'bytes_expected': row['bytes'], 'bytes_actual': p.stat().st_size if p.is_file() else None,
                             'match': h == row['sha256'] and p.stat().st_size == row['bytes']})
    for rel, exp in REQUEST_TABLE.items():
        h = sha(P / rel)
        tj = next((r['sha256'] for r in target['files'] if r['path'] == rel), None)
        res['request_table_check'].append({'path': rel, 'request_md': exp, 'target_json': tj, 'actual': h,
                                           'match': h == exp == tj})
    for rel in ['05_formalization/LEAN_SOURCE_SNAPSHOT_v1.0.zip', '05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip',
                '02_validation/01_INTERNAL_AUDITS/run_20260927_v1.0_f1769273dd2c/30_PACKAGE/INTERNAL_AUDIT_piv-v1.0-f1769273dd2c.zip',
                '04_integrity/MANUSCRIPT_CANDIDATE_v1.0.1.zip']:
        res['zips'][rel] = zip_audit(P / rel)
    # candidate manifest
    man = json.loads((P / '01_manuscript/v1.0.1_candidate/MANIFEST.json').read_text(encoding='utf-8'))
    mm = []
    for row in man['files']:
        p = P / '01_manuscript/v1.0.1_candidate' / row['path']
        mm.append({'path': row['path'], 'ok': p.is_file() and sha(p) == row['sha256']})
    res['candidate_manifest'] = {'count': len(mm), 'mismatches': [m['path'] for m in mm if not m['ok']]}
    # files present in candidate dir but not in manifest
    cand = P / '01_manuscript/v1.0.1_candidate'
    listed = {r['path'].replace('\\', '/') for r in man['files']}
    present = {str(q.relative_to(cand)).replace('\\', '/') for q in cand.rglob('*') if q.is_file()}
    res['candidate_manifest']['unlisted_present'] = sorted(present - listed)
    res['candidate_manifest']['listed_missing'] = sorted(listed - present)
    summ = {
        'all_target_files_match': all(f['match'] for f in res['files']),
        'request_table_matches': all(r['match'] for r in res['request_table_check']),
        'zip_problems': {k: v['problems'][:20] + ([f"... {len(v['problems'])} total"] if len(v['problems']) > 20 else [])
                         for k, v in res['zips'].items()},
        'zip_testzip': {k: v['testzip_first_bad'] for k, v in res['zips'].items()},
        'zip_member_counts': {k: v['member_count'] for k, v in res['zips'].items()},
        'candidate_manifest': res['candidate_manifest'],
    }
    (OUT / f'E0_{label}_full.json').write_text(json.dumps(res, indent=1), encoding='utf-8')
    (OUT / f'E0_{label}_summary.json').write_text(json.dumps(summ, indent=1), encoding='utf-8')
    print(json.dumps(summ, indent=1))


if __name__ == '__main__':
    main()
