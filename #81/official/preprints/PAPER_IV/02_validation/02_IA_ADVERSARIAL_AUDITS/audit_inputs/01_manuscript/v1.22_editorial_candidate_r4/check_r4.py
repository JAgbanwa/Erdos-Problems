"""Verify the exact two-phrase delta and unchanged English/formal artifacts."""
from pathlib import Path
import hashlib,json,re,sys
ROOT=Path(__file__).resolve().parent; BASE=ROOT.parent/'v1.22_editorial_candidate_r3'; PAPER=ROOT.parents[1]
sys.path.insert(0,'C:/Users/jtraverso/.cache/e81-editorial-tools/python-libs')
import fitz
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
changes=json.loads((ROOT/'TERMINOLOGY_DELTA.json').read_text(encoding='utf-8'))['changes']
es='PAPER_IV_preprint_v1.22_es'; en='PAPER_IV_preprint_v1.22_en'
for ext in ('md','tex'):
    old=(BASE/(es+'.'+ext)).read_text(encoding='utf-8'); expected=old
    for before,after in changes:
        assert expected.count(before)==1
        expected=expected.replace(before,after)
    actual=(ROOT/(es+'.'+ext)).read_text(encoding='utf-8')
    assert actual==expected,ext+' differs beyond the two replacements'
    if ext=='md':
        for pattern in (r'\\\[.*?\\\]',r'\\\(.*?\\\)',r'```.*?```',r'\\tag\{[^}]+\}'):
            assert re.findall(pattern,old,re.S)==re.findall(pattern,actual,re.S)
for ext in ('md','tex','pdf','log'): assert sha(ROOT/(en+'.'+ext))==sha(BASE/(en+'.'+ext))
for directory in ('figures','figures_en','typeset_runtime'):
    for p in (BASE/directory).rglob('*'):
        if p.is_file(): assert sha(ROOT/p.relative_to(BASE))==sha(p)
log=(ROOT/(es+'.log')).read_text(encoding='utf-8',errors='replace')
assert not re.search(r'Overfull|Missing character|Undefined control sequence|LaTeX Error|undefined references',log)
assert (ROOT/(es+'.pdf')).stat().st_mtime >= (ROOT/(es+'.tex')).stat().st_mtime
assert (ROOT/'qa_es/pdf_sha256.txt').read_text().strip()==sha(ROOT/(es+'.pdf'))
with fitz.open(ROOT/(es+'.pdf')) as doc, fitz.open(BASE/(es+'.pdf')) as prev:
    assert len(doc)==len(prev)==73
    changed=[i+1 for i in range(len(doc)) if doc[i].get_pixmap().samples!=prev[i].get_pixmap().samples]
    a=' '.join(' '.join(p.get_text() for p in prev).split())
    b=' '.join(' '.join(p.get_text() for p in doc).split())
    for before,after in changes: a=a.replace(before,after)
    # The shorter A.2 phrase changes three Spanish line-end hyphenations only.
    for wrapped,plain in [('conso- lidado','consolidado'),('declara- do','declarado'),('ve- rifica','verifica')]:
        a=a.replace(wrapped,plain); b=b.replace(wrapped,plain)
    assert a==b,'PDF text differs beyond the replacements and three documented hyphenations'
manifest=PAPER/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
assert sha(manifest)=='fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5'
entries=json.loads(manifest.read_text(encoding='utf-8-sig'))
assert len(entries)==615 and all(sha(PAPER/'05_formalization/lean_piv-v12-fb459343d234'/e['path'])==e['sha256'] for e in entries)
result={'revision':'v1.22-r4','exact_two_phrase_delta_md_tex_pdf':True,'protected_mathematics_identical':True,
 'english_byte_identical':True,'frozen_entries_unchanged':615,'spanish_pages':73,'english_pages':72,'changed_spanish_pages':changed,
 'files':{s+'.'+ext:sha(ROOT/(s+'.'+ext)) for s in (es,en) for ext in ('md','tex','pdf')},
 'pdf_linewrap_only':['conso- lidado','declara- do','ve- rifica'],
 'spanish_underfull_warnings':log.count('Underfull'),'lean_executed':False,'visual_review':'see VISUAL_AND_INTEGRITY_REVIEW.md'}
(ROOT/'ARTIFACT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
