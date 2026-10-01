"""Read-only manuscript/PDF/Lean checks; writes only a new r2 evidence file."""
from pathlib import Path
import hashlib, json, re, sys
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'v1.22_editorial_candidate'
PAPER=ROOT.parents[1]
sys.path.insert(0,'C:/Users/jtraverso/.cache/e81-editorial-tools/python-libs')
import fitz
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
es=ROOT/'PAPER_IV_preprint_v1.22_es.md'
text=es.read_text(encoding='utf-8')
body,refs=text.split('## Referencias',1)
assert not re.search(r'\b(?:matchings?|packing)\b',body)
assert 'ganancia acotada de `Model`.' in body
assert refs==(BASE/es.name).read_text(encoding='utf-8').split('## Referencias',1)[1]
checks=json.loads((ROOT/'SEMANTIC_CHECKS.json').read_text(encoding='utf-8'))
assert sha(es)==checks['spanish_output_sha256']
for e in checks['english']:
    assert sha(ROOT/e['file'])==sha(BASE/e['file'])==e['sha256']
for directory in ('figures','figures_en','typeset_runtime'):
    for p in (BASE/directory).rglob('*'):
        if p.is_file(): assert sha(p)==sha(ROOT/p.relative_to(BASE))
for name in ('series_template.tex','typeset_helpers.py','build_draft.py'):
    assert sha(ROOT/name)==sha(BASE/name)
pdf=ROOT/'PAPER_IV_preprint_v1.22_es.pdf'
tex=ROOT/'PAPER_IV_preprint_v1.22_es.tex'
log=(ROOT/'PAPER_IV_preprint_v1.22_es.log').read_text(encoding='utf-8',errors='replace')
assert not re.search(r'Overfull|Missing character|Undefined control sequence|LaTeX Error|undefined references',log)
assert pdf.stat().st_mtime>=tex.stat().st_mtime
assert 'PAPER_IV_preprint_v1.22_es.pdf' in (ROOT/'compiler_console.log').read_text()
assert (ROOT/'qa_es/pdf_sha256.txt').read_text().strip()==sha(pdf)
changed=[]
with fitz.open(BASE/pdf.name) as old, fitz.open(pdf) as new:
    assert len(old)==len(new)==73
    for i in range(len(new)):
        if old[i].get_pixmap().samples != new[i].get_pixmap().samples: changed.append(i+1)
    alltext='\n'.join(p.get_text() for p in new)
    assert all(alltext.count(c)>=text.count(c) for c in '⦃⦄')
    assert not any(f[2]=='Type3' for p in new for f in p.get_fonts())
    # Residual bibliography and source titles are deliberately not translated.
    assert not re.search(r'\b(?:matchings?|packing)\b', '\n'.join(new[i].get_text() for i in range(71)))
manifest=PAPER/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
entries=json.loads(manifest.read_text(encoding='utf-8-sig'))
cut=PAPER/'05_formalization/lean_piv-v12-fb459343d234'
assert len(entries)==615 and all(sha(cut/e['path'])==e['sha256'] for e in entries)
out={'english_byte_identical':checks['english'], 'spanish_pdf_sha256':sha(pdf),
     'spanish_tex_sha256':sha(tex),'spanish_pages':73,'raster_changed_pages':changed,
     'unchanged_figures_templates':True,'protected_body_check':'SEMANTIC_CHECKS.json',
     'pdf_compiled_from_final_tex':True,'render_bound_to_pdf':True,'bad_log_entries':[],
     'source_manifest_sha256':sha(manifest),'source_entries_unchanged':615,
     'lean_executed':False,'pending':'External r2 revalidation'}
(ROOT/'ARTIFACT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
