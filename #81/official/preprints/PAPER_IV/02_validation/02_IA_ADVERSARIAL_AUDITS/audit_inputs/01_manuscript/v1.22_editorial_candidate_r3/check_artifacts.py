"""Check both final bilingual chains and the unchanged frozen formal cut."""
from pathlib import Path
import hashlib,json,re,sys
ROOT=Path(__file__).resolve().parent; BASE=ROOT.parent/'v1.22_editorial_candidate_r2'; PAPER=ROOT.parents[1]
sys.path.insert(0,'C:/Users/jtraverso/.cache/e81-editorial-tools/python-libs')
import fitz
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
out={}
delta=json.loads((ROOT/'STATUS_DELTA.json').read_text(encoding='utf-8'))
for lang in ('es','en'):
    stem=f'PAPER_IV_preprint_v1.22_{lang}'
    md=(ROOT/(stem+'.md')).read_text(encoding='utf-8'); old=(BASE/(stem+'.md')).read_text(encoding='utf-8')
    assert sha(ROOT/(stem+'.md'))==delta[lang]['sha256']
    a=old.splitlines(); b=md.splitlines()
    assert len(a)==len(b)
    assert [i+1 for i,(x,y) in enumerate(zip(a,b)) if x!=y]==[p['line'] for p in delta[lang]['changed_paragraphs']]
    for pat in (r'\\\[.*?\\\]',r'\\\(.*?\\\)',r'```.*?```',r'\\tag\{[^}]+\}',r'^\|.*$',r'^!\[.*$'):
        assert re.findall(pat,md,re.S if not pat.startswith('^') else re.M)==re.findall(pat,old,re.S if not pat.startswith('^') else re.M)
    pdf=ROOT/(stem+'.pdf'); tex=ROOT/(stem+'.tex')
    log=(ROOT/(stem+'.log')).read_text(encoding='utf-8',errors='replace')
    assert not re.search(r'Overfull|Missing character|Undefined control sequence|LaTeX Error|undefined references',log)
    assert pdf.stat().st_mtime>=tex.stat().st_mtime
    assert (ROOT/f'qa_{lang}/pdf_sha256.txt').read_text().strip()==sha(pdf)
    assert tex.read_text(encoding='utf-8').split('\\maketitle')[0]==(BASE/(stem+'.tex')).read_text(encoding='utf-8').split('\\maketitle')[0]
    with fitz.open(pdf) as new,fitz.open(BASE/pdf.name) as prev:
        assert len(new)==len(prev)
        changed=[i+1 for i in range(len(new)) if new[i].get_pixmap().samples!=prev[i].get_pixmap().samples]
        assert not any(f[2]=='Type3' for p in new for f in p.get_fonts())
        out[lang]={'pages':len(new),'changed_pages':changed,'unchanged_pages':len(new)-len(changed),'pdf_sha256':sha(pdf),'tex_sha256':sha(tex),'md_sha256':sha(ROOT/(stem+'.md'))}
for d in ('figures','figures_en','typeset_runtime'):
    for p in (BASE/d).rglob('*'):
        if p.is_file(): assert sha(p)==sha(ROOT/p.relative_to(BASE))
manifest=PAPER/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
entries=json.loads(manifest.read_text(encoding='utf-8-sig'))
assert sha(manifest)=='fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5'
assert len(entries)==615 and all(sha(PAPER/'05_formalization/lean_piv-v12-fb459343d234'/e['path'])==e['sha256'] for e in entries)
out.update({'protected_mathematics_identical':True,'frozen_entries_unchanged':615,'lean_executed':False,'visual_review':'recorded separately after this check'})
(ROOT/'ARTIFACT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
