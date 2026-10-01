"""Independent local checks of the recorded editorial delta; never runs Lean."""
from pathlib import Path
from collections import Counter
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit
import hashlib, json, re, subprocess
import pymupdf as fitz

P = Path(__file__).resolve().parents[2]
ROOT = P.parent.parent
E = P/'02_validation/03_EDITORIAL_CHECKS/v1.23'
BASE = P/'02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/published_v1.22'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return p.read_text(encoding='utf-8-sig')
def js(p): return json.loads(read(p))
def save(p, data): p.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def paragraphs(s): return re.split(r'\n\s*\n',s)

delta=js(E/'ADMINISTRATIVE_DELTA.json')
assert len(delta)==12
records=[]
for lang in ('en','es'):
    old=BASE/f'01_manuscript/PAPER_IV_preprint_v1.22_{lang}.md'
    new=P/f'01_manuscript/PAPER_IV_preprint_v1.23_{lang}.md'
    a,b=read(old),read(new)
    items=[x for x in delta if x['id'].startswith(lang+'-')]
    assert len(items)==6
    expected=a
    for d in items:
        assert expected.count(d['before'])==1
        expected=expected.replace(d['before'],d['after'],1)
    assert expected==b, 'Undeclared Markdown delta'
    patterns={'inline_math':r'\\\((.*?)\\\)', 'display_math':r'\\\[(.*?)\\\]',
              'fenced_blocks':r'```.*?\n(.*?)```', 'headings':r'^#{1,6} .*$',
              'images':r'!\[[^\]]*\]\([^)]*\)'}
    counts={}
    for key,pattern in patterns.items():
        flags=re.M if key=='headings' else re.S
        x,y=re.findall(pattern,a,flags),re.findall(pattern,b,flags)
        assert x==y,(lang,key)
        counts[key]=len(x)
    ref='## References' if lang=='en' else '## Referencias'
    assert a.split(ref)[-1]==b.split(ref)[-1]
    # Independent TeX check: every nonadministrative paragraph is byte-equivalent
    # modulo newline encoding. The only changed paragraphs are these six slots.
    ta=read(old.with_suffix('.tex')); tb=read(new.with_suffix('.tex'))
    pa,pb=paragraphs(ta),paragraphs(tb)
    assert len(pa)==len(pb)
    changed=[(x,y) for x,y in zip(pa,pb) if x!=y]
    assert len(changed)==6,(lang,len(changed))
    for x,y in changed:
        assert not any(marker in x+y for marker in (r'\[',r'\(',r'\begin{verbatim}',r'\begin{longtable}',r'\begin{equation}'))
    for marker in (re.escape(r'\label')+r'\{[^}]*\}',re.escape(r'\includegraphics')+r'(?:\[[^]]*\])?\{[^}]*\}',re.escape(r'\begin')+r'\{[^}]*\}'):
        assert re.findall(marker,ta)==re.findall(marker,tb)
    binding=next(x for x in js(E/'TYPESETTING.json') if x['language']==lang)
    assert binding['tex_sha256']==sha(new.with_suffix('.tex'))
    assert binding['pdf_sha256']==sha(new.with_suffix('.pdf'))
    doc=fitz.open(new.with_suffix('.pdf'))
    assert len(doc)==binding['pages']
    assert all(p.get_text().strip() for p in doc)
    records.append({'language':lang,'checks':counts,'changed_administrative_tex_paragraphs':6,
        'bibliography_unchanged':True,'pages':len(doc),
        'files':{ext:sha(new.with_suffix('.'+ext)) for ext in ('md','tex','pdf')}})

audits=P/'02_validation/02_IA_ADVERSARIAL_AUDITS'
summary=js(audits/'run_v1.22_r4/30_REPORT/SUMMARY.json')
for name,digest in summary['target']['six_sha256'].items():
    assert sha(BASE/'01_manuscript'/name)==digest
formal=js(P/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json')
assert len(formal)==615
assert all(sha(P/'05_formalization/lean_piv-v12-fb459343d234'/x['path'])==x['sha256'] for x in formal)
assert not subprocess.check_output(['git','diff','--name-only','--','preprints/PAPER_I','preprints/PAPER_II','preprints/PAPER_III','preprints/PAPER_IV/05_formalization'],cwd=ROOT).strip()

src=audits/'run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md'
dst=P/'02_validation/translations/v1.22_r4/FINAL_CONSOLIDATED_AUDIT_REPORT_en.md'
sa,sb=read(src),read(dst)
tokens=lambda s:Counter(re.findall(r'`([^`]+)`',s))
assert not (tokens(sa)-tokens(sb)),tokens(sa)-tokens(sb)
hashes=lambda s:Counter(re.findall(r'\b[a-f0-9]{64}\b',s))
assert hashes(sa)==hashes(sb)
assert len(re.findall(r'^## \d+\.',sa,re.M))==len(re.findall(r'^## \d+\.',sb,re.M))==11
save(dst.parent/'TRANSLATION_CHECKS.json',{'status':'PASS','source_sha256':sha(src),'translation_sha256':sha(dst),'numbered_sections':11,'all_original_literal_code_tokens_retained':True,'full_hashes_identical':True,'review':'Editorial translation checked against the original; no auditor-issued new verdict. Original counts and limitations preserved.'})

class Links(HTMLParser):
    def __init__(self): super().__init__(); self.links=[]
    def handle_starttag(self,tag,attrs):
        for k,v in attrs:
            if k in ('href','src'): self.links.append(v)
links_checked=0
for path in (ROOT/'index.html',P/'PaperIV_explained_4_levels.html'):
    parser=Links(); parser.feed(read(path))
    for link in parser.links:
        u=urlsplit(link)
        if u.scheme or u.netloc or not u.path: continue
        assert (path.parent/unquote(u.path)).is_file(),(path,link)
        links_checked+=1
save(E/'SEMANTIC_CHECKS.json',{'status':'PASS','scope':'Editorial identity checks, not a new mathematical or external audit','languages':records,'declared_administrative_changes':12,'frozen_source_entries_unchanged':615,'papers_I_II_III_unchanged':True,'html_local_links_checked':links_checked,'lean_executed':False})
print(json.dumps({'status':'PASS','languages':2,'formal_entries':615,'html_links':links_checked}))
