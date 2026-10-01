"""Read-only artifact checks plus versioned QA outputs; never invokes Lean."""
from pathlib import Path
import sys,re,json,hashlib
from collections import Counter
ROOT=Path(__file__).resolve().parent
PAPER=ROOT.parents[1]
sys.path.insert(0,'C:/Users/jtraverso/.cache/e81-editorial-tools/python-libs')
import pymupdf as fitz
from finish_editorial import NOTATION
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
result={}
for lang in ('en','es'):
    stem=f'PAPER_IV_preprint_v1.21_{lang}'
    md=(ROOT/(stem+'.md')).read_text(encoding='utf-8')
    tex=(ROOT/(stem+'.tex')).read_text(encoding='utf-8')
    log=(ROOT/(stem+'.log')).read_text(encoding='utf-8',errors='replace')
    doc=fitz.open(ROOT/(stem+'.pdf'))
    txt='\n'.join(page.get_text() for page in doc)
    fonts={f[1:4] for page in doc for f in page.get_fonts()}
    result[lang]={
      'pages':len(doc),'hashes':{ext:sha(ROOT/(stem+'.'+ext)) for ext in ('md','tex','pdf')},
      'overfull_boxes':re.findall(r'Overfull[^\n]*',log),
      'missing_glyphs':re.findall(r'Missing character[^\n]*',log),
      'type3_fonts':[f for f in fonts if f[1]=='Type3'],
      'unicode_strict_binders_preserved':all(txt.count(c)>=md.count(c) for c in ('⦃','⦄')),
      'equation_tags_in_tex':all(tag in tex for tag in re.findall(r'\\tag\{([^}]+)\}',md)),
      'body_figure3_reference':('Figure 3 summarizes' if lang=='en' else 'La Figura 3 resume') in md,
      'literal_lean_pages':[i+1 for i,p in enumerate(doc) if 'def IsChordal' in p.get_text() or 'theorem erdos81' in p.get_text()],
      'new_exposition_pages':[i+1 for i,p in enumerate(doc) if any(t in p.get_text() for t in ('C.2.','C.3.','E.1.','191424','615 entradas','615 source'))],
    }
    # Exact inline formula parity checks the new numerical explanations as well.
    base=(ROOT.parent/'v1.2_full_rebuild_candidate'/f'PAPER_IV_preprint_v1.2_{lang}.md').read_text(encoding='utf-8-sig')
    for a,b in NOTATION.items():base=base.replace(a,b)
    norm=lambda x:x.replace(r'\text{ que sirve }',r'\text{ serving }')
    result[lang]['inline_math']=Counter(map(norm,re.findall(r'\\\((.*?)\\\)',md,re.S)))-Counter(map(norm,re.findall(r'\\\((.*?)\\\)',base,re.S)))
en_math=result['en'].pop('inline_math'); es_math=result['es'].pop('inline_math')
parity=en_math==es_math
build=PAPER/'03_reproducibility/full_rebuild_v12_20260929_resume/combined'
meta=json.loads((build/'RUN_META.json').read_text(encoding='utf-8-sig'))
rows=[]
for target in meta['targets']:
    p=build/'modules'/(target+'.log'); t=p.read_text(encoding='utf-8',errors='replace')
    rows.append({'target':target,'log_sha256':sha(p),
      'standard_prints':len(re.findall(r'depends on axioms:\s*\[',t)),
      'all_records':len(re.findall(r'(?:depends on axioms:|axioms)\s*\[',t))})
counts={'standard_prints':sum(x['standard_prints'] for x in rows),'all_records':sum(x['all_records'] for x in rows),'rows':rows}
counts['custom_lists']=counts['all_records']-counts['standard_prints']
(ROOT/'AXIOM_COUNT_RECONCILIATION.json').write_text(json.dumps(counts,indent=2)+'\n',encoding='utf-8')
out={'artifacts':result,'added_inline_math_multiset_parity':parity,'inline_math_differences':{'en_only':dict(en_math-es_math),'es_only':dict(es_math-en_math)},'scope':'Mechanical checks only; visual and mathematical review are distinct. Inline comparison concerns additions to each language baseline, after the declared notation renamings.'}
(ROOT/'ARTIFACT_CHECKS.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,ensure_ascii=False,indent=2))
print('Axiom records:',counts['all_records'],counts['standard_prints'],counts['custom_lists'])
assert parity
assert all(not r['overfull_boxes'] and not r['missing_glyphs'] and not r['type3_fonts'] and r['unicode_strict_binders_preserved'] and r['equation_tags_in_tex'] for r in result.values())
