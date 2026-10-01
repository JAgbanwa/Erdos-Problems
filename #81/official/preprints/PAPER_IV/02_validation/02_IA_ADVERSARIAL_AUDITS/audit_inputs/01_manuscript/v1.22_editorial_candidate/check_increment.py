"""Exact arithmetic, protected-text, artifact and freeze checks. Does not invoke Lean."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import difflib, hashlib, json, re, sys

ROOT=Path(__file__).resolve().parent
PAPER=ROOT.parents[1]
BASE=ROOT.parent/'v1.21_editorial_candidate'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,obj): (ROOT/name).write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def math(t,kind):
    return re.findall(r'\\\[.*?\\\]' if kind=='display' else r'\\\(.*?\\\)',t,re.S)
def norm(t):return t.replace(r'\text{ que sirve }',r'\text{ serving }')
texts={}; adds={}; checks={}
for lang in ('en','es'):
    old=(BASE/f'PAPER_IV_preprint_v1.21_{lang}.md').read_text(encoding='utf-8')
    p=ROOT/f'PAPER_IV_preprint_v1.22_{lang}.md'; new=p.read_text(encoding='utf-8'); texts[lang]=new
    olddis,newdis=Counter(math(old,'display')),Counter(math(new,'display'))
    assert not olddis-newdis, 'Protected display changed'
    assert re.findall(r'```lean\n.*?\n```',old,re.S)==re.findall(r'```lean\n.*?\n```',new,re.S)
    assert re.findall(r'\\tag\{([^}]+)\}',old)==re.findall(r'\\tag\{([^}]+)\}',new)
    pat=r'(?m)^\*\*(?:Theorem|Lemma|Proposition|Corollary|Teorema|Lema|Proposición|Corolario) [^\n]+'
    assert re.findall(pat,old)==re.findall(pat,new)
    changes=list(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='v1.21/'+lang,tofile='v1.22/'+lang))
    (ROOT/f'CHANGES_{lang}.diff').write_text(''.join(changes),encoding='utf-8')
    adds[lang]={kind:Counter(map(norm,math(new,kind)))-Counter(map(norm,math(old,kind))) for kind in ('display','inline')}
    checks[lang]={'baseline_sha256':sha(BASE/f'PAPER_IV_preprint_v1.21_{lang}.md'),'output_sha256':sha(p),
                  'old_displays_retained':sum(olddis.values()),'added_displays':sum((newdis-olddis).values()),
                  'tags_lean_blocks_result_paragraphs_unchanged':True}
assert adds['en']==adds['es'], {k:dict(adds['en'][k]-adds['es'][k]) for k in adds['en']}
assert 'recurrence in §6.3' not in texts['en'] and 'recurrencia de §6.3' not in texts['es']
assert 'Integer and fractional empaquetamientos' not in texts['es']
save('SEMANTIC_CHECKS.json',{'languages':checks,'added_mathematics_bilingual_parity':True,
     'scope':'Preserves every existing display, numbered label, Lean block and result paragraph. New formulas expand existing E18/E19 proofs; external semantic review remains required.'})

q=9*10**19; a=F(1,q); delta=a**21/2208; eps=delta/8; k0=3*10**19+1
h=4*8**5*2208**5*4500**105*(2*10**16)**105
a3=a**3-3*delta; a4=a**6-6*delta
tests={
 'initial_log_argument':100/eps**5 <= 4**4000,
 'initial_size':4001<=k0 and 7<=k0,
 'iteration_count_exact':4/eps**5==h,
 'h_at_least_two':h>=2,
 'gate_exponent_below_k0':59517<=k0,
 'alpha_le_2pow2000':2208*q**21<=2**2000,
 'beta_le_2pow2000':8*q**6<=2**2000,
 'k0_le_2pow2000':k0<=2**2000,
 'decimal_coefficient_le_2pow2000':10**18<=2**2000,
 'fourth_term_rational_bound':(a3+a4)/(a3*a4)<=2*q**6,
 'initial_tower_comparison':4*k0<=2**67 and 67<=65536,
 'absorption_coefficients':F(1,4)+F(7,256)<=1,
 'tower_auxiliary_base':8*6<=2**6,
 'tower_auxiliary_induction':all(8*(t+1)<=2*(8*t) for t in range(6,100)),
 'recurrence_sanity':all(2**t<=t*4**t and 4*(t*4**t)<=2**(4*t) for t in range(1,80)),
 'negative_false_absorption_rejected':not(F(1,4)+F(200,256)<=1),
 'negative_false_tower_base_rejected':not(8*5<=2**5),
 'negative_wrong_iteration_rejected':4/eps**5!=h+1,
}
assert all(tests.values()),tests
save('EXACT_CHECKS.json',{'checks':tests,'pass_count':len(tests),'scope':'Exact rational arithmetic plus finite regression/negative controls; universal inequalities are justified in the manuscript by the existing Lean proof, not by this testing.'})

manifest=PAPER/'03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json'
cut=PAPER/'05_formalization/lean_piv-v12-fb459343d234'
entries=json.loads(manifest.read_text(encoding='utf-8-sig'))
fail=[e['path'] for e in entries if sha(cut/e['path'])!=e['sha256']]
assert not fail,fail
save('LEAN_IDENTITY_CHECK.json',{'entries':len(entries),'manifest_sha256':sha(manifest),'changed':fail,'lean_executed':False})

if '--artifacts' in sys.argv:
    sys.path.insert(0,'C:/Users/jtraverso/.cache/e81-editorial-tools/python-libs')
    import fitz
    out={}
    for lang in ('en','es'):
        stem=f'PAPER_IV_preprint_v1.22_{lang}'
        pdf=ROOT/(stem+'.pdf'); tex=ROOT/(stem+'.tex'); log=ROOT/(stem+'.log')
        lt=log.read_text(encoding='utf-8',errors='replace')
        with fitz.open(pdf) as doc:
            txt='\n'.join(p.get_text() for p in doc)
            fonts={str(f[2]) for p in doc for f in p.get_fonts()}
            out[lang]={'pages':len(doc),'pdf_sha256':sha(pdf),'tex_sha256':sha(tex),
                'pdf_newer_than_tex':pdf.stat().st_mtime>=tex.stat().st_mtime,
                'bad_log_lines':re.findall(r'(?:Overfull|Missing character|Undefined control sequence|LaTeX Error)[^\n]*',lt),
                'expected_output_in_console':stem+'.pdf' in (ROOT/('compiler_console_en.log' if lang=='en' else 'compiler_console.log')).read_text(encoding='utf-8'),
                'type3': 'Type3' in fonts,'strict_binders':all(txt.count(c)>=texts[lang].count(c) for c in '⦃⦄'),
                'tower_pages':[i+1 for i,p in enumerate(doc) if any(s in p.get_text() for s in ['Converting the iterate','De la iteración','Absorbing the five','Absorción de los cinco','regularity bound.','cota explícita de regularidad.'])]}
            assert all([out[lang]['pdf_newer_than_tex'],out[lang]['expected_output_in_console'],not out[lang]['type3'],out[lang]['strict_binders'],not out[lang]['bad_log_lines']]),out[lang]
    save('ARTIFACT_CHECKS.json',out)
    print(json.dumps(out,indent=2))
print('PASS: protected texts, added-math parity, 18 arithmetic/negative checks, 615 source identities. No Lean executed.')
