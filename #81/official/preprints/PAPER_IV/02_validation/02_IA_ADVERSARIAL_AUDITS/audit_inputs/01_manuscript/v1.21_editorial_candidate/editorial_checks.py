"""Lightweight semantic evidence; never builds Lean or changes manuscript text."""
from pathlib import Path
import hashlib,json,re,sys,difflib
from collections import Counter
from fractions import Fraction as F
from finish_editorial import NOTATION
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'v1.2_full_rebuild_candidate'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def presentation(s):
    for a,b in NOTATION.items(): s=s.replace(a,b)
    # Explicit whitelist: notation, monospacing, agreement, and a translated heading.
    return s.replace('`','').replace('**Teorema 6.1 (estabilidad integral).** Existe ', '**Teorema 6.1 (estabilidad integral).** Existen ').replace('gap mixto nulo', 'brecha mixta nula')
def elements(t):
    return {
      'displays':re.findall(r'\\\[(.*?)\\\]',t,re.S),
      'labels':re.findall(r'\\tag\{([^}]+)\}',t),
      'code':re.findall(r'```[^\n]*\n(.*?)```',t,re.S),
      'statement_headings':[line for line in t.splitlines() if re.match(r'(?:\*\*|#{2,4} )(?:Theorem|Lemma|Proposition|Corollary|Teorema|Lema|Proposición|Corolario)\b',line)]
    }
rows={}
for lang in ('en','es'):
    b=BASE/f'PAPER_IV_preprint_v1.2_{lang}.md'
    t=b.read_text(encoding='utf-8-sig')
    rows[lang]={'path':str(b),'sha256':sha(b),'protected':elements(t)}
if sys.argv[1]=='baseline':
    p=HERE/'PROTECTED_BASELINE.json'
    assert not p.exists()
    p.write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
else:
    locked=json.loads((HERE/'PROTECTED_BASELINE.json').read_text(encoding='utf-8'))
    result={}; added={}
    for lang,r in rows.items():
        assert r==locked[lang], 'Frozen baseline changed'
        p=HERE/f'PAPER_IV_preprint_v1.21_{lang}.md'
        now=p.read_text(encoding='utf-8-sig'); new=elements(now); old=r['protected']
        # Added expository equations are allowed; existing displays must remain in order.
        it=iter(map(presentation,new['displays']))
        unchanged=all(any(presentation(x)==y for y in it) for x in old['displays'])
        added[lang]=Counter(map(presentation,new['displays']))-Counter(map(presentation,old['displays']))
        result[lang]={'baseline_sha256':r['sha256'],'candidate_sha256':sha(p),
          'old_display_sequence_preserved':unchanged,'display_count_before':len(old['displays']),
          'display_count_after':len(new['displays']),'labels_unchanged':new['labels']==old['labels'],
          'lean_code_blocks_unchanged':new['code']==old['code'],
          'statement_headings_unchanged':list(map(presentation,new['statement_headings']))==list(map(presentation,old['statement_headings'])),
          'presentation_normalization':{'subscript_renaming':NOTATION,'other':'Backticks; Existe -> Existen in Theorem 6.1 ES; gap mixto nulo -> brecha mixta nula in Proposition D.3 ES. No change to literal Lean.'},
          'qualification':'Mechanical checks complement, not replace, semantic review of added prose.'}
        diff=''.join(difflib.unified_diff(Path(r['path']).read_text(encoding='utf-8-sig').splitlines(True),now.splitlines(True),fromfile='v1.2_'+lang,tofile='v1.21_'+lang))
        (HERE/f'CHANGES_{lang}.diff').write_text(diff,encoding='utf-8')
    (HERE/'SEMANTIC_CHECKS.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
    scalars={
      'joint_elimination_error':F(1,10)+F(4,10**4)+F(4,10**10)+F(4,10**50)<=F(1,9),
      'normalized_missing_mass':F(1,10**41)+F(4,200*10**27)+F(4,40*10**27)+F(16,10**54)<=F(1,10**26),
      'triangle_cleanup_coefficient':F(33,2208)*F(1,10)**9<=F(1,8),
      'four_clique_cleanup_coefficient':F(138,2208)<=F(1,8),
      'regularization_degree':F(129,64)-F(1,4)==F(113,64),
      'old_exterior_degree':F(7,4)<=F(113,64),
      'core_size_window':F(2,10**31)+F(4,10**27)<=F(1,10**20),
      'light_missing_threshold':F(1,10**4)+F(2,10**41)<F(1,200)
      ,'schedule_log_upper':66*F(693147181,10**9)<=46
      ,'schedule_exponential':8*5153+1<=59480*F(6931471803,10**10)
      ,'retained_scale':F(12,7)*(5153+F(1,8))<=12748*F(6931471803,10**10)
      ,'gate_ceiling':2*10**17*392<=2**67
      ,'chain_offset':3*59485+220+12749==191424
    }
    supplemental={'added_display_parity':added['en']==added['es'],
      'added_displays_per_language':{k:sum(v.values()) for k,v in added.items()},
      'exact_rational_coefficient_checks':scalars,
      'limits':'Checks scalar comparisons only. They do not prove the graph lemmas, validate the entire schedule, or replace bilingual/editorial review.'}
    (HERE/'EXPOSITORY_CHECKS.json').write_text(json.dumps(supplemental,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(supplemental,indent=2))
    fields=('old_display_sequence_preserved','labels_unchanged','lean_code_blocks_unchanged','statement_headings_unchanged')
    assert all(r[f] for r in result.values() for f in fields)
    assert supplemental['added_display_parity'] and all(scalars.values())
