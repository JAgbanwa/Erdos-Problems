"""Read-only source/build trace; writes only this audit's derived evidence."""
from pathlib import Path
import ast, csv, hashlib, json, re, zipfile, sys, platform, importlib.metadata as im

RUN=Path(__file__).resolve().parents[1]
PAPER=RUN.parents[2]
SRC=PAPER/'05_formalization/lean_piv-v12-fb459343d234'
MS=PAPER/'01_manuscript/v1.2_full_rebuild_candidate'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,o):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

def annex():
    base=PAPER/'05_formalization/lean_v1.0_freeze'
    overlay=PAPER/'05_formalization/lean_v1.0_gap_annex'
    logs=PAPER/'03_reproducibility/build_gap_annex_20260927'
    rows=read(logs/'RESULTS.json');sources={r['module']:r for r in read(logs/'SOURCES.json')}
    checks=[]; ax=[]
    for r in rows:
        p=overlay/r['path']
        if not p.exists():p=base/r['path']
        log=logs/'modules'/f"{r['module']}.log"
        exitfile=log.with_suffix('.exit')
        t=log.read_text(encoding='utf-8-sig')
        lists=re.findall(r'(?:depends on axioms:|axioms)\s*\[([^\]]*)\]',t)
        ok=(r['status']=='PASS' and r['exitCode']==0 and not r['sorryWarning'] and
            sha(p)==r['sourceSha256']==sources[r['module']]['sha256'] and
            exitfile.read_text().strip()=='EXIT_CODE=0' and
            not re.search(r"sorryAx|declaration uses 'sorry'|^.*error(?:\(|:)",t,re.M) and
            all(set(v.strip() for v in a.split(',') if v.strip())<={'propext','Classical.choice','Quot.sound'} for a in lists))
        checks.append(dict(module=r['module'],passed=ok,source_sha256=sha(p),log_sha256=sha(log)))
        ax.extend(dict(module=r['module'],declaration=n,axioms=a) for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",t))
    assert len(checks)==579 and all(r['passed'] for r in checks)
    save(RUN/'20_EVIDENCE/G4_LEAN/ANNEX_RECHECK.json',dict(status='PASS_RECORDED_BUILD',modules=579,checks=checks,axioms=ax,scope='Historical bounded-clique triangular-gap annex, separate from the 607-module freeze. Not a new compilation.'))

def trace():
    inv=read(RUN/'20_EVIDENCE/G3_FORMAL/SOURCE_INVENTORY.json')
    exports=inv['exports']
    old=PAPER/'02_validation/01_INTERNAL_AUDITS/run_20260927_v1.0_f1769273dd2c/00_CONTROL/build_claim_map.py'
    public=next(ast.literal_eval(n.value) for n in ast.parse(old.read_text(encoding='utf-8')).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='PUBLIC' for t in n.targets))
    # Reuse labels only, not any historical verdict or mathematical evidence.
    for k,v in list(public.items()):
        if k.startswith('PaperIV.DefectSharpPublication.rooted_defect_'):
            public[k.replace('DefectSharpPublication','DefectExplicitPublication')]=v
    updates={
      'chordal_joint_stability_real':('Corollary 6.1a','B08','One clique before every unrestricted partition; real deficits; 16,48,480.'),
      'fixed_defect_joint_stability_real':('Theorem C prime / 6.12-6.13','B08','Fixed s; actual clique C; exactly s defect vertices; same template for all Q; real deficits.'),
      'fixed_defect_stability_explicit':('Theorem C prime / E.4 / F.1','B08','Explicit fixed-s constants and threshold, including minimum-degree and deletion steps.'),
      'fixed_defect_exact_extremal_edit_real':('Corollary 6.3','B08','Optimal-size template; square-root term; resized core need not be a clique of G.'),
      'shifted_template_witness':('Proposition 6.3a','B07','n+s=3q; q>=2s+2; 1<=d; 2d<=q; unrestricted lower witness.'),
      'shifted_template_sqrt_lower_bound':('Proposition 6.3a','B08','Universal optimal-template distance lower bound; exact shifted family.'),
      'certified_shifted_fractional_bound_all_orders':('Proposition 6.4','B02','All n, 0<=s<=n; certified mixed optimum; no n>=8 restriction.'),
      'certified_refined_fractional_bound_all_orders':('Proposition 6.4','B02','Stronger correction only for 4s<=n.'),
      'uniform_shifted_partition_bound':('Proposition 6.4 integral form','B03','Accuracy fixed before n,s,G; threshold uniform in s; epsilon n squared loss.'),
      'uniform_refined_partition_bound':('Proposition 6.4 integral form','B03','Same uniformity; 4s<=n.'),
      'sequence_arbitrary_orders_partition_bound':('Theorem 6.5','B06','Orders tend to infinity, defect/order tends to zero; positive upper excess tends to zero.'),
      'sequence_arbitrary_orders_stability':('Theorem 6.5','B08','Eventual fractional nearness; one root sequence controls all partitions; no substitution into fixed-s theorem.'),
      'theoremC_tower':('Corollary 6.6','B04','Exact eventual target beyond explicit tower.'),
      'theoremC_tower_uniform':('Corollary 6.6','B04','Uniform tower calibration in s.'),
      'theoremC_tower_uniform_sMax':('Corollary 6.6 inverse','B04','Requires n>=tower2(Ptower 0).'),
      'NfarE_le_tower_poly':('Appendix C.4','B04','Rational 0<eta<=1; coefficient 4, not legacy 104.'),
      'exists_clique_additive_defect':('Lemma F.3a','B09','Rooted defect on G; arbitrary finite subset; positive-part square; ordered nonedges.'),
      'l11_caseA':('Appendix F.5 case A','B09','Every coloring has at least eta n squared conflicts; samples with replacement.'),
      'l11_caseB1':('Appendix F.5 case B1','B09','A coloring with small conflicts but a bad section; extension of sampled sequences.'),
      'l11_caseB2':('Appendix F.5 case B2','B09','Small conflicts and no bad section; normalized ranks<=n; edit contradiction.'),
    }
    ax=read(RUN/'20_EVIDENCE/G4_LEAN/AXIOM_RECORDS.json')
    cones=read(RUN/'20_EVIDENCE/G4_LEAN/CONE_RECORDS.json')
    elab=(RUN/'20_EVIDENCE/G4_LEAN/EXPORT_TYPES.txt').read_text(encoding='utf-8')
    rows=[]
    for i,e in enumerate(exports,1):
        n=e['declaration'];short=n.split('.')[-1];c=e['source_candidates'][0]
        loc,es,b,scope=public.get(n,('Supporting interface / Appendix A','Interfaz auxiliar / Apéndice A','B09','Support interface, not a separately asserted theorem.'))
        if short in updates:loc,b,scope=updates[short];es=loc
        if short=='mixed_gap_zero':loc=es='Proposition D.3'
        if short=='targetSize_eq_baseline_add_reserve':loc=es='Appendix D.3'
        if short.startswith('threshold_gt_exp'):loc=es='Appendix G.2'
        a=[x['target'] for x in ax if x['declaration']==n]
        co=[x['target'] for x in cones if re.search(re.escape(n)+r'(?![\w.])',x['record'])]
        assert e['module_in_root'] and e['module_built'] and e['export_evidence'] and n in elab
        rows.append(dict(claim_id=f'C{i:03}',section_es=es,section_en=loc,
          statement_hash=hashlib.sha256(c['header'].encode()).hexdigest(),protected_hypotheses=c['header'],lean_declaration=n,module=c['module'],public_entry='PaperIV',export_evidence='G4_LEAN/EXPORT_TYPES.txt',build_evidence='G4_LEAN/MODULE_PROVENANCE.json',axiom_evidence=';'.join(a) or 'Transitive source-module cone; see G4 full log inventory',constant_cone_evidence=';'.join(co) or 'No separate named provenance claim; see module and transitive axioms',math_block=b,scope=scope,verdict='PASS_INTERNAL_SCOPE_REVIEW' if loc!='Supporting interface / Appendix A' else 'PASS_EXPORT_TRACE'))
    fields=list(rows[0]);out=RUN/'00_CONTROL/CLAIM_MAP.csv'
    with out.open('w',encoding='utf-8',newline='') as f:
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(rows)
    # All named manuscript headings are indexed even when proved in prose/composition.
    text=(MS/'PAPER_IV_preprint_v1.2_en.md').read_text(encoding='utf-8')
    headings=[]
    for line,t in enumerate(text.splitlines(),1):
        if re.match(r'^(?:#+\s*)?\*\*(?:Theorem|Lemma|Proposition|Corollary)\b',t):
            headings.append(dict(line=line,heading=t.split('**')[1],sha256=hashlib.sha256(t.encode()).hexdigest()))
    save(RUN/'20_EVIDENCE/G1_CLAIMS/TRACE_SUMMARY.json',dict(status='TRACE_BUILT',exports=len(rows),public_rows=sum(r['verdict']=='PASS_INTERNAL_SCOPE_REVIEW' for r in rows),headings=headings,limits='Statement hashes are source headers, which can include context comments. Elaborated types in EXPORT_TYPES.txt resolve all implicit hypotheses. Semantic decisions are in MATHEMATICAL_REVIEW.md.'))

if __name__=='__main__':
    annex();trace()
    versions={}
    for n in ('certo-math','certo','z3-solver','PuLP','scipy','PyMuPDF','Pillow'):
        try: versions[n]=im.version(n)
        except im.PackageNotFoundError:pass
    save(RUN/'00_CONTROL/ENVIRONMENT.json',dict(python=sys.version,platform=platform.platform(),packages=versions,lean='4.28.0',mathlib='8f9d9cff6bd728b17a24e163c9402775d9e6a365',policy='No Lean invocation, no dependency download, no subagents in this continuation; serial bounded checks. Existing build and cache reused read-only.'))
    print('PASS annex 579; current export trace generated.')
