"""Quote frozen declarations with source and original external log provenance.
Static extraction only; this is not elaboration or a replacement for E1 review.
"""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent; PAPER=ROOT.parents[1]
CUT=PAPER/'05_formalization/lean_piv-v12-fb459343d234'
LOGS=PAPER/'02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/10_LOGS/E4_main/modules'
requests={
'PaperIV/NearH1LocalConstructor.lean':['exists_near_partition_paid_by_root_sharp','exists_near_partition_paid_by_root'],
'PaperIV/NearCriticalDichotomy.lean':['chordal_far_or_criticalRoot','chordal_far_or_edge_density'],
'PaperIV/HybridDichotomy.lean':['chordal_far_or_nearStructure'],
'PaperIV/SharpConstantOptimality.lean':['erdos81_quadratic_constant_optimal','erdos81_quadratic_constant_isLeast'],
'PaperIV/LinearCoefficient.lean':['linear_coefficient_optimal'],
'PaperIV/RootPartitionStability.lean':['sum_rootPieceDefect_eq'],
'PaperIV/SplitMixedGap.lean':['mixed_gap_zero'],
'PaperIV/SplitCompleteSharpValue.lean':['exists_sharp_cliquePartition_allParities'],
'FarExploration/CleanupRigidVerdict.lean':['threshold_gt_exp','threshold_gt_exp_seventy_two']}
rows=[]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for rel,names in requests.items():
    p=CUT/rel; text=p.read_text(encoding='utf-8'); module=rel[:-5].replace('/','.')
    log=LOGS/(module+'.log'); assert log.exists(),module
    for name in names:
        hit=re.search(r'(?m)^theorem '+re.escape(name)+r'\b',text); assert hit,name
        proof=re.search(r':=\s*(?:by\b|⟨)',text[hit.start():]); assert proof,name
        end=hit.start()+proof.start()
        rows.append({'name':module+'.'+name,'source':rel,'source_sha256':sha(p),
            'line':text.count('\n',0,hit.start())+1,'header':text[hit.start():end].rstrip(),
            'external_compilation_log':str(log.relative_to(PAPER)),'log_sha256':sha(log)})
(ROOT/'SEMANTIC_HEADERS.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
text='# Frozen headers for the supplemental E1 review\n\nStatic extraction; namespace and inherited variables must be read in the linked source. No new Lean execution.\n\n'
for r in rows: text+=f"## {r['name']}\n\nSource `{r['source']}:{r['line']}`; SHA-256 `{r['source_sha256']}`.\n\n```lean\n{r['header']}\n```\n\n"
(ROOT/'SEMANTIC_HEADERS.md').write_text(text,encoding='utf-8')
print('Extracted',len(rows),'headers with frozen source and external log hashes.')
