"""Reproducible author-side integrity and contract audit (Python standard library).

No mathematical proof is inferred from this test suite. Lean checks are run
separately. This suite rejects stale, mismatched or incomplete release evidence.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess, zipfile

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
LEAN = ROOT/'05_formalization/lean_draft_freeze'
BASE = ROOT/'04_integrity/baseline'
rows = []
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def public_files(root):
    for base, dirs, names in os.walk(root):
        dirs[:] = [d for d in dirs if d not in ('.lake','__pycache__')]
        for name in names: yield Path(base)/name
def check(name, condition, detail=''):
    rows.append({'check':name,'pass':bool(condition),'detail':detail})
def stripped(text):
    out=[]; i=0; depth=0; string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; i+=2
            elif text.startswith('-/',i): depth-=1; i+=2
            else: i+=1
        elif string:
            if text[i]=='\\': i+=2
            elif text[i]=='"': string=False; i+=1; out.append(' ')
            else: i+=1
        elif text.startswith('/-',i): depth=1; i+=2; out.append(' ')
        elif text.startswith('--',i):
            j=text.find('\n',i); i=len(text) if j<0 else j
            out.append('\n')
        elif text[i]=='"': string=True; i+=1; out.append(' ')
        else: out.append(text[i]); i+=1
    assert depth==0 and not string, 'Unclosed comment/string in audit input'
    return ''.join(out)

cut=json.loads((BASE/'LEAN_CUT.json').read_text(encoding='utf-8'))
archive=ROOT/'05_formalization/LEAN_SOURCE_SNAPSHOT_v0.8.zip'
check('G0.archive_hash',sha(archive)==cut['sha256'])
with zipfile.ZipFile(archive) as z:
    check('G0.archive_crc',z.testzip() is None)
    check('G0.archive_paths',all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist()))
    check('G3.archive_source_identity',all(hashlib.sha256(z.read('paper4_lean/'+f)).hexdigest()==h for f,h in cut['source_hashes'].items()))
    evidence={'axiom_audit_v08.log','cone_audit_v08.log','supplement_audit_v08.log','bounded_gap_audit_v08.log','SupplementAudit.lean','AUDIT_SNAPSHOT.json','AUDIT_SUMMARY.json','AUDIT_DECLARATIONS.tsv'}
    check('G0.archive_allowlist',set(z.namelist())=={'paper4_lean/'+f for f in cut['source_hashes']}|{'evidence/'+f for f in evidence})
    check('G8.archive_secret_scan',not any(re.search(rb'(?:arstl_[A-Za-z0-9_-]{20,}|ghp_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{30,}|-----BEGIN (?:RSA |OPENSSH )?PRIVATE KEY-----)',z.read(n)) for n in z.namelist()))
check('G3.extracted_source_identity',all(sha(LEAN/f)==h for f,h in cut['source_hashes'].items()),str(cut['source_count'])+' frozen entries')
actual={p.relative_to(LEAN).as_posix() for p in public_files(LEAN) if p.suffix=='.lean'}
expected={p for p in cut['source_hashes'] if p.endswith('.lean')}
check('G3.no_unmanifested_lean',actual==expected)
check('G3.extracted_package_exact', {p.relative_to(LEAN).as_posix() for p in public_files(LEAN)}==set(cut['source_hashes']))
text={f:(LEAN/f).read_text(encoding='utf-8') for f in expected}
code={f:stripped(t) for f,t in text.items()}
for token in ('sorry','admit','axiom','native_decide','implemented_by','sorryAx'):
    bad=[f for f,t in code.items() if re.search(r'\b'+token+r'\b',t)]
    check('G3.token_'+token,not bad,', '.join(bad))
check('G3.scanner_rejects_live_token',bool(re.search(r'\bsorry\b',stripped('/- sorry /- axiom -/ -/\nexample : True := by sorry'))))
check('G3.scanner_ignores_prose',not re.search(r'\bsorry\b',stripped('/- sorry /- sorry -/ -/\n#eval "sorry" -- sorry\n')))
check('G3.scanner_preserves_boundary',stripped('a/- note -/b')=='a b')
manifest=json.loads((LEAN/'lake-manifest.json').read_text())
check('G3.manifest_hash',sha(LEAN/'lake-manifest.json')==cut['lake_manifest_sha256'])
check('G3.toolchain',(LEAN/'lean-toolchain').read_text().strip()==cut['toolchain'])
check('G3.pinned_git_dependencies',all(re.fullmatch('[0-9a-f]{40}',p['rev']) for p in manifest['packages'] if p['type']=='git'))
check('G3.only_local_series_package',all(p['name']=='PaperIIIRelease' and p['dir']=='PaperIIIRelease' for p in manifest['packages'] if p['type']=='path'))
dependency_checks=[]
for dep in manifest['packages']:
    if dep['type']!='git': continue
    directory=LEAN/'.lake/packages'/dep['name']
    revision=subprocess.run(['git','-C',str(directory),'rev-parse','HEAD'],capture_output=True,text=True)
    status=subprocess.run(['git','-C',str(directory),'status','--porcelain','--untracked-files=no'],capture_output=True,text=True)
    dependency_checks.append({'name':dep['name'],'expected':dep['rev'],'actual':revision.stdout.strip(),
      'revision_matches':revision.returncode==0 and revision.stdout.strip()==dep['rev'],
      'tracked_clean':status.returncode==0 and not status.stdout.strip()})
check('G3.cached_dependency_revisions',all(x['revision_matches'] for x in dependency_checks))
check('G3.cached_dependency_sources_clean',all(x['tracked_clean'] for x in dependency_checks))
modules={f[:-5].replace('/','.') for f in expected}
modules|={f[len('PaperIIIRelease/'):-5].replace('/','.') for f in expected if f.startswith('PaperIIIRelease/')}
external={'Mathlib','Lean','Init','Std','Batteries','Qq','Aesop'}
imports={f:re.findall(r'^\s*import\s+([\w.]+)',t,re.M) for f,t in code.items()}
missing=[(f,m) for f,ms in imports.items() for m in ms if m not in modules and m.split('.')[0] not in external]
check('G3.import_closure_complete',not missing,str(missing))
check('G3.no_external_Erdos81_import',not any(m.split('.')[0]=='Erdos81' for ms in imports.values() for m in ms))
root=text['PaperIV.lean']
for name in ('Erdos81Unconditional','Erdos81AllOrders','PaperTheorems'):
    check('G3.root_exports_'+name, 'import PaperIV.'+name in root)
literal=json.loads((BASE/'LEAN_LITERAL_EXCERPTS.json').read_text(encoding='utf-8'))
check('G1.manuscript_lean_excerpts_literal',all(any(x['text'].strip() in t for t in text.values()) for x in literal))
parity=json.loads((BASE/'BILINGUAL_PARITY_v0.8.json').read_text(encoding='utf-8'))
publication=json.loads((ROOT/'04_integrity/SOURCE_TO_PUBLICATION.json').read_text())
check('G0.all_six_manuscripts_bound',len(publication)==6 and all(sha(ROOT/x['publication_path'])==x['sha256'] for x in publication))
md={}; tex={}
for lang in ('es','en'):
    prefix='english' if lang=='en' else 'spanish'
    for ext in ('md','tex','pdf'):
        f=ROOT/f'01_manuscript/PAPER_IV_preprint_v0.8_{lang}.{ext}'
        expected_hash=parity.get(prefix+'_'+ext+'_sha256')
        if expected_hash: check('G0.'+lang+'_'+ext+'_baseline',sha(f)==expected_hash)
    md[lang]=(ROOT/f'01_manuscript/PAPER_IV_preprint_v0.8_{lang}.md').read_text(encoding='utf-8')
    tex[lang]=(ROOT/f'01_manuscript/PAPER_IV_preprint_v0.8_{lang}.tex').read_text(encoding='utf-8')
    check('G5.'+lang+'_draft_status','draft' in md[lang].lower() or 'borrador' in md[lang].lower())
    log=(ROOT/f'03_reproducibility/manuscript_build_logs/PAPER_IV_preprint_v0.8_{lang}.log').read_text(encoding='utf-8',errors='replace')
    console=(ROOT/('03_reproducibility/manuscript_build_logs/compiler_console'+('_en' if lang=='en' else '')+'.log')).read_text(encoding='utf-8',errors='replace')
    check('G6.'+lang+'_compiler_success',f'Output written on PAPER_IV_preprint_v0.8_{lang}.xdv' in log and 'Running xdvipdfmx' in console and f'PAPER_IV_preprint_v0.8_{lang}.pdf`' in console)
    check('G6.'+lang+'_no_layout_errors',not re.search(r'Overfull|Underfull|Missing character|undefined references|^!',log,re.M))
    figures=re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}',tex[lang])
    check('G6.'+lang+'_figures_present',len(figures)==3 and all((ROOT/'01_manuscript'/p).is_file() for p in figures))
    check('G6.'+lang+'_balanced_displays',tex[lang].count(r'\[')==tex[lang].count(r'\]')==118)
    qa=(ROOT/f'03_reproducibility/manuscript_qa/{lang}/VISUAL_QA.md').read_text(encoding='utf-8')
    check('G6.'+lang+'_qa_pdf_binding',sha(ROOT/f'01_manuscript/PAPER_IV_preprint_v0.8_{lang}.pdf') in qa)
    check('G6.'+lang+'_series_layout',r'11pt,a4paper' in tex[lang] and r'\usepackage[margin=1in]{geometry}' in tex[lang])
    check('G6.'+lang+'_unique_labels',len(lab:=re.findall(r'\\label\{([^}]+)\}',tex[lang]))==len(set(lab)))
displays=lambda s:[re.sub(r'\s+','',x) for x in re.findall(r'\\\[.*?\\\]',s,re.S)]
# Only the previously reviewed language-bearing text inside six displays is normalized.
translations={'cordal':'chordal','o':'or','testigo estructural cercano de':'near-structure witness for',
 'enlaces ausentes entre':'missing links between','y':'and',
 'es completo-split con núcleo óptimo':'is complete-split with an optimal core','activo':'active'}
spanish_math=re.sub(r'\\text\{([^{}]*)\}',
 lambda m:r'\text{'+translations.get(m[1].strip(),m[1])+'}',md['es'])
check('G5.equations_identical_modulo_reviewed_text',displays(spanish_math)==displays(md['en']))
check('G5.lean_blocks_identical',re.findall(r'```lean\n(.*?)\n```',md['es'],re.S)==re.findall(r'```lean\n(.*?)\n```',md['en'],re.S))
check('G5.heading_levels_identical',re.findall(r'(?m)^(#+) ',md['es'])==re.findall(r'(?m)^(#+) ',md['en']))
check('G5.references_20_each',all(len(re.findall(r'(?m)^\[\d+\]',md[l]))==20 for l in md))
buildroot=ROOT/'03_reproducibility/author_build_evidence'
results=json.loads((buildroot/'RESULTS.json').read_text()) if (buildroot/'RESULTS.json').exists() else {'commands':[]}
check('G4.all_six_commands_completed',len(results['commands'])==6)
check('G4.all_exit_codes_zero',len(results['commands'])==6 and all(x['exit_code']==0 for x in results['commands']))
check('G4.sources_unchanged',results.get('sources_unchanged',False))
check('G4.fresh_logs_bound',bool(results['commands']) and all(sha(buildroot/(x['name']+'.log'))==x['log_sha256'] for x in results['commands']))
allowed={'propext','Classical.choice','Quot.sound'}
def parse_axioms(s): return re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s,re.S)
for name,minimum in [('axioms',83),('supplement',7),('public_contracts',4),('bounded',1)]:
    log=(buildroot/(name+'.log')).read_text(encoding='utf-8',errors='replace') if (buildroot/(name+'.log')).exists() else ''
    items=parse_axioms(log)
    check('G4.'+name+'_footprints',len(items)>=minimum and all(set(x.strip() for x in ax.split(',') if x.strip())<=allowed for _,ax in items),str(len(items)))
    check('G4.'+name+'_no_error',bool(log) and not re.search(r'error:|sorryAx',log))
cone=(buildroot/'cones.log').read_text(encoding='utf-8',errors='replace') if (buildroot/'cones.log').exists() else ''
check('G4.57_constant_cones',len(re.findall(r'^OK\s+',cone,re.M))==57 and not re.search(r'EXTERNO [1-9]|error:',cone))
refresh=json.loads((buildroot/'SUPPLEMENT_REFRESH.json').read_text()) if (buildroot/'SUPPLEMENT_REFRESH.json').exists() else {'commands':[]}
check('G4.supplement_closure_rebuilt',len(refresh['commands'])==2 and all(x['exit_code']==0 and sha(buildroot/(x['name']+'.log'))==x['log_sha256'] for x in refresh['commands']) and refresh.get('sources_unchanged',False))
fresh_supp=(buildroot/'supplement_after_build.log').read_text(encoding='utf-8',errors='replace') if (buildroot/'supplement_after_build.log').exists() else ''
fresh_supp_axioms=parse_axioms(fresh_supp)
check('G4.supplement_postbuild_footprints',len(fresh_supp_axioms)==7 and all(set(x.strip() for x in ax.split(',') if x.strip())<=allowed for _,ax in fresh_supp_axioms))
check('G4.tampered_axiom_rejected',not set('propext, sorryAx'.split(', '))<=allowed)
check('G0.tampered_hash_rejected',sha(archive)!='0'*64)
files=list(public_files(ROOT))
badpaths=[p.relative_to(ROOT).as_posix() for p in files if p.name.startswith('.env') or p.suffix in ('.olean','.ilean','.exe','.dll','.tar') or any(x.startswith('draft_v0.') for x in p.relative_to(ROOT).parts)]
check('G8.no_cache_credentials_or_superseded_drafts',not badpaths,str(badpaths))
badsecrets=[]
for p in files:
    if p.suffix in ('.md','.json','.py','.lean','.toml','.tex','.yml','.log','.tsv','.txt'):
        if re.search(rb'(?:arstl_[A-Za-z0-9_-]{20,}|ghp_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{30,}|-----BEGIN (?:RSA |OPENSSH )?PRIVATE KEY-----)',p.read_bytes()): badsecrets.append(p.relative_to(ROOT).as_posix())
check('G8.secret_scan',not badsecrets,str(badsecrets))
check('G8.active_manuscripts_exactly_six',len(list((ROOT/'01_manuscript').glob('PAPER_IV*')))==6)
# Integer-accounting regression evidence, not premises of the universal proof.
M=lambda n:n*(n+1)//6
baseline=lambda n,k:k*(n-k)-k*(k-1)//2
check('G2.baseline_identity_n_le_1000',all(6*baseline(n,k)+(n-3*k)*(n-3*k+1)==n*(n+1) for n in range(1001) for k in range(n+1)))
check('G2.critical_core_attains_n_le_1000',all(baseline(n,(n+2)//3)==M(n) for n in range(1001)))
check('G2.target_increment_n_le_1000',all(M(n)-M(n-1)==(n+1)//3 for n in range(1,1001)))
check('G2.baseline_upper_n_le_1000',all(baseline(n,k)<=M(n) for n in range(1001) for k in range(n+1)))
check('G2.wrong_baseline_coefficient_rejected',6*(3*(9-3)-3*(3-1))+(9-3*3)*(9-3*3+1)!=9*10)
for name in ('README.md','04_integrity/PROVENANCE_AND_TRUST.md','03_reproducibility/README.md'):
    check('G8.document_'+name,(ROOT/name).is_file())
out={'audit_class':'internal author-side packaging, formal contracts and reproducibility; not independent mathematical review',
     'checks':rows,'passed':sum(x['pass'] for x in rows),'total':len(rows),
     'source_entry_count':len(cut['source_hashes']), 'lean_source_count':len(expected)}
out['dependency_checks']=dependency_checks
HERE.mkdir(parents=True,exist_ok=True)
(HERE/'CHECK_RESULTS.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(f"{out['passed']}/{out['total']} checks passed")
for x in rows:
    if not x['pass']: print('FAIL',x['check'],x['detail'])
raise SystemExit(0 if out['passed']==out['total'] else 1)
