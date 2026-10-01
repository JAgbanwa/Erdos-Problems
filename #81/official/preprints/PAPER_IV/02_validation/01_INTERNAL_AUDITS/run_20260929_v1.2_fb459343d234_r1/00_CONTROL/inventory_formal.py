"""Static inventory, not a substitute for semantic review or elaboration."""
import ast
import csv
import hashlib
import json
import re
from pathlib import Path

RUN = Path(__file__).resolve().parents[1]
PAPER = RUN.parents[2]
SRC = PAPER / '05_formalization/lean_piv-v12-fb459343d234'
MS = PAPER / '01_manuscript/v1.2_full_rebuild_candidate'
OUT = RUN / '20_EVIDENCE/G3_FORMAL'

def save(p, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')

def stripped(text):
    # Nested Lean block comments, line comments and strings; preserve newlines.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; out.extend('  '); i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; out.extend('  '); i += 2
        elif depth:
            out.append('\n' if text[i]=='\n' else ' '); i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: j = len(text)
            out.extend(' '*(j-i)); i = j
        elif text[i] == '"':
            out.append(' '); i += 1
            while i < len(text):
                if text[i]=='\\': out.extend('  '); i += 2
                elif text[i]=='"': out.append(' '); i += 1; break
                else: out.append('\n' if text[i]=='\n' else ' '); i += 1
        else:
            out.append(text[i]); i += 1
    return ''.join(out)

def main():
    sources = {p.relative_to(SRC).with_suffix('').as_posix().replace('/', '.'): p for p in SRC.rglob('*.lean')}
    graph, unsafe, declarations = {}, [], {}
    for module, p in sources.items():
        raw = p.read_text(encoding='utf-8-sig')
        data = stripped(raw)
        graph[module] = re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)', data, re.M)
        for match in re.finditer(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:unsafe\s+)?axiom\s+', data, re.M):
            unsafe.append({'module': module, 'line': data[:match.start()].count('\n')+1, 'token': match.group()})
        for m in re.finditer(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev|structure)\s+([\w.\u0080-\uffff']+)", data, re.M):
            name = m.group(1)
            stop = data.find(':=', m.end())
            header = raw[m.start():stop if stop>=0 else m.end()]
            declarations.setdefault(name.split('.')[-1], []).append({'module': module, 'local_name': name, 'line': data[:m.start()].count('\n')+1, 'header': header.strip()})
    def closure(root):
        seen, todo = set(), [root]
        while todo:
            m = todo.pop()
            if m in seen: continue
            seen.add(m)
            todo.extend(x for x in graph.get(m, []) if x in sources)
        return seen
    root = closure('PaperIV')
    exports = re.findall(r'^#check\s+(\S+)', (SRC/'ReleaseExportCheck.lean').read_text(encoding='utf-8'), re.M)
    evidence = json.loads((RUN/'20_EVIDENCE/G4_LEAN/MODULE_PROVENANCE.json').read_text())
    built = {r['module'] for r in evidence}
    check_imports = graph['ReleaseExportCheck'] == ['PaperIV']
    rows = []
    for name in exports:
        candidates = declarations.get(name.split('.')[-1], [])
        override = {'E17Bridge.ExplicitAssembly':'E17.ExplicitFarAssembly', 'E19':'E19.GateBounds'}
        preferred = [c for c in candidates if c['module'] == override.get(name.rsplit('.', 1)[0], name.rsplit('.', 1)[0])]
        c = preferred[0] if len(preferred)==1 else candidates[0] if len({c['module'] for c in candidates})==1 else None
        rows.append({'declaration': name, 'source_candidates': candidates if c is None else [c], 'module_in_root': c['module'] in root if c else None, 'module_built': c['module'] in built if c else None, 'export_evidence': 'G4_LEAN/EXPORT_TYPES.txt', 'status': 'TRACE_AVAILABLE' if c else 'NEEDS_NAMESPACE_RESOLUTION'})
    save(OUT/'SOURCE_INVENTORY.json', {'source_count':len(sources), 'root_import_closure':sorted(root), 'release_export_imports':graph['ReleaseExportCheck'], 'unsafe_tokens':unsafe, 'exports':rows})
    save(OUT/'IMPORT_GRAPH.json', graph)
    protected = {}
    for lang in ('en', 'es'):
        text = (MS/f'PAPER_IV_preprint_v1.2_{lang}.md').read_text(encoding='utf-8-sig')
        elements = []
        for kind, pattern in [('display',r'\\\[(.*?)\\\]'),('code',r'```lean\s*(.*?)```'),('heading',r'(?m)^#{1,4} .*$')]:
            for m in re.finditer(pattern,text,re.S if kind!='heading' else 0):
                value = m.group()
                elements.append({'kind':kind,'line':text[:m.start()].count('\n')+1,'text':value,'sha256':hashlib.sha256(value.encode()).hexdigest()})
        protected[lang] = elements
    save(RUN/'00_CONTROL/PROTECTED_ELEMENTS.json', protected)
    summary = {'source_modules':len(sources),'root_modules':len(root),'exports':len(exports),'sole_export_import_is_PaperIV':check_imports,'unsafe_tokens':unsafe,'ambiguous_sources':[r['declaration'] for r in rows if r['status']!='TRACE_AVAILABLE'],'limits':'Lexical scan complements, but does not replace, elaborated exports and transitive axiom checks. No semantic PASS inferred.'}
    save(OUT/'INVENTORY_SUMMARY.json',summary)
    print(json.dumps(summary,indent=2))

if __name__ == '__main__':
    main()
