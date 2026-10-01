"""Apply only the two NEW-05 Spanish terminology corrections to the r3 baseline."""
from pathlib import Path
import difflib,hashlib,json
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'v1.22_editorial_candidate_r3'
p=ROOT/'PAPER_IV_preprint_v1.22_es.md'
old=(BASE/p.name).read_text(encoding='utf-8'); new=old
changes=[('la programación numérica de C.3','el calendario numérico de C.3'),
         ('cota adaptada con muestra fijada','cota adaptada con muestras con anclajes')]
for before,after in changes:
    assert new.count(before)==1,before
    new=new.replace(before,after)
p.write_text(new,encoding='utf-8')
(ROOT/'CHANGES_es.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='r3/'+p.name,tofile='r4/'+p.name)),encoding='utf-8')
(ROOT/'TERMINOLOGY_DELTA.json').write_text(json.dumps({'revision':'v1.22-r4','finding':'NEW-05','changes':changes,'source_sha256':hashlib.sha256((BASE/p.name).read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'english_changes':0},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('Applied exactly two Spanish phrase replacements; English untouched.')
