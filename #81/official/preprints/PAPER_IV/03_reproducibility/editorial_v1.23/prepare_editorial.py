"""Deterministic administrative-only delta from the published v1.22 sources.

Run once before typesetting. No Lean invocation; no changes to proof paragraphs.
The complete old/new paragraph ledger is emitted before downstream checks.
"""
from pathlib import Path
import difflib
import hashlib
import json
import re
import subprocess

PAPER = Path(__file__).resolve().parents[2]
BASE = PAPER / '02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/published_v1.22/01_manuscript'
OUT = PAPER / '01_manuscript'
EVIDENCE = PAPER / '02_validation/03_EDITORIAL_CHECKS/v1.23'
TOOLS = Path('C:/Users/jtraverso/.cache/e81-editorial-tools')
PANDOC = TOOLS / 'pandoc/pandoc-3.11/pandoc.exe'

CHANGES = {
 'en': [
  ('**Audit status of this editorial candidate.**', '**Verification evidence.** The frozen sources and the recorded external build support the formal claims above. The consolidated report for v1.22-r4 records PASS for gates E0–E8. The repository retains that report, its scope limitations and the complete audit history. Version 1.23 changes only editorial presentation; it uses the same Lean source cut and does not claim a new build or a new external audit. Human peer review remains a separate assessment.'),
  ('The series repository, available at', 'The series repository, available at <https://github.com/jtraverso/erdos-81-chordal-clique-partitions>, provides the bilingual manuscripts, frozen formal sources and verification evidence for Papers I–IV. The audited v1.22 package is preserved under the tag `paper-IV-v1.22` and in the audit backup directory. This editorial revision uses the same source cut identified above. The series concept DOI is <https://doi.org/10.5281/zenodo.21273143>; the repository README and changelog record version-specific publication and audit information.'),
  ('The single audit command described in §7 executes', 'The single audit command described in §7 executes all 19 targets, including the root, the individual audit targets and the export check. Lean and dependency revisions are recorded in lean-toolchain and lake-manifest.json. Compilation, public export, axiom inspection and semantic correspondence are distinct checks. The source freeze is unchanged. The consolidated external report and its evidence distinguish individual semantic comparisons from statements covered by the proof-component ledger and compiled declarations.'),
  ('**Scope of the written proof.**', '**Scope of the written proof.** The table below records seven derivations examined in the consolidated external review. Its assessment, ACCEPTABLE_SUMMARY for each row, retains the stated expository limit concerning the cited second-moment estimates in C.2. A successful build checks formal derivations, not completeness of exposition; the written-proof assessment remains distinct from compilation and from human peer review. The audit history and detailed assessments are retained with the supplementary evidence.'),
  ('Appendix E.4 derives the retained terminal accounts', 'Appendix E.4 derives the retained terminal accounts used in §6.6, F.3 proves clique recovery, and F.5 explains the three-case assembly of the adapted pinned-sample bound. The consolidated external report records the corresponding checks and their scope limitations. These checks compare the written accounts with the frozen formal development; they do not turn local compilation into a substitute for mathematical review.'),
 ],
 'es': [
  ('**Estado de auditoría de esta candidata editorial.**', '**Evidencia de verificación.** Las fuentes congeladas y el build externo registrado respaldan las afirmaciones formales anteriores. El informe consolidado de v1.22-r4 registra PASS para las puertas E0–E8. El repositorio conserva ese informe, sus límites de alcance y el historial completo de auditoría. La versión 1.23 cambia únicamente la presentación editorial; utiliza el mismo corte Lean y no afirma un nuevo build ni una nueva auditoría externa. La revisión humana por pares sigue siendo una evaluación separada.'),
  ('El repositorio de la serie, disponible en', 'El repositorio de la serie, disponible en <https://github.com/jtraverso/erdos-81-chordal-clique-partitions>, ofrece los manuscritos bilingües, las fuentes formales congeladas y la evidencia de verificación de Papers I–IV. El paquete auditado v1.22 se conserva bajo la etiqueta `paper-IV-v1.22` y en el directorio de respaldo de auditoría. Esta revisión editorial utiliza el mismo corte de fuentes identificado arriba. El DOI de concepto de la serie es <https://doi.org/10.5281/zenodo.21273143>; el README y el changelog del repositorio registran la información de publicación y auditoría propia de cada versión.'),
  ('El comando único de auditoría descrito en §7 ejecuta', 'El comando único de auditoría descrito en §7 ejecuta los 19 objetivos, incluidos la raíz, los objetivos individuales de auditoría y el control de exportación. Las revisiones de Lean y sus dependencias están registradas en lean-toolchain y lake-manifest.json. Compilación, exportación pública, inspección de axiomas y correspondencia semántica son controles distintos. El congelado de fuentes no cambia. El informe externo consolidado y su evidencia distinguen las comparaciones semánticas individuales de los enunciados cubiertos por el registro de componentes de prueba y las declaraciones compiladas.'),
  ('**Alcance de la prueba escrita.**', '**Alcance de la prueba escrita.** La tabla siguiente registra siete derivaciones examinadas en la revisión externa consolidada. Su evaluación, ACCEPTABLE_SUMMARY para cada fila, conserva el límite expositivo declarado sobre las estimaciones de segundo momento citadas en C.2. Un build satisfactorio verifica derivaciones formales, no la integridad de su exposición; la evaluación de la prueba escrita sigue siendo distinta de la compilación y de la revisión humana por pares. El historial de auditoría y las evaluaciones detalladas se conservan con la evidencia complementaria.'),
  ('El Apéndice E.4 desarrolla las cuentas terminales', 'El Apéndice E.4 desarrolla las cuentas terminales conservadas que se usan en §6.6, F.3 demuestra la recuperación de la clique y F.5 explica el ensamblaje de tres casos de la cota adaptada con muestras con anclajes. El informe externo consolidado registra las comprobaciones correspondientes y sus límites de alcance. Esas comprobaciones contrastan las cuentas escritas con el desarrollo formal congelado; no convierten la compilación local en un sustituto de la revisión matemática.'),
 ]
}

def sha(data): return hashlib.sha256(data).hexdigest()

def tex_paragraph(md):
    result = subprocess.run([str(PANDOC), '-f', 'markdown+tex_math_single_backslash+raw_tex', '-t', 'latex', '--wrap=none'], input=md, text=True, encoding='utf-8', capture_output=True, check=True).stdout.strip()
    def code(m):
        token=m[1].replace(r'\_', '_')
        return r'{\ttfamily\small ' + re.sub(r'([._/-])', lambda k: (r'\_' if k[0]=='_' else k[0])+r'\discretionary{\hbox{\ensuremath{\hookrightarrow}}}{}{}', token) + '}'
    return re.sub(r'\\texttt\{([^{}]+)\}', code, result)

def main():
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    ledger=[]; protection=[]
    for lang in ('en','es'):
        stem=f'PAPER_IV_preprint_v1.22_{lang}'
        original=(BASE/(stem+'.md')).read_text(encoding='utf-8')
        tex_original=(BASE/(stem+'.tex')).read_text(encoding='utf-8')
        md=original; tex=tex_original
        start=md.index('**Preprint:**'); end=md.index('\n\n**MSC 2020:**',start)
        header=('**Preprint:** version 1.23.  \n**Date:** October 1, 2026.' if lang=='en' else '**Preprint:** versión 1.23.  \n**Fecha:** 1 de octubre de 2026.')
        ledger.append(dict(id=f'{lang}-front',before=md[start:end],after=header,change_class='STRUCTURAL_FORM'))
        md=md[:start]+header+md[end:]
        start=tex.index(r'\textbf{Preprint:}'); end=tex.index('\n\n\\textbf{MSC 2020:}',start)
        tex=tex[:start]+tex_paragraph(header)+tex[end:]
        for i,(prefix,new) in enumerate(CHANGES[lang]):
            found=[p for p in md.split('\n\n') if p.startswith(prefix)]
            assert len(found)==1,(lang,prefix,len(found))
            old=found[0]
            md=md.replace(old,new,1)
            # Paragraph boundaries in the already audited TeX are preserved.
            tex_prefix=prefix.replace('**',r'\textbf{',1) if prefix.startswith('**') else prefix
            if prefix.startswith('**'): tex_prefix=prefix.replace('**','',2)
            candidates=[p for p in tex.split('\n\n') if (p.startswith(prefix) or (prefix.startswith('**') and p.startswith(r'\textbf{'+tex_prefix+'}')))]
            assert len(candidates)==1,(lang,prefix,len(candidates))
            tex=tex.replace(candidates[0],tex_paragraph(new),1)
            ledger.append(dict(id=f'{lang}-{i+1}',before=old,after=new,change_class='CLARITY'))
        changed_old={e['before'] for e in ledger if e['id'].startswith(lang)}
        for i,p in enumerate(original.split('\n\n')):
            if any(x in p for x in changed_old): continue
            assert p in md,(lang,i)
            protection.append(dict(id=f'{lang}-paragraph-{i}',sha256=sha(p.encode()),allowed='NONE',owner='author'))
        for pattern in (r'\\\[(.*?)\\\]',r'```lean\n(.*?)```'):
            assert re.findall(pattern,original,re.S)==re.findall(pattern,md,re.S),(lang,pattern)
        assert original.split('## Abstract' if lang=='en' else '## Resumen')[1].split('## 1.')[0] == md.split('## Abstract' if lang=='en' else '## Resumen')[1].split('## 1.')[0]
        newstem=stem.replace('1.22','1.23')
        for ext,before,after in (('md',original,md),('tex',tex_original,tex)):
            (OUT/(newstem+'.'+ext)).write_text(after,encoding='utf-8')
            (EVIDENCE/f'CHANGES_{lang}_{ext}.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile=stem+'.'+ext,tofile=newstem+'.'+ext)),encoding='utf-8')
    (EVIDENCE/'ADMINISTRATIVE_DELTA.json').write_text(json.dumps(ledger,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    (EVIDENCE/'PROTECTED_PARAGRAPHS.json').write_text(json.dumps(protection,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'languages':2,'administrative_changes':len(ledger),'protected_paragraphs':len(protection),'display_math_and_lean_blocks':'UNCHANGED','abstracts':'UNCHANGED'}))

if __name__=='__main__': main()
