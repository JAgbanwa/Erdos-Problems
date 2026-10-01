"""One-time mechanical status/provenance synchronization after the final audit."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
for lang in ('en', 'es'):
    p = ROOT / f'PAPER_IV_preprint_v1.21_{lang}.md'
    t = p.read_text(encoding='utf-8')
    if lang == 'en':
        replacements = {
            'editorial revision prepared alongside the external audit of version 1.2.': 'editorial revision addressing the completed external audit of version 1.2.',
            'Version 1.2 has completed its internal audit, and its external audit is in progress.': 'Version 1.2 has completed both audits: the external formal reproduction passed, while its overall verdict was INCONCLUSIVE because four derivations required fuller exposition.',
            'The completed internal audit and ongoing external audit are separate stages, described below.': 'The completed internal and external audits are separate stages, described below.',
            'Its internal audit is complete and the external v1.2 review is in progress;': 'Its internal audit is complete; the external v1.2 review has concluded with formal reproduction PASS and mathematical exposition INCONCLUSIVE;',
            'It is retained for provenance, but is not the public proof chosen here.': 'It is not the proof selected for the public Theorem C. It remains in use in the formal unrestricted-classification wrappers described in §7 and Table 9.',
        }
    else:
        replacements = {
            'revisión editorial preparada en paralelo con la auditoría externa de la versión 1.2.': 'revisión editorial que atiende la auditoría externa completada de la versión 1.2.',
            'La versión 1.2 completó su auditoría interna y su auditoría externa está en curso.': 'La versión 1.2 completó ambas auditorías: la reproducción formal externa obtuvo PASS, mientras que el veredicto global fue INCONCLUSIVE porque cuatro derivaciones requerían mayor desarrollo expositivo.',
            'la auditoría interna completada y la auditoría externa en curso son etapas separadas': 'las auditorías interna y externa completadas son etapas separadas',
            'La ejecución externa `run_v1.2_r1` sigue en curso al preparar esta candidata.': 'La ejecución externa completada `run_v1.2_r1` dio INCONCLUSIVE global por cuatro derivaciones que requerían mayor desarrollo expositivo, pero PASS en reproducción formal: se compilaron correctamente 607 módulos principales, los 19 objetivos y el anexo de 50 módulos. Los 607 objetos principales compilados fueron idénticos byte a byte a los registrados por el autor.',
            'las explicaciones ampliadas de la versión 1.21 requieren': 'las explicaciones ampliadas y las precisiones de dependencias de la versión 1.21 requieren',
            'Su auditoría interna está completada y la revisión externa de v1.2 está en curso;': 'Su auditoría interna está completada; la revisión externa de v1.2 concluyó con PASS en reproducción formal e INCONCLUSIVE en exposición matemática;',
            'Se conserva por procedencia, pero no es la prueba pública elegida aquí.': 'No es la prueba seleccionada para el Teorema C público. Sigue utilizándose en las interfaces formales de clasificación irrestricta descritas en §7 y Tabla 9.',
        }
    for old, new in replacements.items():
        if new in t:
            continue
        if old not in t:
            raise ValueError(f'Missing exact replacement in {lang}: {old}')
        t = t.replace(old, new)
    p.write_text(t, encoding='utf-8')
