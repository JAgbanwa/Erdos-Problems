"""Final narrowly scoped prose/metadata pass; no Lean, constants, or theorem changes."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
for lang in ('en','es'):
    p=ROOT/f'PAPER_IV_preprint_v1.21_{lang}.md';s=p.read_text(encoding='utf-8')
    for ordinary in ('Assembly','Comparison','Counting','Pinned','Reduction','Sampling','Selection','Selector','Transfer','Vizing'):
        s=s.replace('`'+ordinary+'`', ordinary)
    changes={
      'en':{
        'working Markdown revision prepared alongside':'editorial revision prepared alongside',
        'The typeset editions and the editorial and bilingual review of version 1.21 remain pending.':'The accompanying English and Spanish MD, TeX and PDF editions are submitted for renewed editorial, mathematical and bilingual review.',
        'This is a local formal check and source freeze, not a completed internal or independent audit of version 1.2.':'These records establish the local build and source identity. The completed internal audit and ongoing external audit are separate stages, described below.',
        'The new source freeze is identified locally; new internal and adversarial reviews of this enlarged source-and-manuscript pair remain pending.':'The source freeze is unchanged. Its internal audit is complete and the external v1.2 review is in progress; the revised exposition in v1.21 requires its own review.',
        'The numerical domination of that schedule is still summarized, not expanded inequality by inequality.':'The estimates from the schedule to the selector bound are also developed in C.3; the remaining tower iteration is a symbolic comparison with the recurrence in §6.3.',
        'The gluing estimate charges every changed edge either to a conflict or to a section mismatch:':'Write \\(\\operatorname{mis}_c\\) for the number of mismatches in section \\(c\\). The gluing estimate charges every changed edge either to a conflict or to one of these mismatches:',
      },
      'es':{
        'revisión de trabajo en Markdown preparada en paralelo':'revisión editorial preparada en paralelo',
        'Quedan pendientes las ediciones maquetadas y la revisión editorial y bilingüe de la versión 1.21.':'Las ediciones adjuntas en Markdown, TeX y PDF, en inglés y español, se presentan para una nueva revisión editorial, matemática y bilingüe.',
        'La dominación numérica de ese calendario sigue resumida, no desarrollada desigualdad por desigualdad.':'C.3 desarrolla también las estimaciones que llevan del calendario a la cota del selector; la iteración de torre restante es una comparación simbólica con la recurrencia de §6.3.',
        'de ese brecha':'de esa brecha',
        'para el **brecha triangular**':'para la **brecha triangular**',
        'la brecha **mixto**':'la brecha **mixta**',
        'dla brecha':'de la brecha',
        'de Apéndice G.1':'del Apéndice G.1',
        'La estimación de pegado carga cada arista modificada a un conflicto o a una discrepancia de sección:':'Escribamos \\(\\operatorname{mis}_c\\) para el número de discrepancias de la sección \\(c\\). La estimación de pegado carga cada arista modificada a un conflicto o a una de esas discrepancias:',
        'El nuevo congelado de fuentes se identifica localmente; las nuevas revisiones interna y adversarial de este par ampliado de fuentes y manuscritos siguen pendientes.':'El congelado de fuentes no cambia. Su auditoría interna está completada y la revisión externa de v1.2 está en curso; la exposición revisada de v1.21 requiere su propia revisión.',
      }
    }[lang]
    for a,b in changes.items():s=s.replace(a,b)
    if lang=='es':
        for line in s.splitlines():
            if line.startswith('El punto único de auditoría') or line.startswith('El comando único de auditoría'):
                s=s.replace(line,line.replace('quedan pendientes','requieren revisión diferenciada'))
    p.write_text(s,encoding='utf-8')
