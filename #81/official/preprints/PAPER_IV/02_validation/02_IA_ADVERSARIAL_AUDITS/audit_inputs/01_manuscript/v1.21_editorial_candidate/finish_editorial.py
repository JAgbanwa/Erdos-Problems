"""Surgical, idempotent presentation corrections for the separate v1.21 candidate."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
LEAN = ROOT.parents[1] / '05_formalization/lean_piv-v12-fb459343d234'

NOTATION = {
    r'N_{\mathrm{lej}}': r'N_{\mathrm{far}}',
    r'N_{\rm lejano}': r'N_{\rm far}',
    r'e_{\rm cruz}': r'e_{\rm cross}',
    r'x_K^{\rm limpio}': r'x_K^{\rm clean}',
    r'E_{\rm cub}': r'E_{\rm covered}',
}

def outside(text, fn):
    # Do not edit literal code, formulae, URLs, or existing code spans.
    parts = re.split(r'(```.*?```|`[^`\n]+`|\\\[.*?\\\]|\\\(.*?\\\)|<https?://[^>]+>|!\[.*?\]\([^)]+\))', text, flags=re.S)
    for i in range(0, len(parts), 2):
        parts[i] = fn(parts[i])
    return ''.join(parts)

def once(text, old, new):
    if new in text:
        return text
    assert text.count(old) == 1, (old[:90], text.count(old))
    return text.replace(old, new)

def main():
    modules = {p.stem for p in LEAN.rglob('*.lean') if '.lake' not in p.parts and re.search(r'[a-z][A-Z]', p.stem)}
    modules.update({'PaperIV', 'Nibble', 'MixedRounding', 'FDCheck', 'ConstructorBudget', 'FREEZE_SCOPE.json'})
    def mark(m):
        word = m[0]
        if word in modules or '_' in word or ('.' in word and any(x in modules for x in word.split('.'))):
            return '`' + word + '`'
        return word
    for lang in ('en', 'es'):
        p = ROOT / f'PAPER_IV_preprint_v1.21_{lang}.md'
        text = p.read_text(encoding='utf-8')
        for word in ('Theorem', 'Model', 'Main', 'Basic', 'Defs', 'Setup', 'Bounds', 'Schedule', 'Oracle', 'Chain', 'Audit'):
            text = text.replace('`'+word+'`', word)
        # Presentation-only alpha-renamings, identical in both languages; never in Lean fences.
        parts = re.split(r'(```.*?```)', text, flags=re.S)
        for i in range(0, len(parts), 2):
            for old, new in NOTATION.items():
                parts[i] = parts[i].replace(old, new)
        text = ''.join(parts)
        if lang == 'en':
            text = once(text, 'Both \\(\\delta\\) and \\(\\tau\\) may be real. The root is chosen before \\(Q\\) and \\(\\tau\\).',
                'Both \\(\\delta\\) and \\(\\tau\\) may be real. The root is chosen before \\(Q\\) and \\(\\tau\\). Figure 3 summarizes the construction and its two conclusions.')
            text = once(text, 'The attribution printed in the document is retained; the repository account name is not substituted for an authorship attribution.',
                'The attribution printed in the document is retained. The README at that same commit credits Morluto for the mathematical proof, N0zoM1z0 for the manuscript and Lean implementation, and Jacobian at PreferenceLabs as part of the project: <https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/README.md>. These repository credits are distinguished from the signature printed on the manuscript.')
            text = once(text, 'Computations were reviewed within their stated scope; a finite search does not replace a universal proof.',
                'Jacobian is also credited by the project behind [5]; its use here is acknowledged separately from the logical dependencies of our formal proof. Computations were reviewed within their stated scope; a finite search does not replace a universal proof.')
            text = text.replace('This is a local formal check and a source freeze, not a completed internal or independent audit of version 1.2.',
                'These records establish the local build and source identity; the completed internal audit and the ongoing external audit are separate stages, described below.')
        else:
            text = text.replace('basta la holgura fraccional', 'basta el margen fraccional')
            text = text.replace('**Teorema 6.1 (estabilidad integral).** Existe ', '**Teorema 6.1 (estabilidad integral).** Existen ')
            text = text.replace('estrella con pesos de ambos signos', 'estrella con signos')
            text = once(text, 'Se conserva la firma que figura en el documento; el nombre de la cuenta del repositorio no se sustituye por una atribución de autoría.',
                'Se conserva la firma que figura en el documento. El README de ese mismo commit acredita a Morluto por la prueba matemática, a N0zoM1z0 por el manuscrito y la implementación Lean, y a Jacobian de PreferenceLabs como parte del proyecto: <https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/README.md>. Estos créditos del repositorio se distinguen de la firma impresa en el manuscrito.')
            text = once(text, 'Los cálculos se revisaron según su alcance; una búsqueda finita no reemplaza una prueba universal.',
                'El proyecto de [5] también acredita a Jacobian; su uso aquí se declara por separado de las dependencias lógicas de nuestra prueba formal. Los cálculos se revisaron según su alcance; una búsqueda finita no reemplaza una prueba universal.')
            text = text.replace('Éste es un control formal local y un congelado de fuentes, no una auditoría interna o independiente completada de la versión 1.2.',
                'Estos registros establecen la compilación local y la identidad de fuentes; la auditoría interna completada y la auditoría externa en curso son etapas separadas, descritas a continuación.')
            # The figure citation follows the same sentence in both editions.
            line = next(x for x in text.splitlines() if 'pueden ser reales' in x and 'raíz' in x)
            if 'Figura 3' not in line:
                text = once(text, line, line + ' La Figura 3 resume la construcción y sus dos conclusiones.')
            def spanish(s):
                for old, new in [('el gap', 'la brecha'), ('El gap', 'La brecha'), ('del gap', 'de la brecha'), ('un gap', 'una brecha')]:
                    s = s.replace(old, new)
                for old, new in {'baseline':'valor base','build':'compilación','packings':'empaquetamientos','targets':'objetivos','target':'objetivo','logs':'registros','log':'registro','gap':'brecha'}.items():
                    s = re.sub(r'\b'+old+r'\b', new, s)
                return s.replace('compilación exitoso','compilación exitosa').replace('un compilación','una compilación').replace('brecha mixto','brecha mixta').replace('brecha mixta nulo','brecha mixta nula').replace('brecha nulo','brecha nula').replace('brecha cero','brecha nula')
            text = outside(text, spanish)
        text = outside(text, lambda s: re.sub(r'(?<![\w/])\b[A-Za-z][A-Za-z0-9]*(?:[._][A-Za-z0-9_]+)*\b(?![\w/])', mark, s))
        text = re.sub(r'\n{4,}', '\n\n\n', text)
        p.write_text(text, encoding='utf-8')

if __name__ == '__main__':
    main()
