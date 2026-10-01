"""Apply presentation-only changes to copies of the established series pipeline."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent
for name in ('build_draft.py','build_draft_en.py'):
    p=ROOT/name
    s=p.read_text(encoding='utf-8')
    s=s.replace('from typeset_helpers import mark_identifiers','from typeset_helpers import mark_identifiers, literal_lean')
    s=s.replace("STEM = 'PAPER_IV_preprint_v1.2_", "STEM = 'PAPER_IV_preprint_v1.21_")
    a=s.index('    # Literal Lean is retained')
    b=s.index('    # A heading immediately',a)
    s=s[:a]+"    body = re.sub(r'```lean\\n(.*?)\\n```', literal_lean, body, flags=re.S)\n"+s[b:]
    s=s.replace("[str(TECTONIC),'--keep-logs'", "[str(TECTONIC),'--only-cached','--keep-logs'")
    s=s.replace("return m[0] if r'\\ ' in m[1] else", "return r'\\mbox{'+m[0]+'}' if r'\\ ' in m[1] else")
    s=s.replace("'font.family': 'DejaVu Serif'", "'pdf.fonttype':42, 'ps.fonttype':42, 'font.family': 'DejaVu Serif'")
    s=s.replace('Con holgura', 'Con margen')
    p.write_text(s,encoding='utf-8')
for name in ('series_template.tex','series_template_en.tex'):
    p=ROOT/name;s=p.read_text(encoding='utf-8')
    extra='\\newfontfamily\\LeanSymbols{seguisym.ttf}[Path=C:/Windows/Fonts/]\n\\newlength{\\LeanCharWidth}\n'
    if '\\LeanSymbols' not in s:
        s=s.replace('\\usepackage{amsmath,amssymb}',extra+'\\usepackage{amsmath,amssymb}')
    p.write_text(s,encoding='utf-8')
for name in ('make_stability_figure.py','make_stability_figure_es.py'):
    p=ROOT/name;s=p.read_text(encoding='utf-8')
    s=s.replace("'font.family':", "'pdf.fonttype':42,'ps.fonttype':42,'font.family':")
    s=s.replace('Cotas de ediciones y baseline', 'Cotas de ediciones y valor base')
    p.write_text(s,encoding='utf-8')
