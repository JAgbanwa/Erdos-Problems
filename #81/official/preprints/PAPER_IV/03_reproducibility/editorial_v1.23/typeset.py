"""Build final delivered TeX serially with the existing cached Tectonic engine.

No downloads, Lean builds or figure regeneration. Temporary AUX files stay
outside the repository. Uses two full invocations of the established engine.
"""
from pathlib import Path
import argparse, hashlib, json, re, shutil, subprocess
import pymupdf as fitz
from PIL import Image, ImageDraw

PAPER=Path(__file__).resolve().parents[2]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--work',type=Path,required=True)
    ap.add_argument('--engine',type=Path,default=Path('C:/Users/jtraverso/.cache/e81-editorial-tools/tectonic/tectonic.exe'))
    a=ap.parse_args(); work=a.work.resolve()
    assert not work.is_relative_to(PAPER), 'Keep intermediates outside the package'
    evidence=PAPER/'02_validation/03_EDITORIAL_CHECKS/v1.23'
    records=[]
    for lang in ('en','es'):
        stem=f'PAPER_IV_preprint_v1.23_{lang}'
        tex=PAPER/'01_manuscript'/f'{stem}.tex'
        out=work/lang; out.mkdir(parents=True,exist_ok=True)
        for run in (1,2):
            p=subprocess.run([str(a.engine),'--only-cached','--keep-logs','--keep-intermediates','--reruns','1','--outdir',str(out),str(tex)],cwd=tex.parent,capture_output=True)
            (evidence/f'compiler_{lang}_{run}.log').write_bytes(p.stdout+b'\n'+p.stderr)
            p.check_returncode()
        log=(out/(stem+'.log')).read_text(encoding='utf-8',errors='replace')
        # Tectonic reports XDV in the TeX log and the delivered PDF in its console.
        console=(p.stdout+b'\n'+p.stderr).decode('utf-8',errors='replace')
        assert 'Output written on '+stem+'.xdv' in log
        assert 'Writing `' in console and stem+'.pdf' in console
        bad=re.findall(r'^.*(?:Overfull \\[hv]box|Missing character|undefined references|Undefined control sequence|Fatal error).*$',log,re.M)
        assert not bad,bad
        shutil.copy2(out/(stem+'.log'),evidence/f'tex_{lang}.log')
        pdf=tex.with_suffix('.pdf'); shutil.copy2(out/(stem+'.pdf'),pdf)
        assert sha(pdf)==sha(out/(stem+'.pdf'))
        renders=out/'renders'; renders.mkdir(exist_ok=True)
        doc=fitz.open(pdf)
        texts=[]
        for i,page in enumerate(doc):
            page.get_pixmap(matrix=fitz.Matrix(1.35,1.35)).save(renders/f'page_{i+1:03}.png')
            texts.append(page.get_text())
        for offset in range(0,len(doc),8):
            sheet=Image.new('RGB',(1600,1150),'#dedede'); draw=ImageDraw.Draw(sheet)
            for j in range(min(8,len(doc)-offset)):
                im=Image.open(renders/f'page_{offset+j+1:03}.png'); im.thumbnail((385,530))
                x=(j%4)*400+(400-im.width)//2; y=(j//4)*575+27
                sheet.paste(im,(x,y)); draw.text(((j%4)*400+12,(j//4)*575+8),f'{lang.upper()} {offset+j+1}',fill='black')
            sheet.save(renders/f'contact_{offset//8+1:02}.png')
        (evidence/f'pdf_text_{lang}.txt').write_text('\n\f\n'.join(texts),encoding='utf-8')
        records.append(dict(language=lang,pages=len(doc),tex_sha256=sha(tex),pdf_sha256=sha(pdf),passes=2,diagnostic_errors=bad,render_directory=str(renders),visual_review='PENDING'))
        print(json.dumps(records[-1]),flush=True)
    (evidence/'TYPESETTING.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
if __name__=='__main__': main()
