"""Read-only checks of final manuscripts; renders and evidence go only to this run."""
import hashlib
import json
import re
from pathlib import Path
import fitz
from PIL import Image, ImageDraw

RUN = Path(__file__).resolve().parents[1]
PAPER = RUN.parents[2]
MS = PAPER / '01_manuscript/v1.2_full_rebuild_candidate'
OUT = RUN / '20_EVIDENCE/G5_PARITY'
VIS = RUN / '20_EVIDENCE/G6_PDF'

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    VIS.mkdir(parents=True, exist_ok=True)
    texts = {lang:(MS/f'PAPER_IV_preprint_v1.2_{lang}.md').read_text(encoding='utf-8-sig') for lang in ('en','es')}
    def math(s):
        return re.findall(r'\\\[(.*?)\\\]|\\\((.*?)\\\)', s, re.S)
    def normalize(s):
        # Retain text-bearing differences for explicit translation review.
        return re.sub(r'\s+', '', s)
    equations = {lang:[normalize(a or b) for a,b in math(t)] for lang,t in texts.items()}
    differences = [{'index':i,'en':a,'es':b} for i,(a,b) in enumerate(zip(equations['en'],equations['es'])) if a!=b]
    codes = {lang:re.findall(r'```lean\s*(.*?)```',t,re.S) for lang,t in texts.items()}
    headings = {}
    for lang,t in texts.items():
        headings[lang] = [(len(m[1]), re.findall(r'(?:\d+|[A-G])(?:\.\d+)*(?:a|b|′)?', m[2].split(':')[0])) for m in re.finditer(r'(?m)^(#+) (.*)$',t)]
    parity = {'equation_counts':{k:len(v) for k,v in equations.items()},'math_text_differences':differences,'lean_code_equal':codes['en']==codes['es'],'lean_code_counts':{k:len(v) for k,v in codes.items()},'labels_equal':re.findall(r'\\tag\{([^}]+)\}',texts['en'])==re.findall(r'\\tag\{([^}]+)\}',texts['es']), 'labels_count':len(re.findall(r'\\tag\{([^}]+)\}',texts['en'])), 'figure_counts':{k:len(re.findall(r'!\[',v)) for k,v in texts.items()},'status':'STATIC_CHECKS_PENDING_TRANSLATION_REVIEW'}
    (OUT/'RESULTS.json').write_text(json.dumps(parity,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    pdfs = []
    for lang in ('en','es'):
        path = MS/f'PAPER_IV_preprint_v1.2_{lang}.pdf'
        pdf = fitz.open(path)
        rows, sheets, thumbs = [], [], []
        for i,page in enumerate(pdf):
            text = page.get_text()
            bounds=[]
            for word in page.get_text('words'):
                if word[0]<-1 or word[1]<-1 or word[2]>page.rect.width+1 or word[3]>page.rect.height+1:
                    bounds.append(word)
            pix=page.get_pixmap(matrix=fitz.Matrix(1.35,1.35),alpha=False)
            png=VIS/f'{lang}_{i+1:03d}.png'
            pix.save(png)
            im=Image.open(png); im.thumbnail((340,490))
            thumbs.append((i+1,im.copy())); im.close()
            rows.append({'page':i+1,'characters':len(text),'out_of_page_words':bounds,'replacement_glyph': '\ufffd' in text, 'render':png.name})
            if len(thumbs)==9 or i==len(pdf)-1:
                sheet=Image.new('RGB',(1080,1560),'#dddddd'); draw=ImageDraw.Draw(sheet)
                for j,(num,im) in enumerate(thumbs):
                    x=(j%3)*360; y=(j//3)*520
                    draw.text((x+10,y+4),f'{lang.upper()} {num}',fill='black')
                    sheet.paste(im,(x+10,y+24)); im.close()
                name=f'{lang}_contact_{len(sheets)+1:02d}.png'
                sheet.save(VIS/name);sheet.close();sheets.append(name);thumbs=[]
        (VIS/f'{lang}_extracted.txt').write_text('\n\f\n'.join(p.get_text() for p in pdf),encoding='utf-8')
        log=(MS/f'PAPER_IV_preprint_v1.2_{lang}.log').read_text(encoding='utf-8',errors='replace')
        warnings=[line for line in log.splitlines() if any(x in line for x in ['Overfull','Missing character:','undefined references','! LaTeX Error'])]
        pdfs.append({'language':lang,'pdf_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'page_count':len(pdf),'pages':rows,'contact_sheets':sheets,'compiler_output_record':re.findall(r'Output written on.*',log),'compiler_warnings':warnings})
    (VIS/'RENDER_INDEX.json').write_text(json.dumps({'status':'RENDERED_NOT_YET_VISUALLY_REVIEWED','pdfs':pdfs},indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'equations':parity['equation_counts'],'math_differences':differences,'codes_equal':parity['lean_code_equal'],'labels_equal':parity['labels_equal'],'pdfs':[{k:v for k,v in r.items() if k not in ('pages','contact_sheets')} for r in pdfs]},ensure_ascii=False,indent=2))

if __name__=='__main__': main()
