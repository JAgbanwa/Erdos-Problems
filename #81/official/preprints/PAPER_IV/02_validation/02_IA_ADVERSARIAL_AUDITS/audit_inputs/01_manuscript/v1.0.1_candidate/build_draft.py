"""Conversión reproducible del MD mediante el estilo local y figuras vectoriales."""
from pathlib import Path
import hashlib
import re
import subprocess
import sys
import unicodedata

ROOT = Path(__file__).resolve().parent
TOOLS = Path(r'C:\Users\jtraverso\.cache\e81-editorial-tools')
sys.path.insert(0, str(TOOLS / 'python-libs'))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
import fitz
from PIL import Image, ImageOps, ImageDraw

STEM = 'PAPER_IV_preprint_v1.0.1_es'
PANDOC = TOOLS / 'pandoc/pandoc-3.11/pandoc.exe'
TECTONIC = TOOLS / 'tectonic/tectonic.exe'

def figures():
    directory = ROOT / 'figures'
    directory.mkdir(exist_ok=True)
    plt.rcParams.update({'font.family': 'DejaVu Serif', 'font.size': 11})
    def box(ax,x,y,w,h,label,face='#f4f6f8',edge='#314659',fs=10):
        ax.add_patch(FancyBboxPatch((x-w/2,y-h/2),w,h,
            boxstyle='round,pad=0.06',facecolor=face,edgecolor=edge,lw=1.05))
        ax.text(x,y,label,ha='center',va='center',fontsize=fs)
    def arrow(ax,a,b,color='#314659'):
        ax.annotate('',xy=b,xytext=a,arrowprops={'arrowstyle':'->','color':color,'lw':1.15})

    # Figure 1: same accounting condition, two distinct mechanisms.
    fig, ax = plt.subplots(figsize=(7.0, 5.0))
    ax.set(xlim=(0, 12), ylim=(0, 8)); ax.axis('off')
    ax.text(3,7.7,'Preprint [5]',ha='center',va='center',
            fontsize=11,fontweight='bold',color='#7b3f24')
    ax.text(9,7.7,'Esta investigación',ha='center',va='center',
            fontsize=11,fontweight='bold',color='#244d70')
    for x,col,face in [(3,'#9a5b36','#fbf2ec'),(9,'#315f83','#edf4fa')]:
        box(ax,x,6.75,4.8,.65,'Grafo cordal grande: dos casos',face=face,edge=col,fs=10)
    labels=[(1.55,'Con holgura\nTransferencia\nsubcuadrática','#9a5b36','#fbf2ec'),
            (4.45,'Crítico\nPrimera entrada\ny estabilización','#9a5b36','#fbf2ec'),
            (7.55,'Rama L · §3\nRedondeo mixto\nRC01','#315f83','#edf4fa'),
            (10.45,'Rama C · §§4–5\nDescenso\ny H1/RD09','#315f83','#edf4fa')]
    for x,label,col,face in labels:
        box(ax,x,4.95,2.6,1.28,label,face=face,edge=col,fs=9.7)
        parent=3 if x<6 else 9
        arrow(ax,(parent,6.35),(x,5.65),col)
        arrow(ax,(x,4.25),(parent,3.6),col)
    for x,col,face in [(3,'#9a5b36','#fff9f5'),(9,'#315f83','#f5faff')]:
        box(ax,x,3.1,5.0,.9,'Partición del grafo original\n'+r'$e(G)-g(\mathcal{P})\leq M(n)$',face=face,edge=col,fs=10.5)
        arrow(ax,(x,2.58),(5 if x==3 else 7,1.87),col)
    box(ax,6,1.05,10.2,1.4,'Las dos construcciones satisfacen (1.3)\n'+
        r'$W^*(G)-g(\mathcal{P})\leq M(n)-F_4(G)$'+'\n'+
        r'Pérdida de ganancia $\leq$ margen disponible',face='#edf3ed',edge='#3e6a46',fs=11)
    fig.tight_layout(pad=.25)
    for ext in ('pdf','png'): fig.savefig(directory / ('fig1_presupuesto_comparado.'+ext),dpi=180)
    plt.close(fig)

    # Figure 2: one proof, two refinements.
    fig, ax = plt.subplots(figsize=(7.0, 5.2))
    ax.set(xlim=(0, 12),ylim=(0, 11)); ax.axis('off')
    box(ax,6,10.1,5.2,.85,'Modelo y óptimo certificado · §2',face='#eaf0f5',fs=10.5)
    box(ax,3.0,8.25,4.6,1.25,'Rama L: hay margen\nTeorema 3.1: redondeo RC01\nCorolario 3.5: paga la pérdida',face='#edf4fa',edge='#315f83',fs=10)
    box(ax,9.0,8.25,4.6,1.25,'Rama C: valor crítico\nProposición 4.3: localización\nTeorema 5.0: construcción',face='#edf4fa',edge='#315f83',fs=10)
    box(ax,6,5.9,6.5,.85,r'Teorema B · §6: $c_4(G)\leq M(n)$ eventualmente',face='#edf3ed',edge='#3e6a46',fs=10.5)
    box(ax,6,4.4,6.5,.85,r'Teorema A · §6.3: $c_4(G)\leq M(n)+b$ para todo $n$',face='#edf3ed',edge='#3e6a46',fs=10.5)
    for a,b in [((4.7,9.64),(3,8.95)),((7.3,9.64),(9,8.95)),
                ((3,7.57),(4.7,6.4)),((9,7.57),(7.3,6.4)),((6,5.43),(6,4.88))]:
        arrow(ax,a,b)
    box(ax,3,1.65,5.05,1.65,'Puente de modelos · §7.2\nConserva recursos y ganancias\nActúa sobre el modelo de §2',face='#f6f1fa',edge='#6e4b83',fs=10)
    box(ax,9,1.65,5.05,1.65,'Refinamiento híbrido · §5.4\nConserva el testigo de la rama C\nEstabilidad y clasificación · §6.5',face='#f6f1fa',edge='#6e4b83',fs=10)
    ax.text(6,3.15,'REFINAMIENTOS DE LA MISMA DEMOSTRACIÓN',ha='center',va='center',fontsize=9,color='#6e4b83')
    # Outer dashed connectors indicate retained data/representation, not proof dependencies.
    for coords in [[(3.32,10.1),(.28,10.1),(.28,1.65),(.41,1.65)],
                   [(11.37,8.25),(11.74,8.25),(11.74,1.65),(11.59,1.65)]]:
        for a,b in zip(coords[:-2],coords[1:-1]):
            ax.plot([a[0],b[0]],[a[1],b[1]],color='#6e4b83',ls='--',lw=1.1)
        ax.annotate('',xy=coords[-1],xytext=coords[-2],arrowprops={'arrowstyle':'->','color':'#6e4b83','lw':1.1,'linestyle':'--'})
    fig.tight_layout(pad=.2)
    for ext in ('pdf','png'): fig.savefig(directory / ('fig2_prueba_y_variantes.'+ext),dpi=180)
    plt.close(fig)

    # Figure 3: physical host realization.
    fig, ax = plt.subplots(figsize=(7.5,2.5))
    ax.set(xlim=(-.6,5.6),ylim=(-.45,2.4)); ax.axis('off')
    pts={'u₁':(0,0),'v₁':(1.5,0),'u₂':(3.5,0),'v₂':(5,0),'z':(2.5,2)}
    for left,right,col in [('u₁','v₁','#284e72'),('u₂','v₂','#965622')]:
        for a,b in [(left,right),(left,'z'),(right,'z')]:
            ax.plot([pts[a][0],pts[b][0]],[pts[a][1],pts[b][1]],color=col,lw=2)
    for name,(x,y) in pts.items():
        ax.scatter(x,y,s=90,c='white',edgecolors='#111111',zorder=3)
        ax.text(x,y+(.23 if name=='z' else -.24),name,ha='center',va='center',fontsize=13)
    fig.tight_layout(pad=.1)
    for ext in ('pdf','png'): fig.savefig(directory / ('fig3_anfitrion.'+ext),dpi=180)
    plt.close(fig)

def convert():
    source = (ROOT / (STEM+'.md')).read_text(encoding='utf-8')
    assert not any(ord(c)<32 and c not in '\n\r' for c in source)
    body = source[source.index('**Paper IV de la serie**'):]
    # Keep short comparison tables with their captions; the long source map may span pages.
    def reserve_table(m):
        lines=m[0].strip().splitlines()
        if len(lines)<=10:
            return '\\Needspace{'+str(2*len(lines)+6)+'\\baselineskip}\n\n'+m[0]
        return m[0]
    body = re.sub(r'(?m)(?:^\|[^\n]*\|\n)+', reserve_table, body)
    def replace_figure(m):
        caption, stem = m.groups()
        return '\n\\begin{figure}[H]\n\\centering\n' + \
            '\\includegraphics[width=.95\\linewidth]{figures/'+stem+'.pdf}\n' + \
            '\\caption{'+caption+'}\n\\end{figure}\n'
    body = re.sub(r'!\[(.*?)\]\(figures/([^\)]+)\.png\)', replace_figure, body)
    # Literal Lean is retained in Markdown; typeset its Unicode using math glyphs.
    symbols = {'∀':r'\(\forall\)', '∃':r'\(\exists\)', '→':r'\(\to\)',
               '≤':r'\(\le\)', '∧':r'\(\land\)', '∈':r'\(\in\)',
               '∉':r'\(\notin\)', '≠':r'\(\ne\)', '¬':r'\(\neg\)',
               'ℕ':r'\(\mathbb N\)', 'ℚ':r'\(\mathbb Q\)',
               '⦃':r'\(\{\!\{\)', '⦄':r'\(\}\!\}\)'}
    def lean_block(m):
        lines=[]
        for line in m[1].strip('\n').splitlines():
            chunks=[]
            for ch in line:
                chunks.append(symbols.get(ch, {'_':r'\_', '{':r'\{', '}':r'\}',
                    '#':r'\#', '%':r'\%', '&':r'\&', '\\':r'\textbackslash{}'}.get(ch,ch)))
            lines.append(''.join(chunks) + r'\par')
        return '\n\\begin{quote}\\footnotesize\\ttfamily\\raggedright\n'+'\n'.join(lines)+'\n\\end{quote}\n'
    body = re.sub(r'```lean\n(.*?)\n```', lean_block, body, flags=re.S)
    # A heading immediately followed by a result must travel with that result.
    body = re.sub(r'(?m)^(### [^\n]+\n\n)(?=\*\*(?:Lema|Teorema|Proposición|Corolario))',
                  lambda m: '\\Needspace{14\\baselineskip}\n\n'+m[1], body)
    # Keep the introductory lines of a numbered result with its statement.
    body = re.sub(r'(?m)^(\*\*(?:Lema|Proposición|Teorema|Corolario) [0-9])',
                  lambda m: '\\Needspace{9\\baselineskip}\n\n'+m[1], body)
    proc = subprocess.run([str(PANDOC),'-f','markdown+tex_math_single_backslash+raw_tex',
        '-t','latex','--wrap=none'],input=body,text=True,encoding='utf-8',capture_output=True,check=True)
    # Pandoc encodes accented characters in autogenerated section labels as uxxx.
    # Decode and transliterate the labels, leaving the printed Spanish headings intact.
    def ascii_label(m):
        decoded = re.sub(r'ux([0-9a-fA-F]{2})',
            lambda code: chr(int(code[1], 16)), m[1])
        return r'\label{' + unicodedata.normalize('NFKD', decoded).encode('ascii', 'ignore').decode() + '}'
    latex_body = re.sub(r'\\label\{([^}]+)\}', ascii_label, proc.stdout)
    latex_body = latex_body.replace('\\subsection{Referencias}', '\\clearpage\n\\subsection{Referencias}\n\\begingroup\\small\\setlength{\\parskip}{4pt}')
    latex_body = latex_body.replace('{[}10{]} L. de Moura', '\\clearpage\n{[}10{]} L. de Moura')
    latex_body += '\n\\endgroup\n'
    # Pandoc explicitly writes [l] for longtable; center each table in the text block.
    latex_body = latex_body.replace('\\begin{longtable}[]{', '\\begin{longtable}[c]{')
    latex_body = latex_body.replace('\\begin{longtable}[l]{', '\\begin{longtable}[c]{')
    # Preserve literal identifiers in mono; every permitted break has a visible marker.
    def inline_code(m):
        token = m[1].replace(r'\_', '_')
        if re.fullmatch(r'[A-Za-z0-9_.-]+', token):
            rendered = []
            run = 0
            for i, ch in enumerate(token):
                rendered.append(r'\_' if ch == '_' else ch)
                run += 1
                if i + 1 < len(token) and (ch in '._-' or run >= 12):
                    rendered.append(r'\discretionary{\hbox{\ensuremath{\hookrightarrow}}}{}{}')
                    run = 0
            return r'{\ttfamily\small ' + ''.join(rendered) + '}'
        return m[0] if r'\ ' in m[1] else r'\nolinkurl{' + token + '}'
    latex_body = re.sub(r'\\texttt\{([^{}]+)\}', inline_code, latex_body)
    # This path may break at its slash, never inside the directory name.
    latex_body = latex_body.replace(r'\nolinkurl{contrib/CliqueTreeExtraction}',
        r'\mbox{contrib/}\allowbreak\mbox{CliqueTreeExtraction}')
    tex = (ROOT/'series_template.tex').read_text(encoding='utf-8').replace('% BODY',latex_body)
    (ROOT/(STEM+'.tex')).write_text(tex,encoding='utf-8')

def compile_pdf():
    proc = subprocess.run([str(TECTONIC),'--keep-logs','--keep-intermediates','--reruns','1',
        '--outdir',str(ROOT),str(ROOT/(STEM+'.tex'))],cwd=ROOT,
        text=True,encoding='utf-8',errors='replace',capture_output=True)
    (ROOT/'compiler_console.log').write_text(proc.stdout+'\n'+proc.stderr,encoding='utf-8')
    print(proc.stdout[-3500:]); print(proc.stderr[-3500:])
    proc.check_returncode()

def render():
    out=ROOT/'qa_es'; out.mkdir(parents=True,exist_ok=True)
    doc=fitz.open(ROOT/(STEM+'.pdf'))
    pages=[]
    for i,page in enumerate(doc):
        dest=out/f'page_{i+1:02d}.png'
        page.get_pixmap(matrix=fitz.Matrix(1.45,1.45)).save(dest)
        pages.append(dest)
    for offset in range(0,len(pages),6):
        sheet=Image.new('RGB',(1000,1470),'#d9d9d9'); d=ImageDraw.Draw(sheet)
        for j,p in enumerate(pages[offset:offset+6]):
            im=Image.open(p); im.thumbnail((480,450))
            x=(j%2)*500+(500-im.width)//2; y=(j//2)*490+25
            sheet.paste(im,(x,y)); d.text(((j%2)*500+15,(j//2)*490+6),f'Página {offset+j+1}',fill='black')
        sheet.save(out/f'contact_{offset//6+1}.png')
    texts='\n'.join(page.get_text() for page in doc)
    (out/'pdf_text.txt').write_text(texts,encoding='utf-8')
    meta={'pages':len(doc),'figures':texts.count('Figura '), 'google_absent':not re.search(r'Gemini|Google',texts),
          'harmonic_present':'Harmonic' in texts,'aristotle_present':'Aristotle' in texts}
    print(meta)
    (out/'pdf_sha256.txt').write_text(hashlib.sha256((ROOT/(STEM+'.pdf')).read_bytes()).hexdigest(),encoding='utf-8')

if __name__=='__main__':
    if '--render-only' in sys.argv: render()
    else: convert(); compile_pdf(); render()
