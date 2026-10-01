"""Presentation-only treatment of bare Lean identifiers outside protected spans."""
import re

def literal_lean(m):
    """Retain actual Unicode binders and all indentation, not brace lookalikes."""
    escape={'_':r'\_', '{':r'\{', '}':r'\}', '#':r'\#', '%':r'\%', '&':r'\&', '\\':r'\textbackslash{}'}
    lines=[]
    for line in m[1].strip('\n').splitlines():
        chunks=[]
        for token in re.findall(r' +|[^ ]',line):
            if token.isspace(): chunks.append(r'\hspace*{\dimexpr '+str(len(token))+r'\LeanCharWidth\relax}')
            elif ord(token)>127: chunks.append(r'{\LeanSymbols '+token+'}')
            else: chunks.append(escape.get(token,token))
        lines.append(r'\noindent '+(''.join(chunks) or r'\strut')+r'\par')
    return '\n'+r'\Needspace{'+str(len(lines)+2)+r'\baselineskip}'+ '\n'+r'\begin{quote}\fontsize{8.5}{10.2}\selectfont\ttfamily\raggedright\setlength{\parskip}{0pt}\settowidth{\LeanCharWidth}{0}'+'\n'+'\n'.join(lines)+'\n'+r'\end{quote}'+'\n'
def mark_identifiers(text):
    fence=chr(96)
    pattern=(r"\\\[.*?\\\]|\\\(.*?\\\)|"+fence*3+r".*?"+fence*3+
             "|"+fence+r"[^"+fence+r"]+"+fence+r"|<https?://[^>]+>|!\[.*?\]\([^)]+\)")
    pieces=re.split("("+pattern+")",text,flags=re.S)
    for i in range(0,len(pieces),2):
        pieces[i]=re.sub(r"(?<![\w/])([A-Za-z][A-Za-z0-9]*(?:[._][A-Za-z0-9]+)+)(?![\w/])",
            lambda m:fence+m[0]+fence if "_" in m[0] or ("." in m[0] and len(m[0])>20) else m[0],pieces[i])
    return "".join(pieces)
