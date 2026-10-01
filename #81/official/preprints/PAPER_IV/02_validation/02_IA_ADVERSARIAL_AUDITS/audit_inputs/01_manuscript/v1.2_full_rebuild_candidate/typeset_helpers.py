"""Presentation-only treatment of bare Lean identifiers outside protected spans."""
import re
def mark_identifiers(text):
    fence=chr(96)
    pattern=(r"\\\[.*?\\\]|\\\(.*?\\\)|"+fence*3+r".*?"+fence*3+
             "|"+fence+r"[^"+fence+r"]+"+fence+r"|<https?://[^>]+>|!\[.*?\]\([^)]+\)")
    pieces=re.split("("+pattern+")",text,flags=re.S)
    for i in range(0,len(pieces),2):
        pieces[i]=re.sub(r"(?<![\w/])([A-Za-z][A-Za-z0-9]*(?:[._][A-Za-z0-9]+)+)(?![\w/])",
            lambda m:fence+m[0]+fence if "_" in m[0] or ("." in m[0] and len(m[0])>20) else m[0],pieces[i])
    return "".join(pieces)
