"""
package.py — render report PDFs, zip each script folder with SHA-256, build manifest.
Run from the PAPER_I_EXT_AUDIT package root's _lib.
"""
import os, sys, glob, zipfile, hashlib
sys.path.insert(0, os.path.dirname(__file__))
import pdfgen

PKG = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(65536), b""):
            h.update(c)
    return h.hexdigest()

def render_script_reports():
    for md in glob.glob(os.path.join(PKG, "scripts", "*", "report.md")):
        pdf = md[:-3] + ".pdf"
        title = "PAPER_I_EXT_AUDIT — " + os.path.basename(os.path.dirname(md))
        pdfgen.md_to_pdf(open(md, encoding="utf-8").read(), pdf, title)
        print("pdf ->", os.path.relpath(pdf, PKG))

def render_top_reports():
    tops = {"FINAL_AUDIT_REPORT.md": "Paper I — External Adversarial Audit — Final Report",
            "ENVIRONMENT.md": "Paper I External Audit — Environment & Reproducibility"}
    for md, title in tops.items():
        p = os.path.join(PKG, md)
        if os.path.exists(p):
            pdfgen.md_to_pdf(open(p, encoding="utf-8").read(), p[:-3] + ".pdf", title)
            print("pdf ->", md[:-3] + ".pdf")

def zip_scripts():
    for d in sorted(glob.glob(os.path.join(PKG, "scripts", "*"))):
        if not os.path.isdir(d):
            continue
        name = os.path.basename(d)
        zpath = os.path.join(d, name + ".zip")
        if os.path.exists(zpath): os.remove(zpath)
        with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as z:
            for root, dirs, files in os.walk(d):
                dirs[:] = [x for x in dirs if x != "__pycache__"]
                for fn in files:
                    if fn.endswith(".zip") or fn.endswith(".zip.sha256") or fn.endswith(".pyc"):
                        continue
                    fp = os.path.join(root, fn)
                    z.write(fp, os.path.relpath(fp, d))
        digest = sha256(zpath)
        with open(zpath + ".sha256", "w", newline="\n") as f:
            f.write(f"{digest}  {name}.zip\n")
        print("zip ->", os.path.relpath(zpath, PKG), digest[:16], "...")

def manifest():
    out = os.path.join(PKG, "SHA256_MANIFEST.txt")
    with open(out, "w", newline="\n") as f:
        for root, dirs, files in os.walk(PKG):
            dirs[:] = [x for x in dirs if x != "__pycache__"]
            for fn in sorted(files):
                if fn.endswith(".pyc"): continue
                fp = os.path.join(root, fn)
                rel = os.path.relpath(fp, PKG).replace("\\", "/")
                if rel == "SHA256_MANIFEST.txt": continue
                f.write(f"{sha256(fp)}  {rel}\n")
    print("wrote SHA256_MANIFEST.txt")

if __name__ == "__main__":
    render_script_r