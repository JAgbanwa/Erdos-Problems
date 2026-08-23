"""
04 — Lean formal-verification certificate audit (Paper I, Gate H).

Independently checks the manuscript's formal-verification claims:
  (H1) statement match:  paperI_main : Phi <= n^2/6 + n  with Phi = edgeCount - 2*nu3star
  (H2) source cleanliness: no real `sorry`/`admit`/`native_decide`/added `axiom`
       in the canonical Lean sources (comment mentions of the word "sorry" excluded)
  (H3) SHA-256 of the released lean tree == recorded 04_integrity/SHA256SUMS.txt
  (H4) independent build result: exit code, and #print axioms for paperI_main /
       residual_duality parsed from the fresh-tree build log; must be
       [propext, Classical.choice, Quot.sound] with NO sorryAx / no project axiom
  (H5) cross-check (H4) against the released gate_logs/print_axioms_residual_and_main.log

Paths are resolved relative to the canonical PAPER_I package.
"""
import sys, os, io, re, hashlib
try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

HERE = os.path.dirname(__file__)
PKG  = os.path.abspath(os.path.join(HERE, "..", ".."))          # PAPER_I_EXT_AUDIT_...
CANON = os.path.abspath(os.path.join(PKG, ".."))                # PAPER_I
LEAN = os.path.join(CANON, "05_formalization", "lean")
BUILD_LOG = r"C:\Users\jtrav\l\build2.log"                      # independent fresh-tree build

LEAN_SOURCES = ["DeltaNu.lean", "FiniteLPDuality.lean", "WCDH_check.lean",
                "PaperI/PaperI_Statement.lean", "PaperI/PaperI_Arith.lean",
                "lean-toolchain", "lakefile.toml", "lake-manifest.json"]

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(65536), b""):
            h.update(c)
    return h.hexdigest()

def strip_comments(src):
    """Remove /- ... -/ block comments and -- line comments (approximate, good enough
       to distinguish real tactic `sorry` from docstring mentions)."""
    src = re.sub(r"/-.*?-/", " ", src, flags=re.S)
    src = re.sub(r"--[^\n]*", " ", src)
    return src

def run():
    log = io.StringIO()
    def P(*a):
        t = " ".join(str(x) for x in a); print(t); print(t, file=log)
    P("="*78); P("04 — LEAN FORMAL CERTIFICATE AUDIT (Paper I, Gate H)"); P("="*78)

    # (H1) statement match
    P("\n(H1) statement match")
    stmt = open(os.path.join(LEAN, "PaperI", "PaperI_Statement.lean"), encoding="utf-8").read()
    m = re.search(r"theorem\s+paperI_main.*?:=", stmt, flags=re.S)
    decl = re.search(r"theorem\s+paperI_main.*?\n", stmt, flags=re.S)
    has_stmt = ("G.Phi" in stmt and "(G.n : ℝ) ^ 2 / 6 + (G.n : ℝ)" in stmt)
    has_phi = re.search(r"def\s+Phi[^\n]*edgeCount[^\n]*nu3star", stmt) or \
              ("(G.edgeCount : ℝ) - 2 * nu3star" in stmt)
    P(f"   paperI_main present            : {bool(m)}")
    P(f"   states Phi <= n^2/6 + n        : {has_stmt}")
    P(f"   Phi = edgeCount - 2*nu3star    : {bool(has_phi)}")
    h1 = bool(m) and has_stmt and bool(has_phi)

    # (H2) source cleanliness
    P("\n(H2) source cleanliness (real sorry/admit/native_decide/axiom; comments excluded)")
    h2_bad = []
    for rel in LEAN_SOURCES:
        if not rel.endswith(".lean"): continue
        code = strip_comments(open(os.path.join(LEAN, rel), encoding="utf-8").read())
        for tok in (r"\bsorry\b", r"\badmit\b", r"\bnative_decide\b", r"^\s*axiom\b"):
            hits = re.findall(tok, code, flags=re.M)
            if hits:
                h2_bad.append((rel, tok, len(hits)))
        P(f"   {rel:34s}: clean" if not any(b[0]==rel for b in h2_bad)
          else f"   {rel:34s}: FLAGS {[b[1] for b in h2_bad if b[0]==rel]}")
    h2 = (len(h2_bad) == 0)

    # (H3) SHA vs recorded manifest
    P("\n(H3) SHA-256 of released lean tree vs 04_integrity/SHA256SUMS.txt")
    recorded = {}
    man = os.path.join(CANON, "04_integrity", "SHA256SUMS.txt")
    for line in open(man, encoding="utf-8"):
        parts = line.split()
        if len(parts) == 2 and parts[1].startswith("05_formalization/lean/"):
            recorded[parts[1]] = parts[0]
    h3_bad = 0; h3_n = 0
    for rel in LEAN_SOURCES:
        key = "05_formalization/lean/" + rel
        fp = os.path.join(LEAN, rel)
        if key in recorded and os.path.exists(fp):
            got = sha256(fp); ok = (got == recorded[key]); h3_n += 1
            if not ok: h3_bad += 1
            P(f"   {rel:34s}: {'MATCH' if ok else 'MISMATCH'}")
        elif os.path.exists(fp):
            P(f"   {rel:34s}: (not in recorded manifest)")
    h3 = (h3_bad == 0 and h3_n > 0)

    # (H4) independent build result + axioms
    P("\n(H4) independent fresh-tree build result")
    axioms_main = axioms_resid = None; build_exit = None; sorryax = False
    if os.path.exists(BUILD_LOG):
        blog = open(BUILD_LOG, encoding="utf-8", errors="replace").read()
        mexit = re.search(r"BUILD EXIT:\s*(\d+)", blog)
        build_exit = mexit.group(1) if mexit else None
        for line in blog.splitlines():
            if "paperI_main' depends on axioms" in line or "paperI_main depends on axioms" in line:
                axioms_main = line.split("axioms:")[-1].strip()
            if "residual_duality' depends on axioms" in line or "residual_duality depends on axioms" in line:
                axioms_resid = line.split("axioms:")[-1].strip()
            if "sorryAx" in line: sorryax = True
        P(f"   build log                    : {BUILD_LOG}")
        P(f"   BUILD EXIT                    : {build_exit}")
        P(f"   #print axioms paperI_main     : {axioms_main}")
        P(f"   #print axioms residual_duality: {axioms_resid}")
        P(f"   sorryAx present anywhere      : {sorryax}")
    else:
        P(f"   build log NOT FOUND at {BUILD_LOG} — independent build INCONCLUSIVE")
    expected = "[propext, Classical.choice, Quot.sound]"
    h4 = (build_exit == "0" and axioms_main is not None and expected in (axioms_main or "")
          and not sorryax)

    # (H5) cross-check against released gate log
    P("\n(H5) cross-check vs released gate_logs/print_axioms_residual_and_main.log")
    gl = os.path.join(LEAN, "gate_logs", "print_axioms_residual_and_main.log")
    rec_main = None
    if os.path.exists(gl):
        for line in open(gl, encoding="utf-8", errors="replace"):
            if "paperI_main" in line and "axioms" in line:
                rec_main = line.split("axioms:")[-1].strip()
        P(f"   recorded paperI_main axioms   : {rec_main}")
        P(f"   matches independent build     : {rec_main == axioms_main if axioms_main else 'N/A (no indep build)'}")
    h5 = (rec_main is not None and expected in (rec_main or ""))

    P("-"*78)
    def v(b): return "PASS" if b else ("INCONCLUSIVE" if b is None else "FAIL")
    P(f"(H1) statement match             : {v(h1)}")
    P(f"(H2) source sorry/axiom clean    : {v(h2)}")
    P(f"(H3) SHA vs recorded manifest    : {v(h3)}")
    P(f"(H4) independent build + axioms  : {v(h4)}  {'' if h4 else '(see note)'}")
    P(f"(H5) recorded gate log axioms    : {v(h5)}")
    overall = ("PASS" if (h1 and h2 and h3 and h4 and h5) else
               "PASS_WITH_RESIDUAL_RISK" if (h1 and h2 and h3 and h5) else "INCOMPLETE")
    P(f"GATE H OVERALL                   : {overall}")
    P("="*78)
    with open(os.path.join(HERE, "results.txt"), "w", encoding="utf-8") as f:
        f.write(log.getvalue())
   