"""
Orchestrator: for each audit block, generate the PDF certificate, compute SHA-256 of the
results file, zip the whole block folder, and write the block zip's SHA-256.

Run from INTERNAL_AUDIT/ after each block's verify_*.py has produced its results file.
"""
import hashlib
import os
import sys
import zipfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "common"))
from make_certificate import build as build_cert  # noqa: E402


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


BLOCKS = [
    dict(
        dir="block01_algebraic_identities",
        block_id="Block 01 — Algebraic identities (symbolic, exact)",
        results="identities_results.txt",
        title=("Symbolic (SymPy) exact proof of the closed-form algebraic identities the "
               "paper's audit relies on: T(G) key identity (Thm 4.2), (9.12)/(9.20) "
               "coefficients, (9.19) completed square and bound, delta>=7/8 for both "
               "parities (9.10), corridor threshold p=2304, mu breakpoint continuity, and "
               "the (4.5) closed forms."),
        summary=[
            "- 12/12 identity checks PASS (simplify(LHS-RHS)=0 or exact rational / SOS).",
            "- All checks symbolic over Q[p,q,d,s,rho,alpha]; no floating point.",
        ],
        verdict="PASS (12/12 identities)",
    ),
    dict(
        dir="block02_common_profile_LP",
        block_id="Block 02 — Common-profile LP: nu3*(H(p,q,d)) = F(p,q,d) (Thm 3.1)",
        results="common_profile_LP_results.txt",
        title=("Direct fractional triangle-packing LP on the actual graph H(p,q,d) (SciPy "
               "HiGHS) compared against the closed form F(p,q,d), over the grid 3<=p<=8, "
               "0<=q<=8, 0<=d<=p."),
        summary=[
            "- (LP) 351/351: direct-graph HiGHS packing LP optimum equals closed form F.",
            "- (EXACT) 351/351: exact-rational feasible-cover certificate nu3* <= F.",
            "- Maximum |LP - F| over the grid = 3.9e-14; exact cover removes float reliance.",
        ],
        verdict="PASS (LP 351/351, EXACT 351/351)",
    ),
    dict(
        dir="block03_unified_margin",
        block_id="Block 03 — Unified fractional margin (Thm 4.2 / E-4.2)",
        results="margin_results.txt",
        title=("Exact-rational grid audit of the completion-of-squares inequality (4.5) "
               "F(p,q,d) >= q*d/2 + (C_alpha+mu(alpha))*p^2 - p/2 over 3<=p<=48, 1<=q<=2p, "
               "0<=d<=p, plus third-branch dominance bookkeeping."),
        summary=[
            "- 78,384/78,384 exact-rational margin checks PASS.",
            "- Third (hot-neighbourhood) branch co-minimises in 36,317 cases and never",
            "  violates the margin.",
        ],
        verdict="PASS (78,384/78,384 checks)",
    ),
    dict(
        dir="block04_corridor_ILP",
        block_id="Block 04 — Corridor integral packing (Lemma 5.1 & Cor 5.3)",
        results="corridor_ILP_results.txt",
        title=("Exact 0/1 ILP (PuLP/CBC) computation of nu3(G) on 372 systematically "
               "generated split graphs, verifying E-5.1 (nu3 >= (1/q) sum C(d_i,2)) and "
               "Corollary 5.3 (Phi <= n^2/6 + p/2 + (s^2-6s+3)/12) on the applicable "
               "instances, plus basic invariants."),
        summary=[
            "- 372/372 instances satisfy 0<=Phi and 3*nu3<=|E| (CBC optimality verified).",
            "- E-5.1: 180/180 applicable instances PASS.",
            "- Corollary 5.3: 180/180 applicable instances PASS.",
        ],
        verdict="PASS (E-5.1 180/180, Cor5.3 180/180, basic 372/372)",
    ),
]

HERE = os.path.dirname(os.path.abspath(__file__))
manifest = []

for blk in BLOCKS:
    bdir = os.path.join(HERE, blk["dir"])
    results_path = os.path.join(bdir, "results", blk["results"])
    results_sha = sha256_file(results_path)
    # certificate
    num = blk["dir"].split("_")[0]  # blockNN
    pdf_path = os.path.join(bdir, f"certificate_{num}.pdf")
    build_cert(pdf_path, blk["block_id"], blk["title"], blk["results"],
               blk["verdict"], results_sha, blk["summary"])
    # zip the block folder (relative paths inside)
    zip_path = os.path.join(HERE, blk["dir"] + ".zip")
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for root, _, files in os.walk(bdir):
            for fn in files:
                if fn.endswith(".zip"):
                    continue
                full = os.path.join(root, fn)
                arc = os.path.relpath(full, HERE)
                zf.write(full, arc)
    zip_sha = sha256_file(zip_path)
    with open(zip_path + ".sha256", "w", encoding="utf-8") as f:
        f.write(f"{zip_sha}  {blk['dir']}.zip\n")
    manifest.append((blk["dir"], blk["verdict"], results_sha, zip_sha))
    print(f"[ok] {blk['dir']}: cert + zip + sha written")

# top-level manifest
with open(os.path.join(HERE, "SHA256_MANIFEST.txt"), "w", encoding="utf-8") as f:
    f.write("Paper III — INTERNAL_AUDIT — SHA-256 manifest\n")
    f.write("=" * 60 + "\n\n")
    for d, verdict, rsha, zsha in manifest:
        f.write(f"{d}\n")
        f.write(f"    verdict         : {verdict}\n")
        f.write(f"    results SHA-256 : {rsha}\n")
        f.write(f"    zip SHA-256     : {zsha}\n\n")
print("wrote SHA256_MANIFEST.txt")
