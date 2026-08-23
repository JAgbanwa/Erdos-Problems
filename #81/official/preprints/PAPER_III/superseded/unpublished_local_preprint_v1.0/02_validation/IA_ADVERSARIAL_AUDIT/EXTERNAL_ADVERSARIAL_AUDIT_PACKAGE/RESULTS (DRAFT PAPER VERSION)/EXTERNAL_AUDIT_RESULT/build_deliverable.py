r"""
EXTERNAL ADVERSARIAL AUDIT — deliverable builder.

Generates: per-block one-page PDF certificates, per-block zips + .sha256,
findings/FINDINGS.csv is expected to exist already, ADVERSARIAL_AUDIT_REPORT.pdf
from the .md, and the top-level SHA256_MANIFEST.txt.

Run AFTER all block scripts have produced their results/ files.
"""
import os, sys, hashlib, zipfile, datetime

HERE = os.path.dirname(os.path.abspath(__file__))

BLOCKS = {
    'blockA_faithfulness': dict(
        title='Block A — Paper-Ledger Faithfulness & Internal Consistency',
        verdict='PASS_WITH_OBSERVATIONS',
        scope=('A1 verbatim-equivalence of all 18 LEDGER nodes vs manuscript v0.9.5; '
               'A2 dependency-DAG reconstruction from the proofs (acyclicity, Section 9 '
               'assembly hygiene); A3 census of external inputs incl. Appendix D '
               'self-containment.'),
        evidence=('35/35 statement anchors present; per-node comparison table: no '
                  'statement-level discrepancy; DAG acyclic, matches ledger; AX usage '
                  'localized as claimed. FINDING A-1 (minor): strongest self-containment '
                  'phrasings overstate (classical Dirac / Turan / chi-prime(K_t) also used). '
                  '3 presentational observations.'),
        results_file='results/blockA_census_results.txt'),
    'blockB_external_inputs': dict(
        title='Block B — External Inputs AX1/AX2 vs Literature',
        verdict='PASS',
        scope=('B1 AX1 (Haxell-Rodl/Yuster) faithfulness and not-stronger check; '
               'B2 AX2 (Dross + Barber-Kuhn-Lo-Osthus) threshold and divisibility; '
               'B3 usage localization (bulk / sparse only; Prop 10.1 uses neither).'),
        evidence=('AX1 is the K3 instance of the published theorem (verbatim in Yuster '
                  'arXiv:math/0305350 abstract, attributing fixed-graph case to Haxell-Rodl); '
                  'AX2 appears verbatim in Dross arXiv:1503.08191 abstract ((0.9+eps)n, '
                  'triangle-divisible). Citation metadata verified. Usage census confirms '
                  'localization. Coverage: paywalled journal texts verified at abstract level.'),
        results_file='results/blockB_literature_verification.md'),
    'blockC_counterexample_search': dict(
        title='Block C — Adversarial Counterexample Search (Finite / Closed-Form Claims)',
        verdict='PASS',
        scope=('C1 nu3*(H(p,q,d))=F by exact rational sandwich certificates + raw exact '
               'simplex; C2 margin (4.5) integer grid to p=150 + 200k random to p=1e9; '
               'C3 Lemmas 5.1/5.2/7.1 + Cor 5.3 with packing certificates and exact nu3; '
               'C4 Prop 10.1 at true scale incl. p=2304; C5 sharpness family; C6 Appendix B '
               'exhaustive; C7 Lemma 4.1 by exact simplex on arbitrary profiles.'),
        evidence='See results/*.txt — zero violations across ~2.55 million instances.',
        results_file='results/c2_margin_results.txt'),
    'blockD_algebra_rederivation': dict(
        title='Block D — Independent Re-derivation of the Algebra (no CAS)',
        verdict='PASS',
        scope=('All load-bearing identities and inequality chains of Sections 4, 5, 9 and '
               'Appendices A-B, re-proved with a self-written exact polynomial class over '
               'Fraction: T-identity, (4.5) residuals incl. branch-3 completion, (5.2)/(5.3), '
               '(9.5)-(9.20) chains, threshold p=2304, mu continuity, Lemma 6.1 counting, '
               'Lemma 7.1 assembly identity (D23, not displayed in the paper), sharpness.'),
        evidence='38/38 checks PASS (results/algebra_results.txt).',
        results_file='results/algebra_results.txt'),
    'blockE_audit_the_audit': dict(
        title='Block E — Audit of the Internal Audit',
        verdict='PASS_WITH_OBSERVATIONS',
        scope=('E1 re-run of all four internal blocks; E2 adversarial script reading; '
               'E3 boundary stress of their shared formula module and grids.'),
        evidence=('E1: all four blocks reproduce BIT-IDENTICALLY, grid counts re-derived. '
                  'E2: 3 minor script defects (unimplemented advertised check; float '
                  'tolerance; unchecked solver status - fail-safe direction), none '
                  'verdict-affecting. E3: 0 mismatches on 20k+ boundary/random cases.'),
        results_file='results/e3_boundary_results.txt'),
}

def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def make_cert(block, meta):
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.units import cm
    from reportlab.pdfgen import canvas
    bdir = os.path.join(HERE, block)
    letter = block.split('_')[0].replace('block', '').upper()
    out = os.path.join(bdir, f'certificate_block{letter}.pdf')
    c = canvas.Canvas(out, pagesize=A4)
    W, H = A4
    y = H - 2.2*cm
    c.setFont('Helvetica-Bold', 14)
    c.drawString(2*cm, y, 'EXTERNAL ADVERSARIAL AUDIT — CERTIFICATE')
    y -= 0.9*cm
    c.setFont('Helvetica-Bold', 11)
    c.drawString(2*cm, y, meta['title'])
    y -= 0.8*cm
    c.setFont('Helvetica', 9)
    def wrap(text, width=100):
        words = text.split(); lines = []; cur = ''
        for w in words:
            if len(cur) + len(w) + 1 > width: lines.append(cur); cur = w
            else: cur = (cur + ' ' + w).strip()
        if cur: lines.append(cur)
        return lines
    def para(label, text):
        nonlocal y
        c.setFont('Helvetica-Bold', 9); c.drawString(2*cm, y, label); y -= 0.45*cm
        c.setFont('Helvetica', 9)
        for ln in wrap(text):
            c.drawString(2*cm, y, ln); y -= 0.42*cm
        y -= 0.2*cm
    para('Subject:', 'Linear-Error Clique Partitions of Split Graphs (Erdos #81, '
         'Paper III), review version v0.9.5. Lean formalization explicitly OUT of scope.')
    para('Scope of this block:', meta['scope'])
    para('Evidence summary:', meta['evidence'])
    rf = os.path.join(bdir, meta['results_file'])
    rh = sha256(rf) if os.path.exists(rf) else 'MISSING'
    para('Primary results file:', f"{meta['results_file']}  SHA-256: {rh}")
    c.setFont('Helvetica-Bold', 11)
    c.drawString(2*cm, y, f"VERDICT: {meta['verdict']}"); y -= 0.8*cm
    c.setFont('Helvetica', 9)
    c.drawString(2*cm, y, f'Auditor: external adversarial audit agent (Claude, Anthropic '
                 f'model claude-fable-5), independent tooling.'); y -= 0.45*cm
    c.drawString(2*cm, y, f'Date: {datetime.date.today().isoformat()}   '
                 f'Package audited: see received_inputs.sha256'); y -= 0.45*cm
    c.showPage(); c.save()
    return out

def zip_block(block):
    bdir = os.path.join(HERE, block)
    zpath = os.path.join(HERE, f'{block}.zip')
    with zipfile.ZipFile(zpath, 'w', zipfile.ZIP_DEFLATED) as z:
        for dp, _, fns in os.walk(bdir):
            for fn in sorted(fns):
                p = os.path.join(dp, fn)
                z.write(p, os.path.relpath(p, HERE))
    with open(zpath + '.sha256', 'w') as f:
        f.write(sha256(zpath) + '  ' + os.path.basename(zpath) + '\n')

def md_to_pdf(md_path, pdf_path, title):
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.units import cm
    from reportlab.pdfgen import canvas
    text = open(md_path, encoding='utf-8').read()
    c = canvas.Canvas(pdf_path, pagesize=A4)
    W, H = A4
    y = H - 2*cm
    c.setFont('Helvetica-Bold', 13); c.drawString(1.8*cm, y, title); y -= 0.9*cm
    for raw in text.splitlines():
        line = raw.rstrip()
        bold = line.startswith('#')
        line = line.lstrip('#').strip() if bold else line
        font = ('Helvetica-Bold', 10) if bold else ('Helvetica', 8)
        c.setFont(*font)
        maxw = 118 if not bold else 90
        chunks = [line[i:i+maxw] for i in range(0, max(len(line), 1), maxw)] or ['']
        for ch in chunks:
            if y < 1.8*cm:
                c.showPage(); y = H - 2*cm; c.setFont(*font)
            c.drawString(1.8*cm, y, ch)
            y -= 0.40*cm if not bold else 0.55*cm
    c.showPage(); c.save()

def main():
    for block, meta in BLOCKS.items():
        make_cert(block, meta)
        zip_block(block)
        print('certified+zipped', block)
    # High-quality report PDF via the dedicated platypus renderer (Arial/Consolas,
    # proper tables). Fall back to the crude renderer only if it is unavailable.
    rep_md = os.path.join(HERE, 'ADVERSARIAL_AUDIT_REPORT.md')
    if os.path.exists(rep_md):
        try:
            import make_report_pdf
            make_report_pdf.main()
        except Exception as e:
            print('platypus renderer failed, using fallback:', e)
            md_to_pdf(rep_md, os.path.join(HERE, 'ADVERSARIAL_AUDIT_REPORT.pdf'),
                      'External Adversarial Audit Report — Paper III (v0.9.5)')
        print('report pdf written')
    # manifest last
    lines = []
    for dp, _, fns in os.walk(HERE):
        for fn in sorted(fns):
            if fn == 'SHA256_MANIFEST.txt': continue
            p = os.path.join(dp, fn)
            lines.append(f'{sha256(p)}  {os.path.relpath(p, HERE).replace(os.sep, "/")}')
    lines.sort(key=lambda l: l.split('  ', 1)[1])
    with open(os.path.join(HERE, 'SHA256_MANIFEST.txt'), 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines) + '\n')
    print(f'manifest: {len(lines)} files')

if __name__ == '__main__':
    main()
