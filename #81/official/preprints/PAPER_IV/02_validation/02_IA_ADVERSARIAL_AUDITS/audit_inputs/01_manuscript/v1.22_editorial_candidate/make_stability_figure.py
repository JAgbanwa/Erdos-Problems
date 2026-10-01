"""Figure 4: schematic proof dependencies, not an additional theorem."""
from pathlib import Path
import sys
sys.path.insert(0, 'C:/Users/jtraverso/.cache/e81-editorial-tools/python-libs')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'figures_en'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'pdf.fonttype':42,'ps.fonttype':42,'font.family': 'DejaVu Serif', 'font.size': 11})
fig, ax = plt.subplots(figsize=(10, 7.5))
ax.set(xlim=(0, 10), ylim=(0, 8))
ax.axis('off')

def box(x, y, w, h, label, fill='#edf2f7', edge='#244c70'):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle='round,pad=0.08',
                              linewidth=1.1, edgecolor=edge, facecolor=fill))
    ax.text(x+w/2, y+h/2, label, ha='center', va='center', linespacing=1.45)

def arrow(start, end):
    ax.annotate('', xy=end, xytext=start,
                arrowprops={'arrowstyle': '->', 'color': '#244c70', 'lw': 1.2})

box(1.7, 6.8, 6.6, .65, 'Near-extremal graph with fixed defect $s$\nTheorem C′, fixed-defect hypotheses')
box(1.7, 5.35, 6.6, .85, 'Low-degree deletion with evolving deficit\n(6.15); induction window in Appendix F.1')
box(1.7, 3.9, 6.6, .85, 'Controlled terminal: clique root and retained accounts\n(6.14)')
box(1.7, 2.45, 6.6, .85, 'Reinsert deleted vertices: one root in the original graph\nEdit and baseline bounds (6.12)')
box(.15, .25, 4.5, 1.35,
    'Keep this root for every partition\nPiece count and edge mass\n(6.13), derived through (6.16)',
    '#edf4ed', '#39634b')
box(5.1, .25, 4.75, 1.35,
    'Resize to an optimal-size template\nCorollary 6.3; additional square-root cost\nWorst-case obstruction: Proposition 6.3a',
    '#faf0e5', '#85532c')
for top, bottom in [(6.8, 6.2), (5.35, 4.75), (3.9, 3.3)]:
    arrow((5, top-.08), (5, bottom+.08))
arrow((4.2, 2.37), (2.4, 1.68))
arrow((5.8, 2.37), (7.4, 1.68))
fig.tight_layout(pad=.5)
for extension in ('png', 'svg', 'pdf'):
    fig.savefig(OUT / ('fig4_same_root_stability.' + extension),
                dpi=180, bbox_inches='tight', facecolor='white')
plt.close(fig)
