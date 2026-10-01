"""Translate Figure 4 without changing its graph or geometry."""
from pathlib import Path
import make_stability_figure as base

labels=[
 "Grafo casi extremal de defecto fijo $s$\nTeorema C′, hipótesis de defecto fijo",
 "Borrado de grado bajo con déficit variable\n(6.15); ventana de inducción en el Apéndice F.1",
 "Terminal controlado: clique raíz y cuentas conservadas\n(6.14)",
 "Reinsertar vértices: una raíz en el grafo original\nCotas de edición y baseline (6.12)",
 "Conservar la raíz para toda partición\nNúmero de piezas y masa de aristas\n(6.13), mediante (6.16)",
 "Ajustar a una plantilla de tamaño óptimo\nCorolario 6.3; coste adicional de raíz cuadrada\nObstrucción de peor caso: Proposición 6.3a",
]
texts=[t for t in base.ax.texts if t.get_text()]
assert len(texts)==len(labels)
for t,label in zip(texts,labels):
    t.set_text(label)
out=Path(__file__).resolve().parent/"figures"
for ext in ("png","svg","pdf"):
    base.fig.savefig(out/("fig4_same_root_stability."+ext),dpi=180,bbox_inches="tight",facecolor="white")
