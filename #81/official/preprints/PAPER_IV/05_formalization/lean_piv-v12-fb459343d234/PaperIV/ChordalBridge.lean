import PaperIV.ChordalStructure
import PaperIV.DonationBudget

/-!
# Puente a la estructura cordal, y la cota incondicional de (A)

Conecta el `SimpleGraph.IsChordal` portado de Paper II (`PaperIV.ChordalStructure`) con el
`PaperIV.FarRounding.IsChordal` que ya usaban los módulos del régimen lejano, y demuestra
el resultado que acota (A) **sin ninguna hipótesis externa**.

## Contenido

* `isChordal_iff` — las dos definiciones de cordalidad coinciden.
* `exists_isSimplicial` — Dirac, en el vocabulario de `FarRounding`.
* `ownerOf`, `ownerOf_eq` — la función arista→pieza inducida por un packing.
* `exists_ownership_of_packing` — **el teorema**: todo packing de `G` induce una
  asignación de aristas y packings por bolsa cuya ganancia total es *exactamente* la del
  packing de partida.
* `assignmentLossOwnAt_of_integralityGap` — corolario: la pérdida de la ruta por bolsas
  **nunca excede el gap de integralidad**.

## Qué dice esto sobre (A), y qué no

`exists_ownership_of_packing` es la recíproca de
`AssignmentLemma.exists_packing_of_ownership`, y tiene una consecuencia que conviene
enunciar sin adornos: **descomponer por bolsas no cuesta nada más allá de lo que cuesta
redondear**. Formalmente, `AssignmentLossOwnAt ζ` se sigue de la mera existencia de un
packing entero a distancia `ζ n²` del óptimo fraccional — es decir, del gap de
integralidad, que es justo la entrada que la ruta quería evitar.

Esto **no cierra (A)**, y conviene ser explícito sobre por qué no: dice que la ruta por
bolsas no es *peor* que la global, no que sea *mejor*. Su utilidad está en el otro
sentido: junto con `AssignmentLemma.loss_decomposition`, permite pagar el redondeo
**bolsa por bolsa**, donde `SplitBagExact.split_bag_exact` lo hace gratis y
`CliqueBagNibble.clique_bag_loss_of_nibble` lo hace barato. Lo que sigue abierto es
exhibir una asignación cuya pérdida *fraccional* —`W*(G) - Σ_b W*(H_b)`— sea `o(n²)`
**sin** pasar por un packing entero óptimo.
-/

namespace PaperIV.ChordalBridge

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Las dos cordalidades coinciden -/

/-- El `IsChordal` de `FarRounding` y el portado de Paper II son el mismo enunciado.

Desde el colapso de nombres lo son **literalmente**: `PaperIV.FarRounding.IsChordal` es un
alias (`export`) de `SimpleGraph.IsChordal`, la definicion canonica de
`PaperIV/ChordalStructure.lean` (= contribucion de Paper II fusionada en `lean-pool` #349).
Se conserva el enunciado porque lo consumen los lemas de abajo y los modulos del regimen
lejano; la demostracion es ahora `Iff.rfl`. -/
theorem isChordal_iff (G : SimpleGraph V) :
    PaperIV.FarRounding.IsChordal G ↔ SimpleGraph.IsChordal G := Iff.rfl

/-- **Dirac (1961)** en el vocabulario de `FarRounding`: todo cordal finito no vacío tiene
un vértice simplicial.  Es el paso de la inducción por eliminación que (A) necesita. -/
theorem exists_isSimplicial [Nonempty V] (h : PaperIV.FarRounding.IsChordal G) :
    ∃ v : V, G.IsSimplicial v :=
  ((isChordal_iff G).1 h).exists_isSimplicial

/-- **Los separadores minimales de un cordal son cliques**, en el vocabulario de
`FarRounding`.  Es el teorema que sostiene el árbol de cliques. -/
theorem minimalSeparator_isClique (h : PaperIV.FarRounding.IsChordal G)
    {S : Finset V} {a b : V} (hS : G.IsMinimalSeparator (S : Set V) a b) :
    G.IsClique (S : Set V) :=
  ((isChordal_iff G).1 h).minimalSeparator_isClique hS

/-! ## 2. Todo packing induce su propia asignación -/

/-- La pieza de `P` que ocupa la arista `e`, si existe.  Está bien definida porque las
piezas de un packing son disjuntas en aristas (`ownerOf_eq`). -/
noncomputable def ownerOf (P : Packing G) (e : Sym2 V) : Finset V :=
  if h : ∃ K ∈ P.pieces, e ∈ pairs K then h.choose else ∅

/-- Si `e` está en el soporte de la pieza `K`, entonces `ownerOf` devuelve exactamente `K`.
Aquí se usa la disyunción en aristas del packing. -/
theorem ownerOf_eq (P : Packing G) {K : Finset V} (hK : K ∈ P.pieces) {e : Sym2 V}
    (he : e ∈ pairs K) : ownerOf P e = K := by
  have hex : ∃ K ∈ P.pieces, e ∈ pairs K := ⟨K, hK, he⟩
  rw [ownerOf, dif_pos hex]
  obtain ⟨hmem, hin⟩ := hex.choose_spec
  by_contra hne
  exact (Finset.disjoint_left.1 (P.edgeDisjoint _ hmem K hK hne)) hin he

/-- El packing de una sola pieza, cuando esa pieza es un ítem; vacío en caso contrario. -/
noncomputable def singletonPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : Finset V) : Packing G :=
  if h : IsItem G b then
    { pieces := {b}
      isItem := by intro K hK; rw [Finset.mem_singleton.1 hK]; exact h
      edgeDisjoint := by
        intro K hK L hL hKL
        rw [Finset.mem_singleton.1 hK, Finset.mem_singleton.1 hL] at hKL
        exact absurd rfl hKL }
  else { pieces := ∅, isItem := by simp, edgeDisjoint := by simp }

theorem singletonPacking_gain_of_isItem {b : Finset V} (h : IsItem G b) :
    (singletonPacking G b).gain = gainOf b := by
  rw [singletonPacking, dif_pos h]
  show ∑ K ∈ ({b} : Finset (Finset V)), gainOf K = gainOf b
  rw [Finset.sum_singleton]

/-- **Todo packing induce su propia asignación.**  Dado `P`, la función `ownerOf P`
reparte las aristas y los packings de una pieza reconstruyen la ganancia **exacta**.

Es la recíproca de `AssignmentLemma.exists_packing_of_ownership`: la ruta por bolsas no
pierde nada frente a un packing global dado. -/
theorem exists_ownership_of_packing (P : Packing G) :
    ∃ (Bs : Finset (Finset V)) (own : Sym2 V → Finset V) (Q : Finset V → Packing G),
      (∀ b ∈ Bs, ∀ K ∈ (Q b).pieces, ∀ e ∈ pairs K, own e = b) ∧
      ∑ b ∈ Bs, (Q b).gain = P.gain := by
  classical
  refine ⟨P.pieces, ownerOf P, singletonPacking G, ?_, ?_⟩
  · intro b hb K hK e he
    have hitem : IsItem G b := P.isItem b hb
    rw [singletonPacking, dif_pos hitem] at hK
    rw [Finset.mem_singleton.1 hK] at he
    exact ownerOf_eq P hb he
  · rw [Packing.gain]
    exact Finset.sum_congr rfl fun b hb => singletonPacking_gain_of_isItem (P.isItem b hb)

/-- **La pérdida de la ruta por bolsas nunca excede el gap de integralidad.**  Si existe un
packing entero a distancia `ζ n²` del óptimo fraccional certificado, entonces
`AssignmentLemma.AssignmentLossOwnAt ζ` se cumple.

Dicho al revés, y es lo que importa para no engañarse: (A) **no puede ser más difícil**
que el redondeo global, pero tampoco lo esquiva por sí sola.  Su valor está en permitir
pagar el redondeo bolsa por bolsa. -/
theorem assignmentLossOwnAt_of_integralityGap {ζ : ℚ}
    (h : ∃ T : ℕ, ∀ n : ℕ, T ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ∃ P : Packing G, w - (P.gain : ℚ) ≤ ζ * (n : ℚ) ^ 2) :
    PaperIV.AssignmentLemma.AssignmentLossOwnAt ζ := by
  classical
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro n hn G _ hchord w hw
  obtain ⟨P, hP⟩ := hT n hn G hchord w hw
  obtain ⟨Bs, own, Q, hsupp, hsum⟩ := exists_ownership_of_packing P
  set ι : Finset (Fin n) → ℕ := fun b => ((Fintype.equivFin (Finset (Fin n))) b).val with hι
  have hinj : Function.Injective ι := by
    intro a b hab
    exact (Fintype.equivFin (Finset (Fin n))).injective (Fin.val_injective hab)
  set Qk : ℕ → Packing G := fun k =>
    if hk : ∃ b ∈ Bs, ι b = k then Q hk.choose
    else ⟨∅, by simp, by simp⟩ with hQk
  have hQkeq : ∀ b ∈ Bs, Qk (ι b) = Q b := by
    intro b hb
    have hex : ∃ b2 ∈ Bs, ι b2 = ι b := ⟨b, hb, rfl⟩
    simp only [hQk]
    rw [dif_pos hex]
    obtain ⟨-, heq⟩ := hex.choose_spec
    rw [hinj heq]
  refine ⟨Bs.image ι, fun e => ι (own e), Qk, ?_, ?_⟩
  · intro k hk K hK e he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hk
    rw [hQkeq b hb] at hK
    show ι (own e) = ι b
    rw [hsupp b hb K hK e he]
  · have hgain : ∑ k ∈ Bs.image ι, ((Qk k).gain : ℚ) = ∑ b ∈ Bs, ((Q b).gain : ℚ) := by
      rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
      exact Finset.sum_congr rfl fun b hb => by rw [hQkeq b hb]
    have htot : ∑ b ∈ Bs, ((Q b).gain : ℚ) = (P.gain : ℚ) := by
      rw [← hsum]; push_cast; ring
    rw [hgain, htot]
    exact hP

end PaperIV.ChordalBridge
