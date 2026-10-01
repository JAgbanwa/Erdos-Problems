import PaperIV.SplitTriangleFactor
import PaperIV.SplitTerminalTarget

/-!
# Núcleos impares con muchos anfitriones: la factorización casi-1 del núcleo

`PaperIV.SplitTriangleFactor` construye la factorización redonda de un grafo split
completo cuyo **núcleo es par**, y `PaperIV.SplitTerminalTarget` deduce de ahí que ese
split alcanza el objetivo de Erdős #81.  `PaperIV.SplitTriangleFactorOdd` cubre los
núcleos impares sólo en el régimen de **pocos** anfitriones (`h ≤ k - 2`), que no es el
régimen extremal.

Este módulo cubre el caso que faltaba: núcleo impar `k = 2n+1` con `h ≥ k`
anfitriones, que es exactamente el régimen cercano (`k ≈ N/3`, `h ≈ 2N/3`).  La
construcción es la *casi-1-factorización* clásica de `K_{2n+1}`: los colores son los
residuos `i ∈ ZMod (2n+1)` y el color `i` consta de los `n` pares `{i+t, i-t}`,
`t = 1, …, n` (el vértice `i` queda libre).  Cada color se asigna a un anfitrión
distinto, lo que produce `n(2n+1) = C(k,2)` triángulos disjuntos en aristas y, por
tanto, una completación con exactamente

```
  k * h - C(k,2) = splitBaseline (k + h) k
```

piezas, la línea de base del split.  Con `PaperIV.SplitBaselineTarget` eso está por
debajo de `targetSize N`.

El módulo **no usa el motor de raíces** (`PaperIV.RootEngine*`): reutiliza sólo la
aritmética redonda de `PaperIV.RoundRobinPairs` y la maquinaria genérica de fase II.
-/

namespace PaperIV.SplitTriangleFactorOddHighHost

open Finset PaperIV.Model PaperIV.SplitUniformIncidence PaperIV.SplitEdgeCount
open PaperIV.PhysicalCompletion PaperIV.RD09PhaseII PaperIV.RoundRobinPairs

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-! ## La casi-1-factorización de `K_{2n+1}` -/

/-- Los desplazamientos no nulos `t = 1, …, n` del esquema redondo. -/
abbrev Off (n : ℕ) : Type := {t : Fin (n + 1) // (t : ℕ) ≠ 0}

/-- Primer extremo del par `t`-ésimo del color `i`. -/
def ofst (i : R n) (t : Off n) : R n := i + ((t.1 : ℕ) : R n)

/-- Segundo extremo del par `t`-ésimo del color `i`. -/
def osnd (i : R n) (t : Off n) : R n := i - ((t.1 : ℕ) : R n)

/-- El par `t`-ésimo del color `i`, dentro del núcleo impar. -/
def opair (i : R n) (t : Off n) : Finset (R n) := {ofst i t, osnd i t}

@[simp] theorem mem_opair {i : R n} {t : Off n} {x : R n} :
    x ∈ opair i t ↔ x = ofst i t ∨ x = osnd i t := by simp [opair]

/-- Los pares impares son exactamente los pares redondos que no tocan al vértice
distinguido. -/
theorem pair_eq_image_opair (i : R n) (t : Off n) :
    pair i t.1 = (opair i t).image some := by
  rw [pair, opair, fstV_pos i t.2, sndV_pos i t.2]
  simp [ofst, osnd, Finset.image_insert]

theorem ofst_ne_osnd (i : R n) (t : Off n) : ofst i t ≠ osnd i t := by
  intro h
  exact fstV_ne_sndV i t.1 (by rw [fstV_pos i t.2, sndV_pos i t.2, ← ofst, ← osnd, h])

theorem card_opair (i : R n) (t : Off n) : (opair i t).card = 2 := by
  rw [opair, Finset.card_insert_of_notMem (by simpa using ofst_ne_osnd i t),
    Finset.card_singleton]

/-- Dos pares del mismo color son disjuntos: cada color es un emparejamiento. -/
theorem opair_disjoint (i : R n) {t t' : Off n} (h : t ≠ t') :
    Disjoint (opair i t) (opair i t') := by
  have hne : t.1 ≠ t'.1 := fun hEq => h (Subtype.ext hEq)
  have himg : Disjoint ((opair i t).image some) ((opair i t').image some) := by
    rw [← pair_eq_image_opair, ← pair_eq_image_opair]
    exact pair_disjoint i hne
  exact (Finset.disjoint_image (Option.some_injective _)).mp himg

/-- Dos pares de colores distintos se cortan en a lo sumo un vértice. -/
theorem opair_inter_card_le_one {i i' : R n} (hii : i ≠ i') (t t' : Off n) :
    (opair i t ∩ opair i' t').card ≤ 1 := by
  have h := card_inter_le_one hii t.1 t'.1
  rw [pair_eq_image_opair, pair_eq_image_opair,
    ← Finset.image_inter _ _ (Option.some_injective _),
    Finset.card_image_of_injective _ (Option.some_injective _)] at h
  exact h

theorem card_Off (n : ℕ) : Fintype.card (Off n) = n := by
  classical
  have : Fintype.card (Off n) =
      (Finset.univ.filter fun t : Fin (n + 1) => (t : ℕ) ≠ 0).card :=
    Fintype.card_subtype _
  rw [this]
  have hfilter : (Finset.univ.filter fun t : Fin (n + 1) => (t : ℕ) ≠ 0) =
      Finset.univ.erase (0 : Fin (n + 1)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro h hEq; exact h (by rw [hEq]; rfl)
    · intro h hval; exact h (Fin.ext (by simpa using hval))
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  omega

/-! ## Los datos del etiquetado -/

variable {Core Hosts : Finset V} {cv hv : R n → V}

/-- El etiquetado de la construcción impar: el núcleo se enumera por `ZMod (2n+1)` y
cada residuo, visto como color, recibe un anfitrión propio. -/
structure OddLabelling (Core Hosts : Finset V) (n : ℕ) (cv hv : R n → V) : Prop where
  cvInj : Function.Injective cv
  cvImage : Finset.univ.image cv = Core
  hvInj : Function.Injective hv
  hvSub : Finset.univ.image hv ⊆ Hosts
  disj : Disjoint Core Hosts

namespace OddLabelling

variable (hL : OddLabelling Core Hosts n cv hv)
include hL

theorem cv_mem (x : R n) : cv x ∈ Core := by
  rw [← hL.cvImage]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

theorem hv_mem (y : R n) : hv y ∈ Hosts :=
  hL.hvSub (Finset.mem_image_of_mem _ (Finset.mem_univ y))

theorem cv_ne_hv (x y : R n) : cv x ≠ hv y := by
  intro hEq
  exact (Finset.disjoint_left.mp hL.disj (hL.cv_mem x)) (hEq ▸ hL.hv_mem y)

end OddLabelling

/-! ## La familia de fase II -/

/-- Un índice por (color/anfitrión, par del color). -/
abbrev Idx (n : ℕ) : Type := R n × Off n

/-- El hub de un índice es su anfitrión: todas las piezas son triángulos. -/
def hubOf (hv : R n → V) : Idx n → Finset V := fun p => {hv p.1}

/-- La arista base de un índice es el par correspondiente del núcleo. -/
def baseOf (cv : R n → V) : Idx n → Sym2 V :=
  fun p => s(cv (ofst p.1 p.2), cv (osnd p.1 p.2))

@[simp] theorem hubOf_apply (hv : R n → V) (p : Idx n) : hubOf hv p = {hv p.1} := rfl

theorem baseOf_toFinset (cv : R n → V) (p : Idx n) :
    (baseOf cv p).toFinset = (opair p.1 p.2).image cv := by
  ext x
  simp only [baseOf, Sym2.mem_toFinset, Sym2.mem_iff, Finset.mem_image, mem_opair]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨ofst p.1 p.2, Or.inl rfl, rfl⟩
    · exact ⟨osnd p.1 p.2, Or.inr rfl, rfl⟩
  · rintro ⟨u, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem piece_eq (cv hv : R n → V) (p : Idx n) :
    piece (hubOf hv) (baseOf cv) p = {hv p.1} ∪ (opair p.1 p.2).image cv := by
  rw [piece, hubOf_apply, baseOf_toFinset]

theorem mem_piece_iff {cv hv : R n → V} {p : Idx n} {x : V} :
    x ∈ piece (hubOf hv) (baseOf cv) p ↔
      x = hv p.1 ∨ ∃ u ∈ opair p.1 p.2, cv u = x := by
  rw [piece_eq]
  simp [Finset.mem_union]

/-- El empaquetado: un triángulo por (anfitrión, par del núcleo). -/
def packing (cv hv : R n → V) : Finset (Finset V) :=
  phaseTwoPacking (hubOf hv) (baseOf cv)

namespace OddLabelling

variable (hL : OddLabelling Core Hosts n cv hv)
include hL

theorem baseOf_mem_graphEdges (p : Idx n) :
    baseOf cv p ∈ graphEdges (splitGraph Core Hosts) := by
  rw [baseOf, mem_graphEdges, SimpleGraph.mem_edgeSet]
  refine splitGraph_adj_inner (hL.cv_mem _) (hL.cv_mem _) ?_
  intro hEq
  exact ofst_ne_osnd p.1 p.2 (hL.cvInj hEq)

theorem image_opair_disjoint {i : R n} {t t' : Off n} (h : t ≠ t') :
    Disjoint ((opair i t).image cv) ((opair i t').image cv) :=
  (Finset.disjoint_image hL.cvInj).mpr (opair_disjoint i h)

theorem image_opair_inter_card_le_one {i i' : R n} (hii : i ≠ i') (t t' : Off n) :
    (((opair i t).image cv) ∩ ((opair i' t').image cv)).card ≤ 1 := by
  rw [← Finset.image_inter _ _ hL.cvInj, Finset.card_image_of_injective _ hL.cvInj]
  exact opair_inter_card_le_one hii t t'

/-- Dos piezas distintas comparten a lo sumo un vértice. -/
theorem meet_pieces (p q : Idx n) (hpq : p ≠ q) :
    ((piece (hubOf hv) (baseOf cv) p) ∩ (piece (hubOf hv) (baseOf cv) q)).card ≤ 1 := by
  by_cases hy : p.1 = q.1
  · have ht : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hy h)
    refine le_trans (Finset.card_le_card ?_) (Finset.card_singleton (hv p.1)).le
    intro x hx
    rw [Finset.mem_inter, piece_eq, piece_eq, Finset.mem_union, Finset.mem_union] at hx
    rw [Finset.mem_singleton]
    rcases hx.1 with h1 | h1
    · exact Finset.mem_singleton.mp h1
    · rcases hx.2 with h2 | h2
      · rw [Finset.mem_singleton] at h2
        rw [h2, hy]
      · exact absurd h2
          (Finset.disjoint_left.mp (by rw [hy] at h1 ⊢; exact hL.image_opair_disjoint ht) h1)
  · refine le_trans (Finset.card_le_card ?_) (hL.image_opair_inter_card_le_one hy p.2 q.2)
    intro x hx
    rw [Finset.mem_inter, piece_eq, piece_eq, Finset.mem_union, Finset.mem_union] at hx
    rw [Finset.mem_inter]
    have hxp : x ∈ (opair p.1 p.2).image cv := by
      rcases hx.1 with h1 | h1
      · exfalso
        rw [Finset.mem_singleton] at h1
        rcases hx.2 with h2 | h2
        · rw [Finset.mem_singleton] at h2
          exact hy (hL.hvInj (h1 ▸ h2 ▸ rfl))
        · obtain ⟨u, -, hu⟩ := Finset.mem_image.mp h2
          exact hL.cv_ne_hv u p.1 (by rw [hu, h1])
      · exact h1
    have hxq : x ∈ (opair q.1 q.2).image cv := by
      rcases hx.2 with h2 | h2
      · exfalso
        rw [Finset.mem_singleton] at h2
        obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hxp
        exact hL.cv_ne_hv u q.1 (by rw [hu, h2])
      · exact h2
    exact ⟨hxp, hxq⟩

/-- La construcción impar es una familia de fase II literal. -/
theorem isPhaseTwoFamily :
    IsPhaseTwoFamily (splitGraph Core Hosts) (hubOf hv) (baseOf cv) where
  baseEdge := hL.baseOf_mem_graphEdges
  hubCard := fun _ => Or.inl (by simp [hubOf])
  hubClique := fun p => by
    simp only [hubOf_apply, Finset.coe_singleton]
    exact SimpleGraph.isClique_singleton _
  hubAdj := by
    rintro p a ha w hw
    rw [hubOf_apply, Finset.mem_singleton] at hw
    subst hw
    have haCore : a ∈ Core := by
      rw [baseOf, Sym2.mem_iff] at ha
      rcases ha with rfl | rfl <;> exact hL.cv_mem _
    exact (splitGraph_adj_cross hL.disj haCore (hL.hv_mem p.1)).symm
  sep := by
    rintro p q a ha hmem
    rw [hubOf_apply, Finset.mem_singleton] at hmem
    rw [baseOf, Sym2.mem_iff] at ha
    rcases ha with rfl | rfl <;> exact hL.cv_ne_hv _ q.1 hmem
  meet := hL.meet_pieces

theorem card_piece_three (p : Idx n) :
    (piece (hubOf hv) (baseOf cv) p).card = 3 :=
  (hL.isPhaseTwoFamily).card_piece_eq_three (by simp [hubOf])

theorem card_eq_three_of_mem_packing {s : Finset V} (hs : s ∈ packing cv hv) :
    s.card = 3 := by
  rw [packing, mem_phaseTwoPacking] at hs
  obtain ⟨p, rfl⟩ := hs
  exact hL.card_piece_three p

theorem isK34Packing : IsK34Packing (splitGraph Core Hosts) (packing cv hv) :=
  { (hL.isPhaseTwoFamily).isPacking_phaseTwoPacking with
    big := fun _ hs => Or.inl (hL.card_eq_three_of_mem_packing hs) }

theorem totalGain_packing :
    totalGain (packing cv hv) = 2 * ((2 * n + 1) * n) := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  have hcardR : Fintype.card (R n) = 2 * n + 1 := ZMod.card (2 * n + 1)
  rw [packing, (hL.isPhaseTwoFamily).totalGain_phaseTwoPacking]
  have hk3 : k3Indices (hubOf hv) = (Finset.univ : Finset (Idx n)) :=
    Finset.filter_true_of_mem (fun p _ => by simp [hubOf])
  have hk4 : k4Indices (hubOf hv) = (∅ : Finset (Idx n)) :=
    Finset.filter_false_of_mem (fun p _ => by simp [hubOf])
  rw [hk3, hk4, Finset.card_univ, Fintype.card_prod, hcardR, card_Off]
  simp

end OddLabelling

/-! ## Existencia del etiquetado y conteo -/

/-- De las hipótesis de cardinalidad `#Core = 2n+1` y `#Hosts ≥ 2n+1` se construyen los
datos del etiquetado impar. -/
theorem exists_oddLabelling {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 1) (hh : 2 * n + 1 ≤ Hosts.card) :
    ∃ cv hv : R n → V, OddLabelling Core Hosts n cv hv := by
  classical
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  have hcardR : Fintype.card (R n) = 2 * n + 1 := ZMod.card (2 * n + 1)
  -- el núcleo
  have hcardC : Fintype.card (R n) = Core.card := by rw [hcardR, hk]
  let eC : R n ≃ {x // x ∈ Core} :=
    (Fintype.equivFinOfCardEq hcardC).trans (Core.equivFin).symm
  -- los anfitriones: un subconjunto de tamaño `2n+1`
  obtain ⟨S, hS, hScard⟩ : ∃ S ⊆ Hosts, S.card = 2 * n + 1 :=
    Finset.exists_subset_card_eq hh
  have hcardS : Fintype.card (R n) = S.card := by rw [hcardR, hScard]
  let eS : R n ≃ {x // x ∈ S} :=
    (Fintype.equivFinOfCardEq hcardS).trans (S.equivFin).symm
  refine ⟨fun u => (eC u : V), fun u => (eS u : V), ?_, ?_, ?_, ?_, hd⟩
  · intro a b hab
    exact eC.injective (Subtype.ext hab)
  · ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩; exact (eC u).2
    · intro hx; exact ⟨eC.symm ⟨x, hx⟩, by simp⟩
  · intro a b hab
    exact eS.injective (Subtype.ext hab)
  · intro x hx
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
    exact hS (eS u).2

/-- **La construcción impar de anfitriones abundantes.**  Para un grafo split completo
con núcleo impar `k = 2n+1` y al menos `k` anfitriones hay un empaquetado físico `K3`
cuya completación es una partición exacta con exactamente `k*h - C(k,2)` piezas: la
línea de base del split. -/
theorem exists_odd_high_host_baseline {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 1) (hh : 2 * n + 1 ≤ Hosts.card) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card
        = Core.card * Hosts.card - Core.card.choose 2 := by
  classical
  obtain ⟨cv, hv, hL⟩ := exists_oddLabelling hd hk hh
  refine ⟨packing cv hv, hL.isK34Packing, isExactPartition_completion
    (hL.isK34Packing).toIsPacking, ?_⟩
  have hsum := card_completion_add_totalGain (hL.isK34Packing)
  rw [hL.totalGain_packing, card_graphEdges_splitGraph hd, hk] at hsum
  have hchoose : (2 * n + 1).choose 2 = (2 * n + 1) * n := by
    have h := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two (2 * n + 1)
    have h2 : (2 * n + 1) * (2 * n + 1 - 1) = 2 * ((2 * n + 1) * n) := by
      have hsub : 2 * n + 1 - 1 = 2 * n := by omega
      rw [hsub]; ring
    omega
  rw [hk, hchoose]
  omega

/-! ## El objetivo integral -/

/-- El recuento impar `k*h - C(k,2)` nunca supera `targetSize N`. -/
theorem odd_count_le_targetSize {n h N : ℕ} (hh : 2 * n + 1 ≤ h)
    (hN : N = 2 * n + 1 + h) :
    (2 * n + 1) * h - (2 * n + 1).choose 2 ≤ PaperIV.targetSize N := by
  have hchoose : (2 * n + 1).choose 2 = (2 * n + 1) * n := by
    have h1 := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two (2 * n + 1)
    have h2 : (2 * n + 1) * (2 * n + 1 - 1) = 2 * ((2 * n + 1) * n) := by
      have hsub : 2 * n + 1 - 1 = 2 * n := by omega
      rw [hsub]; ring
    omega
  have hle : (2 * n + 1) * n ≤ (2 * n + 1) * h := Nat.mul_le_mul_left _ (by omega)
  set m : ℕ := (2 * n + 1) * h - (2 * n + 1) * n with hm
  have hmadd : m + (2 * n + 1) * n = (2 * n + 1) * h := by omega
  have hSq : ((m : ℤ) : ℚ) = PaperIV.splitBaseline (N : ℚ) ((2 * n + 1 : ℕ) : ℚ) := by
    have hmQ : (m : ℚ) + (2 * (n : ℚ) + 1) * (n : ℚ) = (2 * (n : ℚ) + 1) * (h : ℚ) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℚ)) hmadd
    have hNQ : (N : ℚ) = 2 * (n : ℚ) + 1 + (h : ℚ) := by
      rw [hN]; push_cast; ring
    rw [PaperIV.splitBaseline, hNQ]
    push_cast
    linarith
  have hZ : (m : ℤ) ≤ (PaperIV.targetSize N : ℤ) :=
    PaperIV.SplitBaselineTarget.splitBaseline_le_targetSize hSq
  have hmle : m ≤ PaperIV.targetSize N := by exact_mod_cast hZ
  rw [hchoose]
  exact hmle

/-- **Núcleo impar, split completo con muchos anfitriones: se alcanza el objetivo.** -/
theorem exists_exactPartition_card_le_targetSize_odd {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 1)
    (hh : 2 * n + 1 ≤ Hosts.card) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card ≤
        PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨P, hK34, hpart, hcount⟩ := exists_odd_high_host_baseline hd hk hh
  refine ⟨P, hK34, hpart, ?_⟩
  rw [hcount, hk]
  have harith : (2 * n + 1) * Hosts.card - (2 * n + 1).choose 2 ≤
      PaperIV.targetSize (Core.card + Hosts.card) := by
    rw [hk]
    exact odd_count_le_targetSize hh rfl
  exact harith.trans (PaperIV.SplitTerminalTarget.targetSize_mono
    (PaperIV.SplitTerminalTarget.card_add_card_le_card_univ hd))

/-- La misma conclusión en el lenguaje del ensamblaje lejano/cercano. -/
theorem exists_cliquePartition_le_targetSize_odd {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) {n : ℕ} (hk : Core.card = 2 * n + 1)
    (hh : 2 * n + 1 ≤ Hosts.card) :
    ∃ Q : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts),
      Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize (Fintype.card V) := by
  obtain ⟨P, -, hpart, hcount⟩ := exists_exactPartition_card_le_targetSize_odd hd hk hh
  exact PaperIV.PhysicalToCliquePartition.exists_cliquePartition_of_exactPartition_card_le
    hpart hcount

/-- **Todas las paridades.**  Todo grafo split completo cuyo núcleo tenga al menos dos
vértices y que tenga al menos tantos anfitriones como vértices del núcleo admite una
partición en cliques de orden a lo sumo cuatro y tamaño a lo sumo `targetSize N`. -/
theorem exists_cliquePartition_le_targetSize {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts) (hk : 2 ≤ Core.card) (hh : Core.card ≤ Hosts.card) :
    ∃ Q : PaperIV.FarRounding.CliquePartition (splitGraph Core Hosts),
      Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize (Fintype.card V) := by
  rcases Nat.even_or_odd Core.card with heven | hodd
  · obtain ⟨r, hr⟩ := heven
    have hk' : Core.card = 2 * (r - 1) + 2 := by omega
    exact PaperIV.SplitTerminalTarget.exists_cliquePartition_le_targetSize_even hd hk'
      (by omega)
  · obtain ⟨m, hm⟩ := hodd
    exact exists_cliquePartition_le_targetSize_odd hd (n := m) (by omega) (by omega)

end PaperIV.SplitTriangleFactorOddHighHost
