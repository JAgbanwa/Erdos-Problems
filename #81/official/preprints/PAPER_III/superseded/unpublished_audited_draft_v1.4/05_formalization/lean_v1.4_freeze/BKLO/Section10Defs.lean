/-
# BKLO §10 — the vocabulary of Section 10, in edge-set language (r = 2, F = K₃).

This file fixes the notation used by the faithful transcription of Barber–Kühn–Lo–Osthus §10
("Near optimal decompositions") for `r = 2`, i.e. for `F = K₃`.  Graphs are edge sets
`E : Finset (Sym2 V)` over a vertex type `V`, as everywhere else in this project; a *vertex set*
`S : Finset V` plays the role of `V(G)`.

The paper's notation is transcribed as follows.

| paper                     | here                        |
| ------------------------- | --------------------------- |
| `N_G(x, V)`               | `nbhdIn E x W`              |
| `d_G(x, V)`               | `degTo E x W`               |
| `G[S]`                    | `edgesIn E S`               |
| `G[S, T]`                 | `edgesBtw E S T`            |
| `G[P]` (crossing edges)   | `crossParts E P`            |
| `G − G[P] = ⋃_{V∈P} G[V]` | `insideParts E P`           |
| `Δ(H) ≤ c`                | `∀ v, (edeg H v : ℝ) ≤ c`   |
| `r`-divisible, `r = 2`    | `EvenDegrees`               |
| `(k, δ)`-partition        | `IsKDeltaPartition k δ P E S` |
| `F`-decomposition, `F=K₃` | `TriDecomp`                 |

Everything here is `sorry`-free.
-/
import BKLO.Vortex

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Neighbourhoods and degrees into a set -/

/-- `N_E(x, S)`: the neighbours of `x` inside `S`. -/
def nbhdIn (E : Finset (Sym2 V)) (x : V) (S : Finset V) : Finset V :=
  S.filter (fun y => s(x, y) ∈ E)

/-- `d_E(x, S) = |N_E(x, S)|`. -/
def degTo (E : Finset (Sym2 V)) (x : V) (S : Finset V) : ℕ := (nbhdIn E x S).card

theorem mem_nbhdIn {E : Finset (Sym2 V)} {x y : V} {S : Finset V} :
    y ∈ nbhdIn E x S ↔ y ∈ S ∧ s(x, y) ∈ E := by
  simp [nbhdIn]

theorem nbhdIn_subset (E : Finset (Sym2 V)) (x : V) (S : Finset V) : nbhdIn E x S ⊆ S :=
  Finset.filter_subset _ _

theorem nbhdIn_mono_left {E E' : Finset (Sym2 V)} (h : E ⊆ E') (x : V) (S : Finset V) :
    nbhdIn E x S ⊆ nbhdIn E' x S := by
  intro y hy
  rw [mem_nbhdIn] at hy ⊢
  exact ⟨hy.1, h hy.2⟩

theorem nbhdIn_mono_right {E : Finset (Sym2 V)} {S S' : Finset V} (h : S ⊆ S') (x : V) :
    nbhdIn E x S ⊆ nbhdIn E x S' := by
  intro y hy
  rw [mem_nbhdIn] at hy ⊢
  exact ⟨h hy.1, hy.2⟩

theorem degTo_mono_left {E E' : Finset (Sym2 V)} (h : E ⊆ E') (x : V) (S : Finset V) :
    degTo E x S ≤ degTo E' x S :=
  Finset.card_le_card (nbhdIn_mono_left h x S)

theorem degTo_le_card (E : Finset (Sym2 V)) (x : V) (S : Finset V) : degTo E x S ≤ S.card :=
  Finset.card_le_card (nbhdIn_subset E x S)

/-! ### Induced and crossing edge sets -/

/-- `E[S]`: the edges of `E` with both ends in `S`. -/
def edgesIn (E : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) :=
  E.filter (fun e => e ∈ S.sym2)

/-- `E[S, T]`: the edges of `E` with one end in `S` and the other in `T`. -/
def edgesBtw (E : Finset (Sym2 V)) (S T : Finset V) : Finset (Sym2 V) :=
  E.filter (fun e => ∃ a ∈ S, ∃ b ∈ T, e = s(a, b))

/-- `E − E[P] = ⋃_{W ∈ P} E[W]`: the edges of `E` lying inside a part of `P`. -/
def insideParts (E : Finset (Sym2 V)) (P : Finset (Finset V)) : Finset (Sym2 V) :=
  E.filter (fun e => ∃ W ∈ P, e ∈ W.sym2)

/-- `E[P]`: the edges of `E` joining two different parts of `P`. -/
def crossParts (E : Finset (Sym2 V)) (P : Finset (Finset V)) : Finset (Sym2 V) :=
  E.filter (fun e => ¬ ∃ W ∈ P, e ∈ W.sym2)

theorem mem_edgesIn {E : Finset (Sym2 V)} {S : Finset V} {e : Sym2 V} :
    e ∈ edgesIn E S ↔ e ∈ E ∧ ∀ v ∈ e, v ∈ S := by
  simp [edgesIn, Finset.mem_sym2_iff]

theorem mem_insideParts {E : Finset (Sym2 V)} {P : Finset (Finset V)} {e : Sym2 V} :
    e ∈ insideParts E P ↔ e ∈ E ∧ ∃ W ∈ P, ∀ v ∈ e, v ∈ W := by
  simp [insideParts, Finset.mem_sym2_iff]

theorem mem_crossParts {E : Finset (Sym2 V)} {P : Finset (Finset V)} {e : Sym2 V} :
    e ∈ crossParts E P ↔ e ∈ E ∧ ¬ ∃ W ∈ P, ∀ v ∈ e, v ∈ W := by
  simp [crossParts, Finset.mem_sym2_iff]

theorem edgesIn_subset (E : Finset (Sym2 V)) (S : Finset V) : edgesIn E S ⊆ E :=
  Finset.filter_subset _ _

theorem insideParts_subset (E : Finset (Sym2 V)) (P : Finset (Finset V)) :
    insideParts E P ⊆ E := Finset.filter_subset _ _

theorem crossParts_subset (E : Finset (Sym2 V)) (P : Finset (Finset V)) :
    crossParts E P ⊆ E := Finset.filter_subset _ _

theorem disjoint_crossParts_insideParts (E : Finset (Sym2 V)) (P : Finset (Finset V)) :
    Disjoint (crossParts E P) (insideParts E P) := by
  refine Finset.disjoint_left.2 fun e he he' => ?_
  exact (mem_crossParts.1 he).2 (mem_insideParts.1 he').2

theorem crossParts_union_insideParts (E : Finset (Sym2 V)) (P : Finset (Finset V)) :
    crossParts E P ∪ insideParts E P = E := by
  ext e
  simp only [Finset.mem_union, mem_crossParts, mem_insideParts]
  by_cases h : ∃ W ∈ P, ∀ v ∈ e, v ∈ W <;> tauto

theorem sdiff_crossParts (E : Finset (Sym2 V)) (P : Finset (Finset V)) :
    E \ crossParts E P = insideParts E P := by
  ext e
  simp only [Finset.mem_sdiff, mem_crossParts, mem_insideParts]
  constructor
  · rintro ⟨he, h⟩
    refine ⟨he, ?_⟩
    by_contra hx
    exact h ⟨he, hx⟩
  · rintro ⟨he, hx⟩
    exact ⟨he, fun hc => hc.2 hx⟩

theorem edgesIn_mono {E : Finset (Sym2 V)} {S S' : Finset V} (hE : S ⊆ S') :
    edgesIn E S ⊆ edgesIn E S' := by
  intro e he
  rw [mem_edgesIn] at he ⊢
  exact ⟨he.1, fun v hv => hE (he.2 v hv)⟩

theorem edgesIn_mono_left {E E' : Finset (Sym2 V)} (h : E ⊆ E') (S : Finset V) :
    edgesIn E S ⊆ edgesIn E' S := by
  intro e he
  rw [mem_edgesIn] at he ⊢
  exact ⟨h he.1, he.2⟩

/-! ### Degrees and edge deletion -/

theorem edeg_mono {E E' : Finset (Sym2 V)} (h : E ⊆ E') (v : V) : edeg E v ≤ edeg E' v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- The number of vertices `y` with `s(x,y) ∈ H` is at most the degree of `x` in `H`. -/
theorem card_filter_edge_le_edeg (H : Finset (Sym2 V)) (x : V) (S : Finset V) :
    (S.filter (fun y => s(x, y) ∈ H)).card ≤ edeg H x := by
  classical
  have hinj : Set.InjOn (fun y => s(x, y)) (S.filter (fun y => s(x, y) ∈ H)) := by
    intro a _ b _ hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  have hsub : (S.filter (fun y => s(x, y) ∈ H)).image (fun y => s(x, y))
      ⊆ H.filter (fun e => x ∈ e) := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).2, by simp⟩
  calc (S.filter (fun y => s(x, y) ∈ H)).card
      = ((S.filter (fun y => s(x, y) ∈ H)).image (fun y => s(x, y))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ edeg H x := Finset.card_le_card hsub

/-- Deleting `H` from `E` costs each vertex at most `edeg H x` neighbours in any set. -/
theorem degTo_sdiff_ge (E H : Finset (Sym2 V)) (x : V) (S : Finset V) :
    degTo E x S ≤ degTo (E \ H) x S + edeg H x := by
  classical
  have hsub : nbhdIn E x S ⊆ nbhdIn (E \ H) x S ∪ S.filter (fun y => s(x, y) ∈ H) := by
    intro y hy
    rw [mem_nbhdIn] at hy
    by_cases hH : s(x, y) ∈ H
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hy.1, hH⟩)
    · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hy.1, Finset.mem_sdiff.2 ⟨hy.2, hH⟩⟩)
  calc degTo E x S ≤ (nbhdIn (E \ H) x S ∪ S.filter (fun y => s(x, y) ∈ H)).card :=
        Finset.card_le_card hsub
    _ ≤ degTo (E \ H) x S + (S.filter (fun y => s(x, y) ∈ H)).card := Finset.card_union_le _ _
    _ ≤ degTo (E \ H) x S + edeg H x := by
        exact Nat.add_le_add_left (card_filter_edge_le_edeg H x S) _

/-! ### Divisibility (`r`-divisibility for `r = 2`) -/

/-- `E` is `2`-divisible: every vertex has even degree.  (For `F = K₃`, `r = 2`.) -/
def EvenDegrees (E : Finset (Sym2 V)) : Prop := ∀ v : V, Even (edeg E v)

/-! ### Equitable partitions and `(k, δ)`-partitions -/

/-- An equitable partition of `S` into `k` parts: pairwise disjoint parts covering `S`, each of
size `⌊|S|/k⌋` or `⌈|S|/k⌉`. -/
structure IsEquitablePartition (k : ℕ) (P : Finset (Finset V)) (S : Finset V) : Prop where
  card_parts : P.card = k
  pairwise_disjoint : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint W W'
  cover : P.biUnion id = S
  size_lower : ∀ W ∈ P, S.card / k ≤ W.card
  size_upper : ∀ W ∈ P, W.card ≤ (S.card + k - 1) / k

/-- **`(k, δ)`-partition** (BKLO §3): an equitable partition `P` of `S` into `k` parts such that
`d_E(x, W) ≥ δ|W|` for every vertex `x ∈ S` and every part `W ∈ P`. -/
def IsKDeltaPartition (k : ℕ) (d : ℝ) (P : Finset (Finset V)) (E : Finset (Sym2 V))
    (S : Finset V) : Prop :=
  IsEquitablePartition k P S ∧ ∀ x ∈ S, ∀ W ∈ P, d * (W.card : ℝ) ≤ (degTo E x W : ℝ)

theorem IsEquitablePartition.subset_of_mem {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (h : IsEquitablePartition k P S) {W : Finset V} (hW : W ∈ P) : W ⊆ S := by
  intro x hx
  rw [← h.cover]
  exact Finset.mem_biUnion.2 ⟨W, hW, hx⟩

/-- A `(k, d)`-partition is a `(k, d')`-partition for every `d' ≤ d`. -/
theorem IsKDeltaPartition.mono {k : ℕ} {d d' : ℝ} {P : Finset (Finset V)} {E : Finset (Sym2 V)}
    {S : Finset V} (h : IsKDeltaPartition k d P E S) (hd : d' ≤ d) :
    IsKDeltaPartition k d' P E S := by
  refine ⟨h.1, fun x hx W hW => le_trans ?_ (h.2 x hx W hW)⟩
  exact mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)

/-- A `(k, d)`-partition for `E` is a `(k, d)`-partition for any larger edge set. -/
theorem IsKDeltaPartition.mono_edges {k : ℕ} {d : ℝ} {P : Finset (Finset V)}
    {E E' : Finset (Sym2 V)} {S : Finset V} (h : IsKDeltaPartition k d P E S) (hE : E ⊆ E') :
    IsKDeltaPartition k d P E' S :=
  ⟨h.1, fun x hx W hW => le_trans (h.2 x hx W hW) (Nat.cast_le.2 (degTo_mono_left hE x W))⟩

/-- **Degradation of a `(k, δ)`-partition under edge deletion** (BKLO, the remark opening §10.3):
if `P` is a `(k, d)`-partition for `E` and `Δ(H) ≤ c` with `c ≤ (d - d')|W|` for every part `W`,
then `P` is a `(k, d')`-partition for `E - H`. -/
theorem IsKDeltaPartition.sdiff {k : ℕ} {d d' c : ℝ} {P : Finset (Finset V)}
    {E H : Finset (Sym2 V)} {S : Finset V} (h : IsKDeltaPartition k d P E S)
    (hH : ∀ v : V, (edeg H v : ℝ) ≤ c)
    (hc : ∀ W ∈ P, c ≤ (d - d') * (W.card : ℝ)) :
    IsKDeltaPartition k d' P (E \ H) S := by
  refine ⟨h.1, fun x hx W hW => ?_⟩
  have h1 : (degTo E x W : ℝ) ≤ (degTo (E \ H) x W : ℝ) + (edeg H x : ℝ) := by
    exact_mod_cast Nat.cast_le.2 (degTo_sdiff_ge E H x W)
  have h2 := h.2 x hx W hW
  have h3 := hH x
  have h4 := hc W hW
  linarith only [h1, h2, h3, h4]

/-! ### Proposition 10.5 -/

/-- The arithmetic behind Proposition 10.5:
`inter ≥ dy + d - w`, `dy, d ≥ (1 - 1/(R+1) + ε) w` imply `inter ≥ (1 - 1/R) d + ε w`. -/
theorem prop_10_5_arith {R d w dy inter ε : ℝ} (hR1 : 1 ≤ R) (hε : 0 ≤ ε) (hw : 0 ≤ w)
    (hx : (1 - 1 / (R + 1) + ε) * w ≤ d) (hdy : (1 - 1 / (R + 1) + ε) * w ≤ dy)
    (hin : dy + d ≤ inter + w) : (1 - 1 / R) * d + ε * w ≤ inter := by
  have hR0 : (0 : ℝ) < R := by linarith only [hR1]
  have hR1' : (0 : ℝ) < R + 1 := by linarith only [hR0]
  have hbase : (1 - 1 / (R + 1)) * w ≤ d := by nlinarith [mul_nonneg hε hw]
  have hnum : R * w ≤ d * (R + 1) := by
    have h2 : (1 - 1 / (R + 1)) * (R + 1) = R := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_right hbase (le_of_lt hR1')]
  have hdiff : d / R - w / (R + 1) = (d * (R + 1) - R * w) / (R * (R + 1)) := by
    field_simp
    try ring
  have hnn : (0 : ℝ) ≤ d / R - w / (R + 1) := by
    rw [hdiff]
    exact div_nonneg (by linarith) (by positivity)
  have hsplit : (1 - 1 / R) * d = d - d / R := by field_simp
  have hsplit2 : (1 - 1 / (R + 1) + ε) * w = w - w / (R + 1) + ε * w := by
    field_simp
    try ring
  rw [hsplit2] at hdy
  rw [hsplit]
  linarith only [hdy, hin, hnn]

/-- **BKLO Proposition 10.5.**  Let `P` be a `(k, 1 - 1/(r+1) + ε)`-partition for `G` and let
`W ∈ P`.  Then for every vertex `x` and every `y ∈ N_G(x, W)`,
`d_G(y, N_G(x, W)) ≥ (1 - 1/r) d_G(x, W) + ε|W|`, i.e.
`δ(G[N_G(x,W)]) ≥ (1 - 1/r) d_G(x, W) + ε|W|`.

Only the degree hypothesis at `x` and inside `W` is used, so it is stated in that form. -/
theorem prop_10_5 {E : Finset (Sym2 V)} {W : Finset V} {r : ℕ} (hr : 1 ≤ r) {ε : ℝ} (hε : 0 ≤ ε)
    {x : V} (hx : (1 - 1 / ((r : ℝ) + 1) + ε) * (W.card : ℝ) ≤ (degTo E x W : ℝ))
    (hy : ∀ z ∈ W, (1 - 1 / ((r : ℝ) + 1) + ε) * (W.card : ℝ) ≤ (degTo E z W : ℝ)) :
    ∀ y ∈ nbhdIn E x W,
      (1 - 1 / (r : ℝ)) * (degTo E x W : ℝ) + ε * (W.card : ℝ)
        ≤ (degTo E y (nbhdIn E x W) : ℝ) := by
  classical
  intro y hyW
  have hyS : y ∈ W := (nbhdIn_subset E x W) hyW
  -- `N_E(y, N_E(x,W)) = N_E(y,W) ∩ N_E(x,W)`
  have hinter : nbhdIn E y (nbhdIn E x W) = nbhdIn E y W ∩ nbhdIn E x W := by
    ext z
    simp only [mem_nbhdIn, Finset.mem_inter]
    tauto
  -- inclusion-exclusion inside `W`
  have hcard : (nbhdIn E y W).card + (nbhdIn E x W).card
      ≤ (nbhdIn E y W ∩ nbhdIn E x W).card + W.card := by
    have hunion : (nbhdIn E y W ∪ nbhdIn E x W).card ≤ W.card :=
      Finset.card_le_card (Finset.union_subset (nbhdIn_subset _ _ _) (nbhdIn_subset _ _ _))
    have := Finset.card_inter_add_card_union (nbhdIn E y W) (nbhdIn E x W)
    omega
  have hdegeq : degTo E y (nbhdIn E x W) = (nbhdIn E y W ∩ nbhdIn E x W).card := by
    unfold degTo
    rw [hinter]
  have hcardR : (degTo E y W : ℝ) + (degTo E x W : ℝ)
      ≤ (degTo E y (nbhdIn E x W) : ℝ) + (W.card : ℝ) := by
    rw [hdegeq]
    exact_mod_cast hcard
  have hR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  exact prop_10_5_arith hR1 hε (Nat.cast_nonneg _) hx (hy y hyS) hcardR

end BKLO
