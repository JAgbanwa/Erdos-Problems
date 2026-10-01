import A4S1.IndepAllArith
import A4S1.IndepAllPeel

/-!
# E14 (copied from E10 `A4S1.OwnAllSetup`, no forbidden import)
# E10, own terminal for every rooted defect `s`: normalization and the `(m, d)` classification

Fix `s`; write `S = s + 1`, `n = |V|`, `w = n/S²` and `v = n/S⁴`.

Input (`AllInput G A s`): rooted defect `s`, `n ≥ 10⁵⁰ S⁸`, minimum degree `≥ (1/3 − ε) n`, and a
clique `A` of order `n/3 ± εn` with at most `εn²` missing `A`–exterior incidences and at most
`εn²` exterior edges, where `ε = ε_s = 1/(10⁴¹ S⁸)`.

The sets (step 1 of `TASK_E10.txt`, thresholds scaled with `s`; see `data/E10_STATUS.md`):

* `pA0` — the pruned clique: vertices of `A` missing at most `v/10¹⁰` exterior vertices;
* `pR0 = V ∖ pA0`;
* `pY` — heavy vertices, at least `w/10⁴` neighbours in `pR0`; `pL` — light vertices (rows);
* for `y ∈ pY`: `m_y = |pA0 ∖ N(y)|`, `d_y = |pL ∖ N(y)|`;
  * `pYc` — `d_y ≤ w/40` (core),
  * `pYr` — `d_y > w/40`, `m_y ≤ w/200` (rows),
  * `pT`  — `d_y > w/40`, `m_y > w/200` (exceptional);
* core `pCore = pA0 ∪ pYc`, rows `pHost = pL ∪ pYr`.
-/

namespace A4S1.IndepAll

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect A4S1.TerminalPacking

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `ε_s = 1/(10⁴¹ (s+1)⁸)`. -/
def epsS (s : ℕ) : ℚ := 1 / (10 ^ 41 * ((s : ℚ) + 1) ^ 8)

variable (V) in
/-- `w = n/(s+1)²`. -/
def scW (s : ℕ) : ℚ := (Fintype.card V : ℚ) / ((s : ℚ) + 1) ^ 2

variable (V) in
/-- `v = n/(s+1)⁴`. -/
def scV (s : ℕ) : ℚ := (Fintype.card V : ℚ) / ((s : ℚ) + 1) ^ 4

/-- The hypotheses of the terminal at rooted defect `s`, with `ε = ε_s`. -/
structure AllInput (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (s : ℕ) : Prop where
  rd : RootedDefectAt G s
  hn : (10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 8 ≤ Fintype.card V
  deg : ∀ v, ((1 : ℚ) / 3 - epsS s) * Fintype.card V ≤ G.degree v
  clique : G.IsClique (A : Set V)
  size_lo : (Fintype.card V : ℚ) / 3 - epsS s * Fintype.card V ≤ A.card
  size_hi : (A.card : ℚ) ≤ Fintype.card V / 3 + epsS s * Fintype.card V
  miss : ((∑ a ∈ A, ((univ \ A).filter fun y => ¬ G.Adj a y).card : ℕ) : ℚ) ≤
    epsS s * (Fintype.card V : ℚ) ^ 2
  out : ((inEdges G (univ \ A)).card : ℚ) ≤ epsS s * (Fintype.card V : ℚ) ^ 2

variable (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (s : ℕ)

/-- The pruned clique. -/
def pA0 : Finset V :=
  A.filter fun a => (((univ \ A).filter fun y => ¬ G.Adj a y).card : ℚ) ≤ scV V s / 10 ^ 10

/-- The exterior of the pruned clique. -/
def pR0 : Finset V := univ \ pA0 G A s

/-- Heavy exterior vertices: at least `w/10⁴` exterior neighbours. -/
def pY : Finset V :=
  (pR0 G A s).filter fun v => scW V s / 10 ^ 4 ≤ (((pR0 G A s).filter (G.Adj v)).card : ℚ)

/-- Light exterior vertices. -/
def pL : Finset V := pR0 G A s \ pY G A s

/-- Heavy vertices missing at most `w/40` light vertices. -/
def pYc : Finset V :=
  (pY G A s).filter fun y => (((pL G A s).filter fun z => ¬ G.Adj y z).card : ℚ) ≤ scW V s / 40

/-- Heavy vertices missing more than `w/40` light vertices but at most `w/200` of `pA0`. -/
def pYr : Finset V :=
  (pY G A s \ pYc G A s).filter fun y =>
    (((pA0 G A s).filter fun a => ¬ G.Adj y a).card : ℚ) ≤ scW V s / 200

/-- The exceptional vertices. -/
def pT : Finset V := (pY G A s \ pYc G A s) \ pYr G A s

/-- The (not necessarily complete) core. -/
def pCore : Finset V := pA0 G A s ∪ pYc G A s

/-- The rows. -/
def pHost : Finset V := pL G A s ∪ pYr G A s

variable {G A s}

theorem pA0_subset : pA0 G A s ⊆ A := filter_subset _ _

theorem mem_pR0 {v : V} : v ∈ pR0 G A s ↔ v ∉ pA0 G A s := by simp [pR0]

theorem pY_subset : pY G A s ⊆ pR0 G A s := filter_subset _ _

theorem mem_pL {v : V} : v ∈ pL G A s ↔ v ∈ pR0 G A s ∧ v ∉ pY G A s := mem_sdiff

theorem pL_subset : pL G A s ⊆ pR0 G A s := sdiff_subset

theorem pYc_subset : pYc G A s ⊆ pY G A s := filter_subset _ _

theorem mem_pYc {v : V} : v ∈ pYc G A s ↔ v ∈ pY G A s ∧
    (((pL G A s).filter fun z => ¬ G.Adj v z).card : ℚ) ≤ scW V s / 40 := mem_filter

theorem mem_pYr {v : V} : v ∈ pYr G A s ↔ (v ∈ pY G A s ∧ v ∉ pYc G A s) ∧
    (((pA0 G A s).filter fun a => ¬ G.Adj v a).card : ℚ) ≤ scW V s / 200 := by
  simp [pYr, mem_filter, mem_sdiff]

theorem mem_pT {v : V} : v ∈ pT G A s ↔ v ∈ pY G A s ∧ v ∉ pYc G A s ∧ v ∉ pYr G A s := by
  simp [pT, and_assoc]

theorem pYr_subset : pYr G A s ⊆ pY G A s := fun _ h => (mem_pYr.1 h).1.1

theorem pT_subset : pT G A s ⊆ pY G A s := fun _ h => (mem_pT.1 h).1

theorem mem_pCore {v : V} : v ∈ pCore G A s ↔ v ∈ pA0 G A s ∨ v ∈ pYc G A s := mem_union

theorem mem_pHost {v : V} : v ∈ pHost G A s ↔ v ∈ pL G A s ∨ v ∈ pYr G A s := mem_union

theorem pHost_subset_pR0 : pHost G A s ⊆ pR0 G A s := by
  intro v hv
  rcases mem_pHost.1 hv with h | h
  · exact pL_subset h
  · exact pY_subset (pYr_subset h)

theorem pT_not_A0 {v : V} (hv : v ∈ pT G A s) : v ∉ pA0 G A s :=
  mem_pR0.1 (pY_subset (pT_subset hv))

theorem core_host_disjoint : Disjoint (pCore G A s) (pHost G A s) := by
  rw [disjoint_left]
  intro v hv hv'
  rcases mem_pCore.1 hv with h | h <;> rcases mem_pHost.1 hv' with h' | h'
  · exact mem_pR0.1 (pL_subset h') h
  · exact mem_pR0.1 (pY_subset (pYr_subset h')) h
  · exact (mem_pL.1 h').2 (pYc_subset h)
  · exact (mem_pYr.1 h').1.2 h

theorem core_T_disjoint : Disjoint (pCore G A s) (pT G A s) := by
  rw [disjoint_left]
  intro v hv hv'
  rcases mem_pCore.1 hv with h | h
  · exact pT_not_A0 hv' h
  · exact (mem_pT.1 hv').2.1 h

theorem host_T_disjoint : Disjoint (pHost G A s) (pT G A s) := by
  rw [disjoint_left]
  intro v hv hv'
  rcases mem_pHost.1 hv with h | h
  · exact (mem_pL.1 h).2 (pT_subset hv')
  · exact (mem_pT.1 hv').2.2 h

theorem cover (v : V) : v ∈ pCore G A s ∨ v ∈ pHost G A s ∨ v ∈ pT G A s := by
  rw [mem_pCore, mem_pHost, mem_pT]
  by_cases h0 : v ∈ pA0 G A s
  · exact Or.inl (Or.inl h0)
  have hR : v ∈ pR0 G A s := mem_pR0.2 h0
  by_cases hY : v ∈ pY G A s
  · by_cases hc : v ∈ pYc G A s
    · exact Or.inl (Or.inr hc)
    by_cases hr : v ∈ pYr G A s
    · exact Or.inr (Or.inl (Or.inr hr))
    · exact Or.inr (Or.inr ⟨hY, hc, hr⟩)
  · exact Or.inr (Or.inl (Or.inl (mem_pL.2 ⟨hR, hY⟩)))

theorem A0_Yc_disjoint : Disjoint (pA0 G A s) (pYc G A s) :=
  disjoint_left.2 fun _ h h' => mem_pR0.1 (pY_subset (pYc_subset h')) h

theorem L_Yr_disjoint : Disjoint (pL G A s) (pYr G A s) :=
  disjoint_left.2 fun _ h h' => (mem_pL.1 h).2 (pYr_subset h')

theorem card_core : (pCore G A s).card = (pA0 G A s).card + (pYc G A s).card :=
  card_union_of_disjoint A0_Yc_disjoint

theorem card_host : (pHost G A s).card = (pL G A s).card + (pYr G A s).card :=
  card_union_of_disjoint L_Yr_disjoint

theorem card_Y_split : (pYc G A s).card + (pYr G A s).card + (pT G A s).card = (pY G A s).card := by
  have h1 : pYr G A s ⊆ pY G A s \ pYc G A s := filter_subset _ _
  have h2 : (pT G A s).card = (pY G A s \ pYc G A s).card - (pYr G A s).card := card_sdiff_of_subset h1
  have h3 : (pY G A s \ pYc G A s).card = (pY G A s).card - (pYc G A s).card :=
    card_sdiff_of_subset pYc_subset
  have h4 := card_le_card h1
  have h5 := card_le_card (pYc_subset (G := G) (A := A) (s := s))
  omega

theorem card_R0 : (pA0 G A s).card + (pR0 G A s).card = Fintype.card V := by
  rw [pR0, card_sdiff_of_subset (subset_univ _), card_univ]
  have := card_le_univ (pA0 G A s)
  omega

theorem card_R0_split : (pL G A s).card + (pY G A s).card = (pR0 G A s).card := by
  rw [pL, card_sdiff_of_subset pY_subset]
  have := card_le_card (pY_subset (G := G) (A := A) (s := s))
  omega

theorem card_total : (pCore G A s).card + (pHost G A s).card + (pT G A s).card = Fintype.card V := by
  rw [card_core, card_host]
  have := card_Y_split (G := G) (A := A) (s := s)
  have := card_R0 (G := G) (A := A) (s := s)
  have := card_R0_split (G := G) (A := A) (s := s)
  omega

end A4S1.IndepAll
