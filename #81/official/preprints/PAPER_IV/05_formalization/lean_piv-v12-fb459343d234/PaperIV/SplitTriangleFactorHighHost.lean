import PaperIV.SplitTriangleFactor
import PaperIV.SplitPackingObstruction

/-!
# The high-host regime of the complete split graph

`PaperIV.SplitTriangleFactor` builds an explicit triangle packing of the complete split
graph `splitGraph Core Hosts` with an even core `#Core = k = 2n+2` in the *low-host*
regime `#Hosts ≤ k - 1`.  `PaperIV.SplitPackingObstruction` shows that for `#Hosts ≥ k`
no `K3`/`K4` packing can cover all but linearly many edges, so in the high-host regime
the construction must be complemented by `K2` pieces.  This module treats exactly that
complementary regime.

The construction: choose `k - 1 = 2n+1` hosts out of the (arbitrarily large) host set,
and assign the `k-1` round-robin one-factors of the core clique to them — the assignment
is a *bijection* between the selected hosts and the one-factors
(`exists_split_high_host_labelled`).  The resulting physical `K3` packing is an exact
triangle partition of the sub-split-graph `splitGraph Core S` on the selected hosts `S`,
hence a `K3` packing of the full split graph whose uncovered edge set is **literally**
the set of cross edges at the unused hosts, `crossEdges Core (Hosts \ S)`.  Completing it
by those `K2` edges gives an exact physical partition whose piece count is the split
baseline

  `#Core * #Hosts - C(#Core, 2) = k * (N - k) - C(k,2)`,   `N = #Core + #Hosts`,

equivalently `C(k,2) + k * (#Hosts - (k-1))`: the baseline `C(k,2)` of the critical
parameter `#Hosts = k-1` plus a *linear* correction of `k` pieces per extra host.

The unified statement `exists_split_completion_card` covers **all** host numbers at once,
using truncated subtraction:

  `(completion).card = C(k,2) + k * (#Hosts - (k-1))`.

Nothing is assumed: the packing, its ledger and the identification of the uncovered
edges are all proved from the literal split graph; the transport from the selected-host
split graph to the full split graph is the reusable lemma `isK34Packing_mono_hosts`.
-/

namespace PaperIV.SplitTriangleFactorHighHost

open Finset PaperIV.Model PaperIV.SplitUniformIncidence PaperIV.SplitEdgeCount
open PaperIV.PhysicalCompletion PaperIV.SplitTriangleFactor PaperIV.RoundRobinPairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Transport along an enlargement of the host set -/

omit [Fintype V] in
/-- The split graph is monotone in its host set. -/
theorem splitGraph_mono_hosts {Core Hosts Hosts' : Finset V} (h : Hosts' ⊆ Hosts) :
    splitGraph Core Hosts' ≤ splitGraph Core Hosts := by
  intro x y hxy
  obtain ⟨hne, hcase⟩ := hxy
  refine ⟨hne, ?_⟩
  rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr (Or.inl ⟨hx, h hy⟩)
  · exact Or.inr (Or.inr ⟨h hx, hy⟩)

omit [Fintype V] in
/-- A piece of a sub-split-graph is a piece of the larger split graph. -/
theorem isPiece_mono_hosts {Core Hosts Hosts' : Finset V} (hsub : Hosts' ⊆ Hosts) {s : Finset V}
    (hs : IsPiece (splitGraph Core Hosts') s) : IsPiece (splitGraph Core Hosts) s :=
  ⟨hs.clique.mono (splitGraph_mono_hosts hsub), hs.kind⟩

omit [Fintype V] in
/-- **Transport lemma.**  A physical `K3`/`K4` packing of the split graph on a subset of
the hosts is literally a packing of the split graph on all hosts. -/
theorem isK34Packing_mono_hosts {Core Hosts Hosts' : Finset V} (hsub : Hosts' ⊆ Hosts)
    {P : Finset (Finset V)} (hP : IsK34Packing (splitGraph Core Hosts') P) :
    IsK34Packing (splitGraph Core Hosts) P :=
  { pieces := fun s hs => isPiece_mono_hosts hsub (hP.pieces s hs)
    edgeDisjoint := hP.edgeDisjoint
    big := hP.big }

/-! ## The edges gained by enlarging the host set -/

/-- Enlarging the host set from `S` to `Hosts` adds exactly the cross edges at the new
hosts. -/
theorem graphEdges_sdiff_hosts {Core Hosts S : Finset V} (hd : Disjoint Core Hosts)
    (hS : S ⊆ Hosts) :
    graphEdges (splitGraph Core Hosts) \ graphEdges (splitGraph Core S)
      = crossEdges Core (Hosts \ S) := by
  have hdS : Disjoint Core S := Finset.disjoint_of_subset_right hS hd
  ext e
  induction e with
  | _ a b =>
    rw [Finset.mem_sdiff, graphEdges_splitGraph hd, graphEdges_splitGraph hdS,
      Finset.mem_union, Finset.mem_union]
    constructor
    · rintro ⟨hmem, hnot⟩
      have hinner : s(a, b) ∉ pieceEdges Core := fun h => hnot (Or.inl h)
      have hcross : s(a, b) ∈ crossEdges Core Hosts := by
        rcases hmem with h | h
        · exact absurd h hinner
        · exact h
      obtain ⟨x, hx, z, hz, hxz⟩ := mem_crossEdges.mp hcross
      refine mem_crossEdges.mpr ⟨x, hx, z, Finset.mem_sdiff.mpr ⟨hz, ?_⟩, hxz⟩
      intro hzS
      exact hnot (Or.inr (mem_crossEdges.mpr ⟨x, hx, z, hzS, hxz⟩))
    · intro hmem
      obtain ⟨x, hx, z, hz, hxz⟩ := mem_crossEdges.mp hmem
      rw [Finset.mem_sdiff] at hz
      have hzCore : z ∉ Core := fun h => (Finset.disjoint_left.mp hd h) hz.1
      refine ⟨Or.inr (mem_crossEdges.mpr ⟨x, hx, z, hz.1, hxz⟩), ?_⟩
      rintro (hinner | hcross)
      · rw [hxz, mem_pieceEdges_mk] at hinner
        exact hzCore hinner.2.1
      · obtain ⟨x', hx', z', hz', hxz'⟩ := mem_crossEdges.mp hcross
        rw [hxz, Sym2.eq_iff] at hxz'
        rcases hxz' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hz.2 hz'
        · exact hzCore hx'

/-- If a packing of the full split graph covers exactly the edges of the split graph on
a subset `S` of the hosts, then its uncovered edges are exactly the cross edges at the
unused hosts. -/
theorem uncoveredEdges_eq_cross {Core Hosts S : Finset V} (hd : Disjoint Core Hosts)
    (hS : S ⊆ Hosts) {P : Finset (Finset V)}
    (hcov : coveredEdges P = graphEdges (splitGraph Core S)) :
    uncoveredEdges (splitGraph Core Hosts) P = crossEdges Core (Hosts \ S) := by
  rw [uncoveredEdges, hcov, graphEdges_sdiff_hosts hd hS]

omit [Fintype V] in
/-- The number of cross edges at the unused hosts. -/
theorem card_crossEdges_sdiff {Core Hosts S : Finset V} (hd : Disjoint Core Hosts)
    (hS : S ⊆ Hosts) :
    (crossEdges Core (Hosts \ S)).card = Core.card * (Hosts.card - S.card) := by
  rw [card_crossEdges (Finset.disjoint_of_subset_right Finset.sdiff_subset hd),
    Finset.card_sdiff_of_subset hS]

/-- Arithmetic helper: from `c + 2a = a + b` conclude `c = b - a` (in `ℕ`). -/
theorem nat_sub_of_add_two_mul {a b c : ℕ} (h : c + 2 * a = a + b) : c = b - a := by omega

/-- **The baseline count.**  Any physical `K3` packing of the split graph with an even
core `#Core = 2n+2` and total gain `2(2n+1)(n+1) = k(k-1)` (that is: one that uses up all
`k-1` one-factors of the core) has a completion with exactly the split baseline number
of pieces `k*h - C(k,2)`. -/
theorem completion_card_baseline {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) {P : Finset (Finset V)}
    (hP : IsK34Packing (splitGraph Core Hosts) P)
    (hgain : totalGain P = 2 * ((2 * n + 1) * (n + 1))) :
    (completion (splitGraph Core Hosts) P).card = Core.card * Hosts.card - Core.card.choose 2 := by
  have hsum := card_completion_add_totalGain hP
  rw [hgain, card_graphEdges_splitGraph hd, hk, choose_two_even] at hsum
  rw [hk, choose_two_even]
  have h2 : 2 * ((2 * n + 1) * (n + 1)) = 2 * ((n + 1) * (2 * n + 1)) := by ring
  rw [h2] at hsum
  exact nat_sub_of_add_two_mul hsum

/-! ## The high-host construction, with the explicit one-factor assignment -/

/-- **The labelled high-host construction.**  Let `Core` and `Hosts` be disjoint, let the
core be even of size `k = 2n+2`, and let there be at least `k-1 = 2n+1` hosts (the host
set is otherwise arbitrary, in particular arbitrarily large).

Then one can select `k-1` hosts `S ⊆ Hosts`, enumerate the core by the round-robin vertex
set `Option (ZMod (2n+1))` and assign to the selected hosts the `k-1` round-robin
one-factors of the core clique **bijectively** (`col`), so that the literal packing
`PaperIV.SplitTriangleFactor.packing cv hv col`

* is a physical `K3` packing of the full split graph,
* consists of `(2n+1)(n+1)` triangles with total gain `2(2n+1)(n+1) = k(k-1)`,
* covers exactly the edges of the split graph on the selected hosts, and
* leaves uncovered exactly the `k*(h-(k-1))` cross edges at the unused hosts,

so that its completion by `K2` edges is an exact physical partition of the split graph
with exactly `k*h - C(k,2)` pieces. -/
theorem exists_split_high_host_labelled {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) (hh : 2 * n + 1 ≤ Hosts.card) :
    ∃ S ⊆ Hosts, S.card = 2 * n + 1 ∧
      ∃ (cv : Option (R n) → V) (hv : Fin S.card → V) (col : Fin S.card → R n),
        SplitFactorLabelling Core S n cv hv col ∧ Function.Bijective col ∧
        IsK34Packing (splitGraph Core Hosts) (packing cv hv col) ∧
        (∀ s ∈ packing cv hv col, s.card = 3) ∧
        (packing cv hv col).card = (2 * n + 1) * (n + 1) ∧
        totalGain (packing cv hv col) = 2 * ((2 * n + 1) * (n + 1)) ∧
        coveredEdges (packing cv hv col) = graphEdges (splitGraph Core S) ∧
        uncoveredEdges (splitGraph Core Hosts) (packing cv hv col)
          = crossEdges Core (Hosts \ S) ∧
        (uncoveredEdges (splitGraph Core Hosts) (packing cv hv col)).card
          = Core.card * (Hosts.card - (2 * n + 1)) ∧
        IsExactPartition (splitGraph Core Hosts)
          (completion (splitGraph Core Hosts) (packing cv hv col)) ∧
        (completion (splitGraph Core Hosts) (packing cv hv col)).card
          = Core.card * Hosts.card - Core.card.choose 2 := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  obtain ⟨S, hS, hScard⟩ : ∃ S ⊆ Hosts, S.card = 2 * n + 1 :=
    Finset.exists_subset_card_eq hh
  have hdS : Disjoint Core S := Finset.disjoint_of_subset_right hS hd
  obtain ⟨cv, hv, col, hL⟩ := exists_splitFactorLabelling hdS hk (le_of_eq hScard)
  -- the one-factor assignment is a bijection: `#S = 2n+1 = #(ZMod (2n+1))`
  have hcolBij : Function.Bijective col := by
    refine (Fintype.bijective_iff_injective_and_card col).mpr ⟨hL.colInj, ?_⟩
    rw [Fintype.card_fin, hScard, ZMod.card]
  have hcardH : Fintype.card (Fin S.card) = 2 * n + 1 := by rw [Fintype.card_fin, hScard]
  have hcardP : (packing cv hv col).card = (2 * n + 1) * (n + 1) := by
    rw [hL.card_packing, hcardH]
  have hgainP : totalGain (packing cv hv col) = 2 * ((2 * n + 1) * (n + 1)) := by
    rw [hL.totalGain_packing, hcardH]
  have hcovCard : (coveredEdges (packing cv hv col)).card = 3 * ((2 * n + 1) * (n + 1)) := by
    rw [hL.card_coveredEdges_packing, hcardH]
  -- the packing is an exact partition of the split graph on the selected hosts
  have hcov : coveredEdges (packing cv hv col) = graphEdges (splitGraph Core S) := by
    refine Finset.eq_of_subset_of_card_le hL.isPacking.coveredEdges_subset ?_
    rw [card_graphEdges_splitGraph hdS, hcovCard, hk, choose_two_even, hScard]
    nlinarith
  -- transport to the full split graph
  have hK34 : IsK34Packing (splitGraph Core Hosts) (packing cv hv col) :=
    isK34Packing_mono_hosts hS hL.isK34Packing
  have huncov : uncoveredEdges (splitGraph Core Hosts) (packing cv hv col)
      = crossEdges Core (Hosts \ S) := uncoveredEdges_eq_cross hd hS hcov
  have huncovCard : (uncoveredEdges (splitGraph Core Hosts) (packing cv hv col)).card
      = Core.card * (Hosts.card - (2 * n + 1)) := by
    rw [huncov, card_crossEdges_sdiff hd hS, hScard]
  exact ⟨S, hS, hScard, cv, hv, col, hL, hcolBij, hK34,
    fun s hs => hL.card_eq_three_of_mem_packing hs, hcardP, hgainP, hcov, huncov, huncovCard,
    isExactPartition_completion hK34.toIsPacking,
    completion_card_baseline hd hk hK34 hgainP⟩

/-! ## The high-host ledger in existential form -/

/-- **The high-host construction.**  For a complete split graph with an even core of size
`k = 2n+2` and at least `k-1` hosts there is a physical `K3` packing of `(2n+1)(n+1)`
triangles covering every inner edge and every cross edge at `k-1` selected hosts, whose
completion by the `k*(h-(k-1))` remaining cross edges is an exact physical partition of
the split graph with exactly

  `k*h - C(k,2) = C(k,2) + k*(h - (k-1))`

pieces: the baseline value at the critical parameter `h = k-1` plus a linear correction
of `k` per extra host. -/
theorem exists_split_high_host_packing {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) (hh : 2 * n + 1 ≤ Hosts.card) :
    ∃ S ⊆ Hosts, S.card = 2 * n + 1 ∧ ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      (∀ s ∈ P, s.card = 3) ∧
      P.card = (2 * n + 1) * (n + 1) ∧
      totalGain P = 2 * ((2 * n + 1) * (n + 1)) ∧
      coveredEdges P = graphEdges (splitGraph Core S) ∧
      uncoveredEdges (splitGraph Core Hosts) P = crossEdges Core (Hosts \ S) ∧
      (uncoveredEdges (splitGraph Core Hosts) P).card
        = Core.card * (Hosts.card - (2 * n + 1)) ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card
        = Core.card * Hosts.card - Core.card.choose 2 ∧
      (completion (splitGraph Core Hosts) P).card
        = Core.card.choose 2 + Core.card * (Hosts.card - (2 * n + 1)) := by
  obtain ⟨S, hS, hScard, cv, hv, col, -, -, hK34, hthree, hcardP, hgainP, hcov, huncov,
    huncovCard, hpart, hbase⟩ := exists_split_high_host_labelled hd hk hh
  refine ⟨S, hS, hScard, packing cv hv col, hK34, hthree, hcardP, hgainP, hcov, huncov,
    huncovCard, hpart, hbase, ?_⟩
  rw [card_completion hK34, hcardP, huncovCard, hk, choose_two_even]
  ring

/-- **Unified count, all host numbers.**  For a complete split graph with even core of
size `k = 2n+2` and an arbitrary host set there is a physical `K3` packing whose
completion is an exact partition of the split graph into exactly

  `C(k,2) + k * (#Hosts - (k-1))`

pieces (truncated subtraction): the constant baseline `C(k,2)` up to the critical
parameter `#Hosts = k-1`, and a linear correction of `k` pieces per additional host
beyond it. -/
theorem exists_split_completion_card {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      (∀ s ∈ P, s.card = 3) ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card
        = Core.card.choose 2 + Core.card * (Hosts.card - (2 * n + 1)) := by
  by_cases hh : 2 * n + 1 ≤ Hosts.card
  · obtain ⟨S, -, -, P, hK34, hthree, -, -, -, -, -, hpart, -, hcompl⟩ :=
      exists_split_high_host_packing hd hk hh
    exact ⟨P, hK34, hthree, hpart, hcompl⟩
  · push_neg at hh
    obtain ⟨P, hK34, hthree, hcardP, -, -, -, -, huncov⟩ :=
      exists_split_triangle_packing hd hk (by omega)
    refine ⟨P, hK34, hthree, isExactPartition_completion hK34.toIsPacking, ?_⟩
    have hzero : Hosts.card - (2 * n + 1) = 0 := by omega
    rw [card_completion hK34, hcardP, uncoveredEdges, huncov, hk, choose_two_even, hzero]
    have : Hosts.card * (n + 1) + (n + 1) * (2 * n + 1 - Hosts.card) = (n + 1) * (2 * n + 1) := by
      rw [Nat.mul_comm Hosts.card (n + 1), ← Nat.mul_add,
        Nat.add_sub_cancel' (by omega : Hosts.card ≤ 2 * n + 1)]
    omega

/-- **The split baseline, stated with the total vertex count.**  With
`N = #Core + #Hosts` the completion count of the high-host construction is exactly the
split baseline `k*(N-k) - C(k,2)`. -/
theorem exists_split_high_host_baseline {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n N : ℕ} (hk : Core.card = 2 * n + 2) (hh : 2 * n + 1 ≤ Hosts.card)
    (hN : N = Core.card + Hosts.card) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card
        = Core.card * (N - Core.card) - Core.card.choose 2 := by
  obtain ⟨S, -, -, P, hK34, -, -, -, -, -, -, hpart, hbase, -⟩ :=
    exists_split_high_host_packing hd hk hh
  refine ⟨P, hK34, hpart, ?_⟩
  have hNC : N - Core.card = Hosts.card := by omega
  rw [hNC]
  exact hbase

/-! ## Optimality: no `K3`/`K4` packing gives fewer pieces

The residue `k*(h-(k-1))` of the construction is exactly the obstruction bound
`PaperIV.SplitPackingObstruction.card_uncovered_lower_bound_of_many_hosts`.  The
underlying ledger statement is a gain bound: every piece has gain at most twice its
inner (core) resource, so the total gain of any packing is at most `2*C(k,2) = k*(k-1)`,
and therefore no packing completes to fewer than `k*h - C(k,2)` pieces. -/

open PaperIV.SplitPackingObstruction in
/-- **Local gain bound.**  A `K3`/`K4` piece of a complete split graph has gain at most
twice the number of inner (core) edges it carries. -/
theorem gainOf_le_two_mul_innerPart {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {s : Finset V} (hp : IsPiece (splitGraph Core Hosts) s) (hcard : s.card = 3 ∨ s.card = 4) :
    gainOf s ≤ 2 * (innerPart Core s).card := by
  have hclique := hp.clique
  have h3 : 3 ≤ s.card := by rcases hcard with h | h <;> omega
  -- the piece splits into its core part and at most one host
  have hsplit : (s ∩ Core).card + (s ∩ Hosts).card = s.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      rw [← Finset.inter_union_distrib_left]
      exact Finset.inter_eq_left.mpr (subset_core_union_hosts hclique (by omega))
    · refine Finset.disjoint_left.mpr ?_
      intro a ha hb
      exact (Finset.disjoint_left.mp hd (Finset.mem_inter.mp ha).2) (Finset.mem_inter.mp hb).2
  have hhost : (s ∩ Hosts).card ≤ 1 := card_inter_hosts_le_one hd hclique
  have hcore : s.card - 1 ≤ (s ∩ Core).card := by omega
  have hinner : (innerPart Core s).card = (s ∩ Core).card.choose 2 := by
    rw [innerPart_eq, card_pieceEdges]
  -- the gain of the piece is `C(#s, 2) - 1`
  have hgain : gainOf s + 1 = s.card.choose 2 := by
    rw [← card_pieceEdges s, hp.card_pieceEdges_eq]
  rw [hinner]
  rcases hcard with h | h
  · have h2 : 2 ≤ (s ∩ Core).card := by omega
    have : (2 : ℕ).choose 2 ≤ (s ∩ Core).card.choose 2 := Nat.choose_le_choose 2 h2
    rw [h] at hgain
    simp only [Nat.choose] at hgain this ⊢
    omega
  · have h2 : 3 ≤ (s ∩ Core).card := by omega
    have : (3 : ℕ).choose 2 ≤ (s ∩ Core).card.choose 2 := Nat.choose_le_choose 2 h2
    rw [h] at hgain
    simp only [Nat.choose] at hgain this ⊢
    omega

open PaperIV.SplitPackingObstruction in
/-- **Global gain bound.**  Any `K3`/`K4` packing of a complete split graph has total
gain at most `k*(k-1) = 2*C(k,2)`: the core clique is the only gain resource. -/
theorem totalGain_le_core {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {Q : Finset (Finset V)} (hQ : IsK34Packing (splitGraph Core Hosts) Q) :
    totalGain Q ≤ Core.card * (Core.card - 1) := by
  classical
  have hstep : totalGain Q ≤ ∑ s ∈ Q, 2 * (innerPart Core s).card :=
    Finset.sum_le_sum fun s hs => gainOf_le_two_mul_innerPart hd (hQ.pieces s hs) (hQ.big s hs)
  have hsum : ∑ s ∈ Q, (innerPart Core s).card
      = ((coveredEdges Q).filter fun e => e ∈ pieceEdges Core).card :=
    (filter_coveredEdges _ hQ.toIsPacking).symm
  have hle : ((coveredEdges Q).filter fun e => e ∈ pieceEdges Core).card ≤ Core.card.choose 2 := by
    rw [← card_pieceEdges Core]
    exact Finset.card_le_card fun e he => (Finset.mem_filter.mp he).2
  have hmul : ∑ s ∈ Q, 2 * (innerPart Core s).card = 2 * ∑ s ∈ Q, (innerPart Core s).card :=
    (Finset.mul_sum _ _ _).symm
  have hchoose := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two Core.card
  omega

/-- Arithmetic helper: from `c + g = a + b`, `g ≤ t` and `t = 2a` conclude
`b - a ≤ c`. -/
theorem nat_le_of_gain_bound {a b c g t : ℕ} (h : c + g = a + b) (hg : g ≤ t) (ht : t = 2 * a) :
    b - a ≤ c := by omega

/-- **Optimality of the baseline.**  No `K3`/`K4` packing of the complete split graph
completes to fewer than `k*h - C(k,2)` physical pieces. -/
theorem card_completion_ge_baseline {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {Q : Finset (Finset V)} (hQ : IsK34Packing (splitGraph Core Hosts) Q) :
    Core.card * Hosts.card - Core.card.choose 2
      ≤ (completion (splitGraph Core Hosts) Q).card := by
  have hsum := card_completion_add_totalGain hQ
  rw [card_graphEdges_splitGraph hd] at hsum
  have hchoose := PaperIV.SplitUniformIncidence.mul_pred_eq_two_mul_choose_two Core.card
  exact nat_le_of_gain_bound hsum (totalGain_le_core hd hQ) (by omega)

/-- **The high-host construction is optimal.**  Its completion has the least possible
number of physical pieces among the completions of all `K3`/`K4` packings of the split
graph, namely the split baseline `k*h - C(k,2)`. -/
theorem exists_split_high_host_optimal {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    {n : ℕ} (hk : Core.card = 2 * n + 2) (hh : 2 * n + 1 ≤ Hosts.card) :
    ∃ P : Finset (Finset V),
      IsK34Packing (splitGraph Core Hosts) P ∧
      IsExactPartition (splitGraph Core Hosts) (completion (splitGraph Core Hosts) P) ∧
      (completion (splitGraph Core Hosts) P).card
        = Core.card * Hosts.card - Core.card.choose 2 ∧
      ∀ Q : Finset (Finset V), IsK34Packing (splitGraph Core Hosts) Q →
        (completion (splitGraph Core Hosts) P).card
          ≤ (completion (splitGraph Core Hosts) Q).card := by
  obtain ⟨S, -, -, P, hK34, -, -, -, -, -, -, hpart, hbase, -⟩ :=
    exists_split_high_host_packing hd hk hh
  refine ⟨P, hK34, hpart, hbase, fun Q hQ => ?_⟩
  rw [hbase]
  exact card_completion_ge_baseline hd hQ

/-! ## The shape of the completion pieces

Every piece of the completion is either one of the `(2n+1)(n+1)` triangles of the packing
or the `K2` edge piece `{x, z}` of a cross edge at an unused host. -/

theorem completion_pieces_shape {Core Hosts S : Finset V} {P : Finset (Finset V)}
    (huncov : uncoveredEdges (splitGraph Core Hosts) P = crossEdges Core (Hosts \ S))
    {s : Finset V} (hs : s ∈ completion (splitGraph Core Hosts) P) :
    s ∈ P ∨ ∃ x ∈ Core, ∃ z ∈ Hosts \ S, s = ({x, z} : Finset V) := by
  rcases mem_completion.mp hs with h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · rw [huncov, mem_crossEdges] at he
    obtain ⟨x, hx, z, hz, rfl⟩ := he
    exact Or.inr ⟨x, hx, z, hz, by simp [edgePiece, Sym2.toFinset_mk_eq]⟩

/-! ## Non-vacuity

A literal high-host instance: a core of four vertices (`k = 4`, `n = 1`) and five hosts
inside `Fin 9`.  The baseline count is `4 * 5 - C(4,2) = 14`: six triangles on the three
selected hosts, plus `4 * 2 = 8` cross `K2` edges at the two unused hosts. -/

namespace Example

/-- A four-element core inside `Fin 9`. -/
def exCore : Finset (Fin 9) := {0, 1, 2, 3}

/-- Five hosts inside `Fin 9` — more than `k - 1 = 3`, so this is the high-host regime. -/
def exHosts : Finset (Fin 9) := {4, 5, 6, 7, 8}

theorem exDisjoint : Disjoint exCore exHosts := by decide

theorem exCoreCard : exCore.card = 2 * 1 + 2 := by decide

theorem exHostsCard : 2 * 1 + 1 ≤ exHosts.card := by decide

/-- The complete split graph on this core and these five hosts is partitioned into
exactly `14 = 4*5 - C(4,2)` physical pieces: six triangles and eight cross edges. -/
theorem exists_partition_example :
    ∃ P : Finset (Finset (Fin 9)),
      IsK34Packing (splitGraph exCore exHosts) P ∧
      P.card = 6 ∧
      (∀ s ∈ P, s.card = 3) ∧
      IsExactPartition (splitGraph exCore exHosts)
        (completion (splitGraph exCore exHosts) P) ∧
      (completion (splitGraph exCore exHosts) P).card = 14 := by
  obtain ⟨S, -, -, P, hK34, hthree, hcardP, -, -, -, -, hpart, hbase, -⟩ :=
    exists_split_high_host_packing exDisjoint exCoreCard exHostsCard
  refine ⟨P, hK34, by simpa using hcardP, hthree, hpart, ?_⟩
  rw [hbase]
  decide

end Example

end PaperIV.SplitTriangleFactorHighHost


