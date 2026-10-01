import PaperIV.DefectApexStability
import A4S1.HostAbsorption

/-!
# Rooted defect one: the defect–core term is paid by host absorption

`PaperIV.DefectApexStability.defect_apex_linear_stability` bounds the edit distance to the
defect comparator by `16 d + 17 ρ`, where `ρ = e_G(x, R)` is left completely unpaid.  Here,
for `s = 1` and a defect vertex `x` with `G - x` chordal, `ρ` is replaced by the
**shortfall of host supply** `ρ - |S|`, where `S` is any set of root neighbours of `x`
whose host-supply margins are at least `|S|`:

`d_E(G, (K_R ⊔ I_{x}) ∨ I_{V∖(R∪{x})}) ≤ 16 d + 32 (ρ - |S|)`.

In particular, if every root neighbour `a` of `x` has margin
`|N_H(x) ∩ N_H(a)| - (|R|-1) - 2 e(G[H]) ≥ ρ`, then `d_E ≤ 16 d`, with no additive constant.

The proof keeps every resource physical:

1. the near-regime witness of the chordal graph `G - x` gives a literal `K₃/K₄` packing
   of `G - x` with the RD09 ledger `|Q| ≤ B_{n-1}(k) - (117/1825) m - (12687/20000) A`
   (`chordal_near_partition`, the near branch of BP-01 without the final rounding);
2. the partition is pushed to `G` and **every** root edge `x a`, `a ∈ S`, is absorbed into a
   triangle `x a h_a` of `G`, with distinct hosts `h_a` whose link `a h_a` was a singleton
   piece (`A4S1.HostAbsorption.exists_absorbed_partition_of_margin`);
3. the shift identity `B_{n-1}(k) + (n-1-k) ≤ Q₁(n)` and the exact edit decomposition
   `d_E = m + A + μ + ρ` close the signed ledger
   `(117/1825) m + (12687/20000) A + μ + ρ ≤ d + 2 (ρ - |S|)`.
-/

namespace A4S1.DefectOneAbsorbed

open Finset
open PaperIV.FarRounding
open PaperIV.GraphFamilyDistance
open PaperIV.DefectComparatorGraph
open PaperIV.SplitUniformIncidence
open PaperIV.DefectApexStability
open PaperIV.DefectTargetArithmetic
open A4S1.HostAbsorption

/-! ### The near branch, keeping the partition -/

/-- **The near branch of chordal stability, with its partition.**  For large chordal `G`
whose order-four partitions all have at least `M(n) - δ` pieces, `δ ≤ γ n²`, there is a
clique `R` and an order-four partition `Q` of `G` with
`|Q| ≤ B_n(|R|) - (117/1825) m - (12687/20000) A`, where `m` and `A` are the outside edges
and missing incidences of `R`. -/
theorem chordal_near_partition :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ δ : ℚ,
        δ ≤ PaperIV.IntegralStability.gamma * (n : ℚ) ^ 2 →
        (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
            (PaperIV.targetSize n : ℚ) - δ ≤ (Q.size : ℚ)) →
          ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧ 2 ≤ R.card ∧
            ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
              (Q.size : ℚ) ≤ PaperIV.splitBaseline (n : ℚ) R.card -
                (117 : ℚ) / 1825 * ((PaperIV.RootVocab.outsideEdges G R).card : ℚ) -
                (12687 : ℚ) / 20000 * (PaperIV.RootVocab.missingIncidences G R : ℚ) := by
  classical
  obtain ⟨Nnear, hnear⟩ := PaperIV.HybridDichotomy.chordal_near_extremal_stability
  obtain ⟨Nfar, hfar⟩ :=
    PaperIV.FarSlackQuantitative.farRegime_cliquePartition_slack
      PaperIV.NearH1Calibration.eta PaperIV.IntegralStability.eta_pos
  refine ⟨max (max Nnear Nfar) 5, ?_⟩
  intro n hn G _ hG δ hδ hmin
  have hn5 : 5 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnnear : Nnear ≤ n :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnfar : Nfar ≤ n :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  by_cases hslack : (G.edgeFinset.card : ℚ) - w <
      (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2
  · exfalso
    obtain ⟨Q, hQ4, hQlt⟩ := hfar n hnfar G hG w hw hslack
    have h1 := hmin Q hQ4
    have h2 := PaperIV.FarSlackQuantitative.sq_div_six_le_targetSize hn5
    have hn5Q : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn5
    have hsq : (0 : ℚ) < (n : ℚ) ^ 2 := by nlinarith
    have hγ : PaperIV.IntegralStability.gamma = PaperIV.NearH1Calibration.eta / 4 := rfl
    rw [hγ] at hδ
    nlinarith [PaperIV.IntegralStability.eta_pos]
  · obtain ⟨W⟩ := hnear n hnnear G hG w hw hslack
    set R : Finset (Fin n) := W.regularized.root with hRdef
    have hRclique : G.IsClique (R : Set (Fin n)) := W.regularized.isClique
    have hRtwo : 2 ≤ R.card := by
      have h := W.regularized.card_ge
      rw [hRdef]
      omega
    obtain ⟨Q, hQ4, hQsize⟩ :=
      PaperIV.NearRegimePacking.exists_cliquePartition_card_completion W.isPacking
    have hbase : (W.accounts.baseCount : ℚ) =
        PaperIV.splitBaseline (n : ℚ) W.accounts.split := by
      have h := W.accounts.base_eq
      rw [W.accounts_order] at h
      simpa using h
    have hpaid := W.accounts_count_le_improved
    rw [← W.accounts.base_eq] at hpaid
    have hm : W.accounts.missingEdges.card = (PaperIV.RootVocab.outsideEdges G R).card := by
      rw [W.accounts_missing]
    have hA : W.accounts.rootLossEdges.card = PaperIV.RootVocab.missingIncidences G R := by
      rw [W.accounts_rootLoss, PaperIV.RD09SplitEditAccount.card_missingSpokeEdges]
    have hbaseR : (W.accounts.baseCount : ℚ) = PaperIV.splitBaseline (n : ℚ) R.card := by
      rw [hbase, W.accounts_split]
    refine ⟨R, hRclique, hRtwo, Q, hQ4, ?_⟩
    rw [hQsize, ← hm, ← hA, ← hbaseR]
    exact hpaid

/-! ### Counting at the defect vertex -/

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges touching `{x}` are the edges at `x`; there are `deg x` of them. -/
theorem card_touch_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.edgeFinset.filter (Touches {x})).card = (G.neighborFinset x).card := by
  have hEq : G.edgeFinset.filter (Touches {x}) = G.incidenceFinset x := by
    ext e
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, Touches, Finset.mem_singleton,
      SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨he, w, hw, rfl⟩; exact ⟨he, hw⟩
    · rintro ⟨he, hx⟩; exact ⟨he, x, hx, rfl⟩
  rw [hEq, SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]

/-- The defect–core edges at `x` are the edges from `x` to `R`. -/
theorem card_defectCoreEdges_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (R : Finset V) :
    (defectCoreEdges G {x} R).card = (R.filter fun a => G.Adj x a).card := by
  have hEq : defectCoreEdges G {x} R = (R.filter fun a => G.Adj x a).image fun a => s(x, a) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [defectCoreEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Touches, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_union]
      constructor
      · rintro ⟨huv, ⟨w, hw, hwx⟩, hall⟩
        subst hwx
        rw [Sym2.mem_iff] at hw
        rcases hw with rfl | rfl
        · have hv := hall v (Sym2.mem_mk_right _ _)
          have hvR : v ∈ R := hv.resolve_right huv.ne.symm
          exact ⟨v, ⟨hvR, huv⟩, rfl⟩
        · have hu := hall u (Sym2.mem_mk_left _ _)
          have huR : u ∈ R := hu.resolve_right huv.ne
          exact ⟨u, ⟨huR, huv.symm⟩, Sym2.eq_swap⟩
      · rintro ⟨a, ⟨haR, hxa⟩, hEq⟩
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨hxa, ⟨x, Sym2.mem_mk_left _ _, rfl⟩, ?_⟩
          intro w hw
          rw [Sym2.mem_iff] at hw
          rcases hw with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl haR
        · refine ⟨hxa.symm, ⟨x, Sym2.mem_mk_right _ _, rfl⟩, ?_⟩
          intro w hw
          rw [Sym2.mem_iff] at hw
          rcases hw with rfl | rfl
          · exact Or.inl haR
          · exact Or.inr rfl
  rw [hEq, Finset.card_image_of_injective]
  intro y z h
  exact Sym2.congr_right.mp h

end Counting

/-! ### The main theorem -/

/-- **A4 at rooted defect one, with the defect–core term paid by host absorption.**

For all large `n`, let `G` be a graph on `Fin n` and `x` a vertex with `G - x` chordal.
If every order-four clique partition of `G` has at least `Q₁(n) - d` pieces,
`0 ≤ d ≤ gammaApex · n²`, then there is a clique `R ∌ x`, `|R| ≥ 2`, such that for every
set `S` of root neighbours of `x` with `|S| ≤ supplyMargin G x R a` for all `a ∈ S`,

`d_E(G, (K_R ⊔ I_{x}) ∨ I_{V∖(R∪{x})}) ≤ 16 d + 32 (ρ - |S|)`,

where `ρ` is the number of root neighbours of `x`.  No additive constant appears. -/
theorem defect_one_absorbed_stability :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n),
      (G.induce (({x}ᶜ : Finset (Fin n)) : Set (Fin n))).IsChordal →
      ∀ d : ℚ, 0 ≤ d → d ≤ gammaApex * (n : ℚ) ^ 2 →
      (∀ P : CliquePartition G, P.OrderAtMost 4 →
          (defectTarget 1 n : ℚ) - d ≤ (P.size : ℚ)) →
      ∃ R : Finset (Fin n), x ∉ R ∧ G.IsClique (R : Set (Fin n)) ∧ 2 ≤ R.card ∧
        ∀ S : Finset (Fin n), S ⊆ R.filter (fun a => G.Adj x a) →
          (∀ a ∈ S, (S.card : ℤ) ≤ supplyMargin G x R a) →
          (PaperIV.EditMetric.editDist G.edgeFinset
              (graphEdgeSupport (defSplitGraph R {x} ({x}ᶜ \ R))) : ℚ) ≤
            16 * d + 32 * (((R.filter fun a => G.Adj x a).card : ℚ) - S.card) := by
  classical
  obtain ⟨Nst, hst⟩ := chordal_near_partition
  refine ⟨Nst + ⌈8 / PaperIV.IntegralStability.gamma⌉₊ + 3, ?_⟩
  intro n hn G _ x hch d hd0 hdle hyp
  set D : Finset (Fin n) := {x} with hDdef
  have hDs : D.card = 1 := Finset.card_singleton x
  have hgam := PaperIV.IntegralStability.gamma_pos
  set n' := (Dᶜ).card with hn'
  have hn'eq : n' = n - 1 := by rw [hn', Finset.card_compl, Fintype.card_fin, hDs]
  have hn'st : Nst ≤ n' := by omega
  -- the enumeration of `V ∖ {x}`
  let e : Fin n' ↪ Fin n := ((Dᶜ).orderEmbOfFin hn'.symm).toEmbedding
  have he : ∀ y, y ∉ D ↔ ∃ a, e a = y := by
    intro y
    have hr := Finset.range_orderEmbOfFin (Dᶜ) hn'.symm
    constructor
    · intro hy
      have hy' : y ∈ Set.range ((Dᶜ).orderEmbOfFin hn'.symm) := by
        rw [hr]; simpa using hy
      obtain ⟨a, ha⟩ := hy'
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (Dᶜ) hn'.symm a)
  have heD : ∀ a, e a ∉ D := fun a => (he (e a)).2 ⟨a, rfl⟩
  let H : SimpleGraph (Fin n') := G.comap e
  haveI : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (G.Adj (e a) (e b)))
  have hH : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b) := fun a b => Iff.rfl
  have hHch : PaperIV.FarRounding.IsChordal H := by
    let f' : Fin n' ↪ ((Dᶜ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨fun a => ⟨e a, by simpa using heD a⟩,
        fun a b h => e.injective (congrArg Subtype.val h)⟩
    exact hch.comap f' H (fun a b => Iff.rfl)
  -- the edges at `x`
  set T := G.edgeFinset.filter (Touches D) with hTdef
  have hTdeg : T.card = (G.neighborFinset x).card := card_touch_singleton G x
  have hTle : (T.card : ℚ) ≤ n := by
    have h : T.card ≤ D.card * Fintype.card (Fin n) := card_touch_le G D
    rw [hDs, Fintype.card_fin, one_mul] at h
    have : T.card ≤ n := h
    exact_mod_cast this
  -- the avoiding graph and the push of partitions
  have hG0 : ∀ u v, (avoidPart G D).Adj u v ↔ G.Adj u v ∧ u ≠ x ∧ v ≠ x := by
    intro u v
    show (G.Adj u v ∧ u ∉ D ∧ v ∉ D) ↔ _
    simp [hDdef]
  have hext : ∀ Q : CliquePartition H, Q.OrderAtMost 4 →
      (defectTarget 1 n : ℚ) - d - T.card ≤ (Q.size : ℚ) := by
    intro Q hQ
    obtain ⟨Q0, hQ04, hQ0s⟩ := exists_push_partition G D e he H hH Q hQ
    obtain ⟨P, hP4, hPs⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
      G (avoidPart G D) (avoidPart_le G D) Q0 hQ04
    rw [sdiff_avoidPart] at hPs
    have h1 := hyp P hP4
    have h2 : (P.size : ℚ) ≤ (Q0.size : ℚ) + T.card := by exact_mod_cast hPs
    rw [hQ0s] at h2
    linarith
  -- the chordal deficit
  set δ : ℚ := d + T.card - defectTarget 1 n + PaperIV.targetSize n' with hδdef
  have hTn' : PaperIV.targetSize n' ≤ defectTarget 1 n := by
    have h1 := targetSize_mono (show n' ≤ n by omega)
    have h2 := targetSize_le_defectTarget 1 n (by omega)
    rw [farRounding_targetSize_eq] at h2
    omega
  have hTn'Q : (PaperIV.targetSize n' : ℚ) ≤ (defectTarget 1 n : ℚ) := by exact_mod_cast hTn'
  have hceil : 8 ≤ PaperIV.IntegralStability.gamma * n := by
    have h1 : 8 / PaperIV.IntegralStability.gamma ≤
        (⌈8 / PaperIV.IntegralStability.gamma⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : (⌈8 / PaperIV.IntegralStability.gamma⌉₊ : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast (show ⌈8 / PaperIV.IntegralStability.gamma⌉₊ ≤ n by omega)
    rw [div_le_iff₀ hgam] at h1
    nlinarith
  have hn'Q : (n' : ℚ) = (n : ℚ) - 1 := by rw [hn'eq, Nat.cast_sub (by omega)]; simp
  have hsnQ : 2 ≤ (n : ℚ) := by exact_mod_cast (show 2 ≤ n by omega)
  have hδle : δ ≤ PaperIV.IntegralStability.gamma * (n' : ℚ) ^ 2 := by
    have hA : δ ≤ d + n := by rw [hδdef]; linarith
    have hB : (n : ℚ) ^ 2 / 4 ≤ (n' : ℚ) ^ 2 := by
      rw [hn'Q]; nlinarith
    have hC : (n : ℚ) ≤ PaperIV.IntegralStability.gamma * (n : ℚ) ^ 2 / 8 := by
      have hn0 : (0 : ℚ) ≤ n := by positivity
      nlinarith
    have hD : d ≤ PaperIV.IntegralStability.gamma * (n : ℚ) ^ 2 / 8 := by
      unfold gammaApex at hdle; linarith
    nlinarith
  -- the near branch on the induced graph
  obtain ⟨R', hR'cl, hR'2, Q, hQ4, hQle⟩ :=
    hst n' hn'st H hHch δ hδle (fun Q hQ => by have := hext Q hQ; linarith)
  set R : Finset (Fin n) := R'.map e with hRdef
  have hRD : Disjoint R D := by
    rw [Finset.disjoint_left]
    intro y hy
    rw [hRdef, Finset.mem_map] at hy
    obtain ⟨a, -, rfl⟩ := hy
    exact heD a
  have hxR : x ∉ R := fun h => Finset.disjoint_left.mp hRD h (Finset.mem_singleton_self x)
  have hRcl : G.IsClique (R : Set (Fin n)) := by
    intro y hy z hz hyz
    rw [Finset.mem_coe, hRdef, Finset.mem_map] at hy hz
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := hz
    exact (hH a b).1 (hR'cl ha hb (fun h => hyz (h ▸ rfl)))
  have hRcard : R.card = R'.card := Finset.card_map _
  refine ⟨R, hxR, hRcl, by rw [hRcard]; exact hR'2, ?_⟩
  intro S hS hSmargin
  -- absorption on the pushed near partition
  obtain ⟨Q0, hQ04, hQ0s⟩ := exists_push_partition G D e he H hH Q hQ4
  have hSR : S ⊆ R := fun a ha => (Finset.mem_filter.mp (hS ha)).1
  have hSx : ∀ a ∈ S, G.Adj x a := fun a ha => (Finset.mem_filter.mp (hS ha)).2
  obtain ⟨Qg, hQg4, hQgs⟩ :=
    exists_absorbed_partition_of_margin hG0 hxR Q0 hQ04 S hSR hSx hSmargin
  have hQgmin := hyp Qg hQg4
  -- the comparator and its trace on `V ∖ {x}`
  set C := defSplitGraph R D (Dᶜ \ R) with hCdef
  let S' : SimpleGraph (Fin n') := splitGraph R' (Finset.univ \ R')
  have hSadj : ∀ a b, S'.Adj a b ↔ C.Adj (e a) (e b) := by
    intro a b
    have h1 : ∀ c, e c ∈ R ↔ c ∈ R' := fun c => by rw [hRdef, Finset.mem_map' e]
    have h2 : ∀ c, e c ∈ R ∪ D ↔ c ∈ R' := fun c => by
      rw [Finset.mem_union, h1]; exact ⟨fun h => h.resolve_right (heD c), Or.inl⟩
    have h3 : ∀ c, e c ∈ Dᶜ \ R ↔ c ∈ Finset.univ \ R' := fun c => by
      rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_compl, h1]
      exact ⟨fun h => ⟨Finset.mem_univ _, h.2⟩, fun h => ⟨heD c, h.2⟩⟩
    have h4 : e a ≠ e b ↔ a ≠ b := e.injective.ne_iff
    show (splitGraph R' (Finset.univ \ R')).Adj a b ↔
      (defSplitGraph R D (Dᶜ \ R)).Adj (e a) (e b)
    rw [splitGraph_adj_iff, defSplitGraph_adj_iff, h4, h1, h1, h2, h2, h3, h3]
  have hinside := card_symmDiff_filter_not_touch G C D e he H S' hH hSadj
  have hsplit := PaperIV.SplitEditIdentity.editDist_split_eq H hR'cl
  rw [graphEdgeSupport_eq_edgeFinset] at hsplit
  set CT := C.edgeFinset.filter (Touches D) with hCTdef
  have hrho : (T \ CT).card = (R.filter fun a => G.Adj x a).card := by
    rw [hTdef, hCTdef, touch_sdiff_eq_defectCoreEdges G hRD,
      card_defectCoreEdges_singleton G x R]
  have hCTcard : CT.card = 1 * (n' - R'.card) := by
    rw [hCTdef, card_comparator_touch hRD, hDs, Finset.card_sdiff_of_subset, hRcard]
    intro y hy
    rw [hRdef, Finset.mem_map] at hy
    obtain ⟨a, -, rfl⟩ := hy
    exact Finset.mem_compl.mpr (heD a)
  have hbal : T.card + (CT \ T).card = (T \ CT).card + CT.card := by
    have h1 := Finset.card_sdiff_add_card T CT
    have h2 := Finset.card_sdiff_add_card CT T
    rw [Finset.union_comm] at h2
    omega
  have hdist : PaperIV.EditMetric.editDist G.edgeFinset (graphEdgeSupport C) =
      (T \ CT).card + (CT \ T).card +
        ((PaperIV.RootVocab.outsideEdges H R').card +
          PaperIV.RootVocab.missingIncidences H R') := by
    rw [graphEdgeSupport_eq_edgeFinset, PaperIV.EditMetric.editDist,
      ← Finset.card_filter_add_card_filter_not (p := Touches D), symmDiff_filter_touch,
      card_symmDiff_eq, hinside, ← hsplit, PaperIV.EditMetric.editDist]
  -- the signed ledger
  have hk : R'.card ≤ n' := by
    have := Finset.card_le_univ R'
    simpa using this
  have hval := splitBaseline_add_links_le_defectTarget (n := n) (s := 1) (by omega) R'.card
  rw [← hn'eq] at hval
  have hbalQ : (T.card : ℚ) + ((CT \ T).card : ℚ) =
      ((T \ CT).card : ℚ) + ((n' : ℚ) - R'.card) := by
    have := hbal
    rw [hCTcard, one_mul] at this
    have h' : ((T.card + (CT \ T).card : ℕ) : ℚ) =
        (((T \ CT).card + (n' - R'.card) : ℕ) : ℚ) := by rw [this]
    push_cast [Nat.cast_sub hk] at h'
    linarith
  have hQgQ : (Qg.size : ℚ) + 2 * (S.card : ℚ) = (Q.size : ℚ) + (T.card : ℚ) := by
    rw [hTdeg, ← hQ0s]
    exact_mod_cast hQgs
  show (PaperIV.EditMetric.editDist G.edgeFinset (graphEdgeSupport C) : ℚ) ≤ _
  rw [hdist, ← hrho]
  push_cast
  have hm0 : (0 : ℚ) ≤ ((PaperIV.RootVocab.outsideEdges H R').card : ℚ) := Nat.cast_nonneg _
  have hA0 : (0 : ℚ) ≤ (PaperIV.RootVocab.missingIncidences H R' : ℚ) := Nat.cast_nonneg _
  have hmu0 : (0 : ℚ) ≤ ((CT \ T).card : ℚ) := Nat.cast_nonneg _
  have hrho0 : (0 : ℚ) ≤ ((T \ CT).card : ℚ) := Nat.cast_nonneg _
  rw [Nat.cast_one, one_mul] at hval
  linarith

/-- **Linear stability when the host supply covers the root edges of `x`.**  In the
situation of `defect_one_absorbed_stability`, if every root neighbour `a` of `x` has
host-supply margin at least `ρ = |N_R(x)|`, then `d_E ≤ 16 d`; for `d = 0` the graph `G`
**is** the comparator. -/
theorem defect_one_linear_stability_of_supply :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n),
      (G.induce (({x}ᶜ : Finset (Fin n)) : Set (Fin n))).IsChordal →
      ∀ d : ℚ, 0 ≤ d → d ≤ gammaApex * (n : ℚ) ^ 2 →
      (∀ P : CliquePartition G, P.OrderAtMost 4 →
          (defectTarget 1 n : ℚ) - d ≤ (P.size : ℚ)) →
      ∃ R : Finset (Fin n), x ∉ R ∧ G.IsClique (R : Set (Fin n)) ∧ 2 ≤ R.card ∧
        ((∀ a ∈ R, G.Adj x a →
            (((R.filter fun a => G.Adj x a).card : ℕ) : ℤ) ≤ supplyMargin G x R a) →
          (PaperIV.EditMetric.editDist G.edgeFinset
              (graphEdgeSupport (defSplitGraph R {x} ({x}ᶜ \ R))) : ℚ) ≤ 16 * d ∧
          (d = 0 → G.edgeFinset = graphEdgeSupport (defSplitGraph R {x} ({x}ᶜ \ R)))) := by
  obtain ⟨N, hN⟩ := defect_one_absorbed_stability
  refine ⟨N, ?_⟩
  intro n hn G _ x hch d hd0 hdle hyp
  obtain ⟨R, hxR, hRcl, hR2, hbound⟩ := hN n hn G x hch d hd0 hdle hyp
  refine ⟨R, hxR, hRcl, hR2, fun hsup => ?_⟩
  have h := hbound (R.filter fun a => G.Adj x a) Finset.Subset.rfl (fun a ha => by
    have ha' := Finset.mem_filter.mp ha
    exact hsup a ha'.1 ha'.2)
  have h16 : (PaperIV.EditMetric.editDist G.edgeFinset
      (graphEdgeSupport (defSplitGraph R {x} ({x}ᶜ \ R))) : ℚ) ≤ 16 * d := by
    simpa using h
  refine ⟨h16, fun hd => ?_⟩
  rw [hd, mul_zero] at h16
  have h0 : PaperIV.EditMetric.editDist G.edgeFinset
      (graphEdgeSupport (defSplitGraph R {x} ({x}ᶜ \ R))) = 0 := by
    have : (PaperIV.EditMetric.editDist G.edgeFinset
      (graphEdgeSupport (defSplitGraph R {x} ({x}ᶜ \ R))) : ℚ) ≤ 0 := h16
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
  unfold PaperIV.EditMetric.editDist at h0
  rw [Finset.card_eq_zero, ← Finset.bot_eq_empty, symmDiff_eq_bot] at h0
  exact h0

end A4S1.DefectOneAbsorbed
