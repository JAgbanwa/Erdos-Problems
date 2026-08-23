/-
# The cover-down step, derived from the **repaired** fused interface.

This is `BKLO/CoverDownFused.lean` redone against `BKLO.ReservoirClauseR`.  Two things change.

* The link-cover clause of the repaired interface is applied to link systems satisfying the extra
  *global multiplicity* bound, and that bound is **available here**: a vertex `a ∈ W'` is added to
  the link of `u` only when the crossing edge `s(u, a)` survives the nibble, so the number of such
  `u` is at most the leftover degree `η|W|` at `a`.  (Without this bound the clause is false;
  see `BKLO.not_reservoirClauseCoDense`.)
* The conclusion carries the extra damage bound at the scale of the protected level `W''`, which
  the repaired link cover supplies and which is what keeps the between-levels density of the vortex
  alive from one level to the next.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirRepaired

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem star_injective_left (a : V) : Function.Injective (fun x : V => s(x, a)) := by
  intro x y h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exact h1.trans h2

/-! ### The cover-down step, derived -/

/-- **One cover-down step, derived from the reservoir.**

`F` is a triangle-divisible edge set spanned by `W`; `R ⊆ F` is a crossing reservoir between
`W \ W'` and `W'` with abundant common apexes; `P₀` is the output of the nibble on `F` minus the
reservoir minus the edges inside `W'`, with leftover of maximum degree at most `η|W|`; and every
admissible residual link system admits a link cover with damage `γ`.

Then `F` is covered by an edge-disjoint family of triangles down to a remainder inside `W'`, no
edge of `F` inside `W''` is touched, and each vertex of `W'` loses at most `γ|W'|` edges inside
`W'`.  This is exactly the conclusion of the (false, because reservoir-free) input
`BKLO.CoverDownK3`, now *proved* in the presence of the reservoir. -/
theorem coverDown_of_reservoirR {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {η γ : ℝ}
    {P₀ : Finset (Finset V)}
    (hW''W' : W'' ⊆ W')
    (hFW : F ⊆ cliqueEdges W) (hdiv : TriDivisible F)
    (hRF : R ⊆ F) (hRcross : IsCrossing W W' R)
    (hapex : ∀ u ∈ W \ W', ∀ v ∈ W \ W', 2 * η * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ))
    (hlink : ∀ X : V → Finset V, (∀ u ∈ W \ W', X u ⊆ W') →
        (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
        (∀ u ∈ W \ W', Even (X u).card) →
        (∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
          ≤ 2 * η * (W.card : ℝ)) →
        ∃ Q : Finset (Finset V), IsLinkCoverR F W' W'' (W \ W') X γ Q)
    (hP₀ : TriFamilyIn (F \ (R ∪ cliqueEdges W')) P₀)
    (hP₀deg : ∀ v : V,
      (edeg ((F \ (R ∪ cliqueEdges W')) \ famEdges P₀) v : ℝ) ≤ η * (W.card : ℝ)) :
    ∃ P : Finset (Finset V), TriFamilyIn F P ∧
      F \ famEdges P ⊆ cliqueEdges W' ∧
      F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
      (∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ)) ∧
      ∀ v ∈ W', ((resLink F W'' v).card : ℝ)
        ≤ ((resLink (F \ famEdges P) W'' v).card : ℝ) + γ * (W''.card : ℝ) := by
  classical
  set Fp : Finset (Sym2 V) := F \ (R ∪ cliqueEdges W') with hFpdef
  set L₀ : Finset (Sym2 V) := Fp \ famEdges P₀ with hL₀def
  set L : Finset (Sym2 V) := L₀.filter (fun e => ∀ a ∈ W', a ∉ e) with hLdef
  have hFpF : Fp ⊆ F := Finset.sdiff_subset
  have hL₀Fp : L₀ ⊆ Fp := Finset.sdiff_subset
  have hLL₀ : L ⊆ L₀ := Finset.filter_subset _ _
  have hLF : L ⊆ F := (hLL₀.trans hL₀Fp).trans hFpF
  have hRW' : Disjoint R (cliqueEdges W') := disjoint_cliqueEdges_of_isCrossing hRcross
  have hRother : ∀ u x : V, s(u, x) ∈ R → u ∉ W' → x ∈ W' :=
    fun u x h hu => isCrossing_other hRcross h hu
  have hLW' : ∀ e ∈ L, ∀ a ∈ W', a ∉ e := fun e he => (Finset.mem_filter.1 he).2
  have hFpR : ∀ e ∈ Fp, e ∉ R := by
    intro e he
    exact fun hR => (Finset.mem_sdiff.1 he).2 (Finset.mem_union_left _ hR)
  have hFpW' : ∀ e ∈ Fp, e ∉ cliqueEdges W' := by
    intro e he
    exact fun hR => (Finset.mem_sdiff.1 he).2 (Finset.mem_union_right _ hR)
  have hLR : Disjoint L R :=
    Finset.disjoint_left.2 fun e he hR => hFpR e (hL₀Fp (hLL₀ he)) hR
  have hmemW : ∀ e ∈ F, ∀ x, x ∈ e → x ∈ W := fun e he x hx => (mem_cliqueEdgesV.1 (hFW he)).1 x hx
  have hnd : ∀ u v : V, s(u, v) ∈ L → u ≠ v := by
    intro u v huv h
    have := (mem_cliqueEdgesV.1 (hFW (hLF huv))).2
    exact this (by simp [Sym2.isDiag_iff_proj_eq, h])
  have hLnotW' : ∀ u v : V, s(u, v) ∈ L → u ∉ W' ∧ v ∉ W' := by
    intro u v huv
    exact ⟨fun h => hLW' _ huv u h (by simp), fun h => hLW' _ huv v h (by simp)⟩
  have hLdeg : ∀ u : V, (edeg L u : ℝ) ≤ η * (W.card : ℝ) := by
    intro u
    refine le_trans ?_ (hP₀deg u)
    exact_mod_cast edeg_mono hLL₀ u
  -- the greedy cover of the leftover avoiding `W'`
  have hcod : ∀ u v : V, s(u, v) ∈ L → edeg L u + edeg L v ≤ (apexes R W' u v).card := by
    intro u v huv
    have huW : u ∈ W := hmemW _ (hLF huv) u (by simp)
    have hvW : v ∈ W := hmemW _ (hLF huv) v (by simp)
    have hu' := (hLnotW' u v huv).1
    have hv' := (hLnotW' u v huv).2
    have h := hapex u (Finset.mem_sdiff.2 ⟨huW, hu'⟩) v (Finset.mem_sdiff.2 ⟨hvW, hv'⟩)
    have h1 := hLdeg u
    have h2 := hLdeg v
    have : ((edeg L u + edeg L v : ℕ) : ℝ) ≤ ((apexes R W' u v).card : ℝ) := by
      push_cast
      linarith only [h, h1, h2]
    exact_mod_cast this
  obtain ⟨P₁, hP₁3, hP₁sub, hP₁disj, hP₁cov⟩ :=
    exists_coverDown_family W' L.card L R le_rfl hLR hnd hLnotW' hcod
  have hfam₁ : famEdges P₁ ⊆ L ∪ R := by
    intro e he
    obtain ⟨t, ht, het⟩ := exists_triangle_of_mem_famEdges he
    exact hP₁sub t ht het
  have hfam₀ : famEdges P₀ ⊆ Fp := famEdges_subset_of_triFamilyIn hP₀
  set Pc : Finset (Finset V) := P₀ ∪ P₁ with hPcdef
  have hfamPc : famEdges Pc = famEdges P₀ ∪ famEdges P₁ := famEdges_union _ _
  have hP₀F : TriFamilyIn F P₀ := hP₀.mono hFpF
  have hP₁' : TriFamilyIn (F \ famEdges P₀) P₁ := by
    refine ⟨hP₁3, ?_, hP₁disj⟩
    intro t ht e he
    have heLR := hP₁sub t ht he
    refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
    · rcases Finset.mem_union.1 heLR with h | h
      exacts [hLF h, hRF h]
    · intro hP0
      rcases Finset.mem_union.1 heLR with h | h
      · exact (Finset.mem_sdiff.1 (hLL₀ h)).2 hP0
      · exact hFpR _ (hfam₀ hP0) h
  have hPcF : TriFamilyIn F Pc := triFamilyIn_union hP₀F hP₁'
  -- the family so far touches no edge inside `W'`
  have hPcW' : Disjoint (famEdges Pc) (cliqueEdges W') := by
    refine Finset.disjoint_left.2 fun e he he' => ?_
    rw [hfamPc] at he
    rcases Finset.mem_union.1 he with h | h
    · exact hFpW' _ (hfam₀ h) he'
    · rcases Finset.mem_union.1 (hfam₁ h) with h' | h'
      · obtain ⟨hmem, hnd'⟩ := mem_cliqueEdgesV.1 he'
        induction e using Sym2.ind with
        | _ x y => exact hLW' _ h' x (hmem x (by simp)) (by simp)
      · exact (Finset.disjoint_left.1 hRW' h') he'
  -- the residual link system
  set X : V → Finset V := fun u => W'.filter (fun a => s(u, a) ∈ F ∧ s(u, a) ∉ famEdges Pc)
    with hXdef
  have hmemX : ∀ u a : V, a ∈ X u ↔ a ∈ W' ∧ s(u, a) ∈ F ∧ s(u, a) ∉ famEdges Pc := by
    intro u a; simp [hXdef]
  have hstar : ∀ u ∈ W \ W',
      (F \ famEdges Pc).filter (fun e => u ∈ e) = (X u).image (fun a => s(u, a)) := by
    intro u hu
    have hu' : u ∉ W' := (Finset.mem_sdiff.1 hu).2
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨heF, hePc⟩, hue⟩
      -- write `e = s(u, z)`
      obtain ⟨z, rfl⟩ : ∃ z, e = s(u, z) := by
        induction e using Sym2.ind with
        | _ x y =>
          rcases Sym2.mem_iff.1 hue with rfl | rfl
          · exact ⟨y, rfl⟩
          · exact ⟨x, Sym2.eq_swap⟩
      have hz : z ∈ W' := by
        by_contra hzW'
        have h1 : s(u, z) ∉ cliqueEdges W' := by
          intro hc
          exact hu' ((mem_cliqueEdgesV.1 hc).1 u (by simp))
        have h2 : s(u, z) ∉ R := fun hR => hzW' (hRother u z hR hu')
        have h3 : s(u, z) ∈ Fp := by
          refine Finset.mem_sdiff.2 ⟨heF, ?_⟩
          intro hc
          rcases Finset.mem_union.1 hc with h | h
          exacts [h2 h, h1 h]
        have h4 : s(u, z) ∈ L₀ := by
          refine Finset.mem_sdiff.2 ⟨h3, fun hc => hePc ?_⟩
          rw [hfamPc]
          exact Finset.mem_union_left _ hc
        have h5 : s(u, z) ∈ L := by
          refine Finset.mem_filter.2 ⟨h4, ?_⟩
          intro a ha hae
          rcases Sym2.mem_iff.1 hae with rfl | rfl
          exacts [hu' ha, hzW' ha]
        refine hePc ?_
        rw [hfamPc]
        exact Finset.mem_union_right _ (hP₁cov h5)
      exact ⟨z, (hmemX u z).2 ⟨hz, heF, hePc⟩, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨-, haF, haPc⟩ := (hmemX u a).1 ha
      exact ⟨⟨haF, haPc⟩, by simp⟩
  have hXcard : ∀ u ∈ W \ W', (X u).card = edeg (F \ famEdges Pc) u := by
    intro u hu
    rw [edeg, hstar u hu, card_image_star]
  -- the five hypotheses of the link-cover clause
  have hXsub : ∀ u ∈ W \ W', X u ⊆ W' := by
    intro u _ a ha
    exact ((hmemX u a).1 ha).1
  have hXF : ∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F := by
    intro u _ a ha
    exact ((hmemX u a).1 ha).2.1
  have hXeven : ∀ u ∈ W \ W', Even (X u).card := by
    intro u hu
    rw [hXcard u hu]
    have hsub : famEdges Pc ⊆ F := famEdges_subset_of_triFamilyIn hPcF
    have hsum := edeg_sdiff_add hsub u
    obtain ⟨k, hk⟩ := even_edeg_famEdges hPcF u
    obtain ⟨m, hm⟩ : Even (edeg F u) := hdiv.1 u
    refine ⟨(edeg (F \ famEdges Pc) u) / 2, ?_⟩
    omega
  have hXminus : ∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ) ≤ 2 * η * (W.card : ℝ) := by
    intro u hu
    have hu' : u ∉ W' := (Finset.mem_sdiff.1 hu).2
    have hsub : ((X u \ resLink R W' u).image (fun a => s(u, a))) ⊆
        L₀.filter (fun e => u ∈ e) := by
      intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨haX, haR⟩ := Finset.mem_sdiff.1 ha
      obtain ⟨haW', haF, haPc⟩ := (hmemX u a).1 haX
      have hnotR : s(u, a) ∉ R := fun hR => haR (mem_resLink.2 ⟨haW', hR⟩)
      have h1 : s(u, a) ∉ cliqueEdges W' := by
        intro hc
        exact hu' ((mem_cliqueEdgesV.1 hc).1 u (by simp))
      have h3 : s(u, a) ∈ Fp := by
        refine Finset.mem_sdiff.2 ⟨haF, ?_⟩
        intro hc
        rcases Finset.mem_union.1 hc with h | h
        exacts [hnotR h, h1 h]
      refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨h3, fun hc => haPc ?_⟩, by simp⟩
      rw [hfamPc]
      exact Finset.mem_union_left _ hc
    have hcard : (X u \ resLink R W' u).card ≤ edeg L₀ u := by
      calc (X u \ resLink R W' u).card
          = ((X u \ resLink R W' u).image (fun a => s(u, a))).card := (card_image_star _ _).symm
        _ ≤ edeg L₀ u := Finset.card_le_card hsub
    have h2 : ((edeg L₀ u : ℕ) : ℝ) ≤ η * (W.card : ℝ) := hP₀deg u
    have h3 : ((X u \ resLink R W' u).card : ℝ) ≤ (edeg L₀ u : ℝ) := by exact_mod_cast hcard
    have hη0 : (0 : ℝ) ≤ η * (W.card : ℝ) :=
      le_trans (by positivity : (0:ℝ) ≤ (edeg L₀ u : ℝ)) h2
    linarith only [h2, h3]
  have hXplus : ∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ) ≤ 2 * η * (W.card : ℝ) := by
    intro u hu
    have hu' : u ∉ W' := (Finset.mem_sdiff.1 hu).2
    have hsub : ((resLink R W' u \ X u).image (fun a => s(u, a))) ⊆
        (famEdges P₁).filter (fun e => u ∈ e) := by
      intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨haR, haX⟩ := Finset.mem_sdiff.1 ha
      obtain ⟨haW', haRmem⟩ := mem_resLink.1 haR
      have haF : s(u, a) ∈ F := hRF haRmem
      have hPc : s(u, a) ∈ famEdges Pc := by
        by_contra hc
        exact haX ((hmemX u a).2 ⟨haW', haF, hc⟩)
      rw [hfamPc] at hPc
      rcases Finset.mem_union.1 hPc with h | h
      · exact absurd haRmem (hFpR _ (hfam₀ h))
      · exact Finset.mem_filter.2 ⟨h, by simp⟩
    have hcard1 : (resLink R W' u \ X u).card ≤ edeg (famEdges P₁) u := by
      calc (resLink R W' u \ X u).card
          = ((resLink R W' u \ X u).image (fun a => s(u, a))).card := (card_image_star _ _).symm
        _ ≤ edeg (famEdges P₁) u := Finset.card_le_card hsub
    have hcard2 : edeg (famEdges P₁) u ≤ 2 * (P₁.filter (fun t => u ∈ t)).card :=
      edeg_famEdges_le_two_mul_card_filter P₁ hP₁3 u
    have hcard3 : (P₁.filter (fun t => u ∈ t)).card ≤ edeg L u :=
      card_triangles_at_le_edeg hP₁3 hP₁sub hP₁disj hLW' hRother hRW' hu'
    have h4 : ((resLink R W' u \ X u).card : ℝ) ≤ 2 * (edeg L u : ℝ) := by
      have : (resLink R W' u \ X u).card ≤ 2 * edeg L u := by omega
      exact_mod_cast this
    have h5 := hLdeg u
    linarith only [h4, h5]
  have hXmult : ∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * η * (W.card : ℝ) := by
    intro a haW'
    have hsub : (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).image
        (fun u => s(u, a))) ⊆ L₀.filter (fun e => a ∈ e) := by
      intro e he
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨huW, hua⟩ := Finset.mem_filter.1 hu
      have hu' : u ∉ W' := (Finset.mem_sdiff.1 huW).2
      obtain ⟨haX, haR⟩ := Finset.mem_sdiff.1 hua
      obtain ⟨-, haF, haPc⟩ := (hmemX u a).1 haX
      have hnotR : s(u, a) ∉ R := fun hR => haR (mem_resLink.2 ⟨haW', hR⟩)
      have h1 : s(u, a) ∉ cliqueEdges W' := fun hc =>
        hu' ((mem_cliqueEdgesV.1 hc).1 u (by simp))
      have h3 : s(u, a) ∈ Fp := by
        refine Finset.mem_sdiff.2 ⟨haF, ?_⟩
        intro hc
        rcases Finset.mem_union.1 hc with h | h
        exacts [hnotR h, h1 h]
      refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨h3, fun hc => haPc ?_⟩, by simp⟩
      rw [hfamPc]
      exact Finset.mem_union_left _ hc
    have hcard : ((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card ≤ edeg L₀ a := by
      calc ((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card
          = (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).image
              (fun u => s(u, a))).card :=
            (Finset.card_image_of_injective _ (star_injective_left a)).symm
        _ ≤ edeg L₀ a := Finset.card_le_card hsub
    have h2 : ((edeg L₀ a : ℕ) : ℝ) ≤ η * (W.card : ℝ) := hP₀deg a
    have h3 : (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
        ≤ (edeg L₀ a : ℝ) := by exact_mod_cast hcard
    have hη0 : (0 : ℝ) ≤ η * (W.card : ℝ) :=
      le_trans (by positivity : (0:ℝ) ≤ (edeg L₀ a : ℝ)) h2
    linarith only [h2, h3]
  obtain ⟨Q, ⟨hQfam, hQcov, hQsub, hQW'', hQdam⟩, hQnext⟩ :=
    hlink X hXsub hXF hXeven hXminus hXplus hXmult
  -- the three families compose
  have hQPc : ∀ t ∈ Q, Disjoint (cliqueEdges t) (famEdges Pc) := by
    intro t ht
    refine Finset.disjoint_left.2 fun e he hePc => ?_
    have heQ : e ∈ famEdges Q := Finset.mem_biUnion.2 ⟨t, ht, he⟩
    rcases Finset.mem_union.1 (hQsub heQ) with h | h
    · obtain ⟨u, hu, a, ha, rfl⟩ := mem_crossStars.1 h
      exact ((hmemX u a).1 ha).2.2 hePc
    · exact (Finset.disjoint_left.1 hPcW' hePc) h
  have hQF : TriFamilyIn (F \ famEdges Pc) Q := triFamilyIn_sdiff hQfam hQPc
  refine ⟨Pc ∪ Q, triFamilyIn_union hPcF hQF, ?_, ?_, ?_, ?_⟩
  · -- the leftover lies inside `W'`
    intro e he
    obtain ⟨heF, heP⟩ := Finset.mem_sdiff.1 he
    rw [famEdges_union] at heP
    have hePc : e ∉ famEdges Pc := fun h => heP (Finset.mem_union_left _ h)
    have heQ : e ∉ famEdges Q := fun h => heP (Finset.mem_union_right _ h)
    by_contra hcl
    -- some endpoint of `e` lies outside `W'`
    obtain ⟨u, hue, hu'⟩ : ∃ u, u ∈ e ∧ u ∉ W' := by
      by_contra hc
      push_neg at hc
      exact hcl (mem_cliqueEdgesV.2 ⟨hc, (mem_cliqueEdgesV.1 (hFW heF)).2⟩)
    have huW : u ∈ W := hmemW _ heF u hue
    have hu : u ∈ W \ W' := Finset.mem_sdiff.2 ⟨huW, hu'⟩
    have hmem : e ∈ (F \ famEdges Pc).filter (fun e => u ∈ e) :=
      Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨heF, hePc⟩, hue⟩
    rw [hstar u hu] at hmem
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hmem
    exact heQ (hQcov (crossStars_mem hu ha))
  · -- no edge inside `W''` is touched
    intro e he
    obtain ⟨heF, heW''⟩ := Finset.mem_inter.1 he
    refine Finset.mem_sdiff.2 ⟨heF, ?_⟩
    rw [famEdges_union]
    intro hc
    rcases Finset.mem_union.1 hc with h | h
    · exact (Finset.disjoint_left.1 hPcW' h) (cliqueEdges_mono hW''W' heW'')
    · exact (Finset.disjoint_left.1 hQW'' h) heW''
  · -- the damage inside `W'`
    intro v hv
    have hEsub : F ∩ cliqueEdges W' ⊆ cliqueEdges W' := Finset.inter_subset_right
    have hsplit : (F ∩ cliqueEdges W') \ (famEdges Q ∩ cliqueEdges W')
        = (F ∩ cliqueEdges W') \ famEdges Q := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have h1 : edeg (F ∩ cliqueEdges W') v
        ≤ edeg ((F ∩ cliqueEdges W') \ famEdges Q) v
          + edeg (famEdges Q ∩ cliqueEdges W') v := by
      have := edeg_le_sdiff_add_edeg (F ∩ cliqueEdges W') (famEdges Q ∩ cliqueEdges W') v
      rwa [hsplit] at this
    have h2 : (F ∩ cliqueEdges W') \ famEdges Q ⊆ F \ famEdges (Pc ∪ Q) := by
      intro e he
      obtain ⟨heE, heQ⟩ := Finset.mem_sdiff.1 he
      obtain ⟨heF, heW'⟩ := Finset.mem_inter.1 heE
      refine Finset.mem_sdiff.2 ⟨heF, ?_⟩
      rw [famEdges_union]
      intro hc
      rcases Finset.mem_union.1 hc with h | h
      · exact (Finset.disjoint_left.1 hPcW' h) heW'
      · exact heQ h
    have h3 : edeg ((F ∩ cliqueEdges W') \ famEdges Q) v ≤ edeg (F \ famEdges (Pc ∪ Q)) v :=
      edeg_mono h2 v
    have h4 := hQdam v hv
    have h1' : (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg ((F ∩ cliqueEdges W') \ famEdges Q) v : ℝ)
          + (edeg (famEdges Q ∩ cliqueEdges W') v : ℝ) := by exact_mod_cast h1
    have h3' : (edeg ((F ∩ cliqueEdges W') \ famEdges Q) v : ℝ)
        ≤ (edeg (F \ famEdges (Pc ∪ Q)) v : ℝ) := by exact_mod_cast h3
    linarith
  · -- the damage into the protected level `W''`
    intro v hv
    have hsub : resLink F W'' v ⊆
        resLink (F \ famEdges (Pc ∪ Q)) W'' v ∪ resLink (famEdges Q) W'' v := by
      intro a ha
      obtain ⟨haW'', haF⟩ := mem_resLink.1 ha
      by_cases hQe : s(v, a) ∈ famEdges Q
      · exact Finset.mem_union_right _ (mem_resLink.2 ⟨haW'', hQe⟩)
      · refine Finset.mem_union_left _ (mem_resLink.2 ⟨haW'', Finset.mem_sdiff.2 ⟨haF, ?_⟩⟩)
        rw [famEdges_union]
        intro hc
        rcases Finset.mem_union.1 hc with h | h
        · refine (Finset.disjoint_left.1 hPcW' h) (mem_cliqueEdgesV.2 ⟨?_, ?_⟩)
          · intro z hz
            rcases Sym2.mem_iff.1 hz with rfl | rfl
            exacts [hv, hW''W' haW'']
          · exact (mem_cliqueEdgesV.1 (hFW haF)).2
        · exact hQe h
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (resLink (F \ famEdges (Pc ∪ Q)) W'' v)
      (resLink (famEdges Q) W'' v)
    have h3 := hQnext v hv
    have h4 : ((resLink F W'' v).card : ℝ)
        ≤ ((resLink (F \ famEdges (Pc ∪ Q)) W'' v).card : ℝ)
          + ((resLink (famEdges Q) W'' v).card : ℝ) := by
      exact_mod_cast le_trans h1 h2
    linarith

end BKLO
