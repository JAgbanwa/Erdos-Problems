import A4S1.IndepAbsorb
import A4S1.IndepPhaseOne
import A4S1.IndepLedger

/-!
# E14, G1: the independent hosting constructor `caseA_indep`

Configuration: `V = S ⊔ H ⊔ W` (core `S`, rows `H`, exceptional vertices `W`), the core **not**
necessarily complete; only the real edges of `G[S]` are hosted.

**Construction (RD09 phases I/II plus link-usage absorption).**

1. *Absorption* (`exists_absorption_matchings`, balanced selection of
   `A4S1.PerVertexAbsorption` and greedy distinct hosts of `A4S1.HostAbsorption`): reserved
   links `M w`, triangles `{w, a, h}`.  A link `a h` is *usable* afterwards iff it is an edge and
   is not reserved.
2. *Phase I* (RD09): the padded equitable Vizing colouring of `G[H]` with `k` colours
   (`PaperIV.PaddedEquitableColouring`, classes `≤ q`), colours read in the group
   `Multiplicative (Fin k)`, an injective labelling `root` of the core, and the best of the
   `k` cyclic shifts (`exists_shift_lift_ge`, from `PaperIV.RD09FiniteAveraging`).  The core
   vertex `v` lifts the edges of its class through usable links; the lifted triangles form the
   multi-host lift of `PaperIV.MultiHostTriangleLift`.
3. *Phase II*: every edge `uv` of `G[S]` gets a host `h ∈ H` from the list of rows joined to
   `u` and `v` by usable links not spent in phase I; the lists have at least
   `b − 2τ − 4q` rows and the dyadic Galvin scheme (`PaperIV.DyadicHosting`) colours all core
   pairs; the triangles `{u, v, h}` are `A4S1.TerminalPacking.hostedTriangles`.
4. *Ledger* (`exists_partition_of_three_families`): `|Q| + 2(Σ|M w| + t + e(S)) = e(G)` with
   `2t ≥ e(H)`.

**Hypotheses (our constants).**  `σ` bounds the core non-neighbours of a row **plus `|W|`**,
`τ` the row non-neighbours of a core vertex **plus `|W|`** (one reserved link per exceptional
vertex at each end), the colours satisfy `Δ(G[H]) + 1 ≤ k`, `|S| ≤ k ≤ 2(|S| − 2σ)`, the
classes have at most `q ≥ ⌈e(H)/k⌉` edges, and the phase-II lists need
`3⌈|S|/2⌉ + 2τ + 4q ≤ |H| + 2`.

**Conclusion.**
`|Q| + e(S) + 2 Σ_w min(u_w, v_w) ≤ |S||H| + Σ_w deg w + 2|W|(|W| + ⌊√D⌋)`.
-/

namespace A4S1.Indep

open Finset A4S1.TerminalPacking PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **G1: the independent hosting constructor.** -/
theorem caseA_indep (S H W : Finset V) (hSH : Disjoint S H) (hSW : Disjoint S W)
    (hHW : Disjoint H W) (hcov : ∀ v, v ∈ S ∨ v ∈ H ∨ v ∈ W)
    (k q σ τ D : ℕ) (hk : 0 < k)
    (hσ : ∀ h ∈ H, (S.filter fun v => ¬ G.Adj h v).card + W.card ≤ σ)
    (hτ : ∀ v ∈ S, (H.filter fun h => ¬ G.Adj v h).card + W.card ≤ τ)
    (hΔ : ∀ v ∈ H, (H.filter (G.Adj v)).card + 1 ≤ k)
    (hck : S.card ≤ k) (hθ : k ≤ 2 * (S.card - 2 * σ))
    (hq : PaperIV.EquitableEdgeColouring.classCeiling (inEdges G H).card k ≤ q)
    (hb : 3 * ((S.card + 1) / 2) + 2 * τ + 4 * q ≤ H.card + 2)
    (hD : ∀ X ⊆ S, ∀ Y ⊆ H, ((X ×ˢ Y).filter fun p => ¬ G.Adj p.1 p.2).card ≤ D) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + (inEdges G S).card +
          2 * ∑ w ∈ W, min (S.filter (G.Adj w)).card (H.filter (G.Adj w)).card ≤
        S.card * H.card + ∑ w ∈ W, G.degree w + 2 * W.card * (W.card + Nat.sqrt D) := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · obtain ⟨Q, hQ4, hQ⟩ := exists_partition_of_triangles (G := G) (∅ : Finset (Finset V))
      (by simp) (by simp) (by simp)
    refine ⟨Q, hQ4, ?_⟩
    have h1 : G.edgeFinset.card = 0 := by
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro e
      induction e using Sym2.ind with | _ a b => exact isEmptyElim a
    have h2 : (inEdges G S).card = 0 := by
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro e
      induction e using Sym2.ind with | _ a b => exact isEmptyElim a
    rw [Finset.eq_empty_of_isEmpty W]
    simp only [card_empty, mul_zero, add_zero, sum_empty, h2] at hQ ⊢
    omega
  have hSH' : ∀ x, x ∈ S → x ∈ H → False := fun x h1 h2 => disjoint_left.1 hSH h1 h2
  /- 1. absorption -/
  obtain ⟨M, hM1, hM2, hM3, hM4⟩ := exists_absorption_matchings (G := G) S H D hD W
  set F := W.biUnion M with hF
  have hFcnt : ∀ z, (F.filter fun p => p.1 = z).card ≤ W.card ∧
      (F.filter fun p => p.2 = z).card ≤ W.card := card_filter_fst_biUnion_le W M hM2
  /- usable links -/
  set okL : V → V → Prop := fun v x => G.Adj v x ∧ (v, x) ∉ F with hokL
  have hFmem : ∀ w ∈ W, ∀ p ∈ M w, p ∈ F := fun w hw p hp => mem_biUnion.2 ⟨w, hw, hp⟩
  /- non-usable links at a row / at a core vertex -/
  have hbadRow : ∀ x ∈ H, (S.filter fun v => ¬ okL v x).card ≤ σ := by
    intro x hx
    have hsub : S.filter (fun v => ¬ okL v x) ⊆
        S.filter (fun v => ¬ G.Adj x v) ∪ (F.filter fun p => p.2 = x).image Prod.fst := by
      intro v hv
      rw [mem_filter] at hv
      by_cases hadj : G.Adj x v
      · have hvF : (v, x) ∈ F := by
          by_contra hn; exact hv.2 ⟨hadj.symm, hn⟩
        exact mem_union_right _ (mem_image.2 ⟨(v, x), mem_filter.2 ⟨hvF, rfl⟩, rfl⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hv.1, hadj⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le (S.filter fun v => ¬ G.Adj x v)
      ((F.filter fun p => p.2 = x).image Prod.fst)
    have h3 := card_image_le (s := F.filter fun p => p.2 = x) (f := Prod.fst)
    have h4 := (hFcnt x).2
    have h5 := hσ x hx
    omega
  have hbadCore : ∀ v ∈ S, (H.filter fun x => ¬ okL v x).card ≤ τ := by
    intro v hv
    have hsub : H.filter (fun x => ¬ okL v x) ⊆
        H.filter (fun x => ¬ G.Adj v x) ∪ (F.filter fun p => p.1 = v).image Prod.snd := by
      intro x hx
      rw [mem_filter] at hx
      by_cases hadj : G.Adj v x
      · have hvF : (v, x) ∈ F := by
          by_contra hn; exact hx.2 ⟨hadj, hn⟩
        exact mem_union_right _ (mem_image.2 ⟨(v, x), mem_filter.2 ⟨hvF, rfl⟩, rfl⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hx.1, hadj⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le (H.filter fun x => ¬ G.Adj v x)
      ((F.filter fun p => p.1 = v).image Prod.snd)
    have h3 := card_image_le (s := F.filter fun p => p.1 = v) (f := Prod.snd)
    have h4 := (hFcnt v).1
    have h5 := hτ v hv
    omega
  /- 2. phase I: colouring of the rows, labels of the core, best shift -/
  haveI : NeZero k := ⟨hk.ne'⟩
  let B := PaperIV.PaddedEquitableColouring.equitableBoundedColouringOfCard (rowGraph G H) k
    (maxDegree_rowGraph_add_one_le H k hk hΔ)
  set E := inEdges G H with hEdef
  have hGE : ∀ e, e ∈ PaperIV.Model.graphEdges (rowGraph G H) ↔ e ∈ E := by
    intro e
    change e ∈ (rowGraph G H).edgeFinset ↔ e ∈ E
    rw [edgeFinset_rowGraph]
  have hGEcard : (PaperIV.Model.graphEdges (rowGraph G H)).card = E.card := by
    change (rowGraph G H).edgeFinset.card = E.card
    rw [edgeFinset_rowGraph]
  set col : Sym2 V → Multiplicative (Fin k) := fun e => Multiplicative.ofAdd (B.colour e)
    with hcol
  have hcolProper : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → col e = col f →
      Disjoint e.toFinset f.toFinset := by
    intro e he f hf hef hc
    exact B.proper e ((hGE e).2 he) f ((hGE f).2 hf) hef (Multiplicative.ofAdd.injective hc)
  have hcolClass : ∀ j, (E.filter fun e => col e = j).card ≤ q := by
    intro j
    have heq : E.filter (fun e => col e = j) = PaperIV.ColourClasses.colourClass
        (PaperIV.Model.graphEdges (rowGraph G H)) B.colour (Multiplicative.toAdd j) := by
      ext e
      rw [PaperIV.ColourClasses.mem_colourClass, mem_filter, hGE]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h2]; rfl⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [hcol]; simp only; rw [h2]; rfl⟩
    rw [heq]
    refine (B.class_card_le _).trans ?_
    rw [hGEcard]
    exact hq
  obtain ⟨root, -, hroot⟩ := A4S1.HostAbsorption.exists_injOn_choice S
    (fun _ => (univ : Finset (Multiplicative (Fin k)))) (fun a _ => by simpa using hck)
  set ok : V → Sym2 V → Prop := fun v e => ∀ z ∈ e.toFinset, okL v z with hok
  have hc' : ∀ e ∈ E, S.card - 2 * σ ≤ (S.filter fun v => ok v e).card := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
    rw [hEdef, mk_mem_inEdges] at he
    have hsub : S ⊆ S.filter (fun v => ok v s(x, y)) ∪
        (S.filter (fun v => ¬ okL v x) ∪ S.filter (fun v => ¬ okL v y)) := by
      intro v hv
      by_cases h1 : okL v x
      · by_cases h2 : okL v y
        · refine mem_union_left _ (mem_filter.2 ⟨hv, fun z hz => ?_⟩)
          rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact h1
          · exact h2
        · exact mem_union_right _ (mem_union_right _ (mem_filter.2 ⟨hv, h2⟩))
      · exact mem_union_right _ (mem_union_left _ (mem_filter.2 ⟨hv, h1⟩))
    have h1 := card_le_card hsub
    have h2 := card_union_le (S.filter (fun v => ok v s(x, y)))
      (S.filter (fun v => ¬ okL v x) ∪ S.filter (fun v => ¬ okL v y))
    have h3 := card_union_le (S.filter (fun v => ¬ okL v x)) (S.filter (fun v => ¬ okL v y))
    have h4 := hbadRow x he.2.1
    have h5 := hbadRow y he.2.2
    omega
  obtain ⟨g, hg⟩ := exists_shift_lift_ge S E col root ok (S.card - 2 * σ) hc'
  have hcardI : Fintype.card (Multiplicative (Fin k)) = k := by simp
  rw [hcardI] at hg
  set lift := liftAt E col root ok g with hlift
  set t := ∑ v ∈ S, (lift v).card with ht
  have h2t : E.card ≤ 2 * t := by
    have hpos : 0 < S.card - 2 * σ := by omega
    have : E.card * (S.card - 2 * σ) ≤ (2 * t) * (S.card - 2 * σ) := by
      calc E.card * (S.card - 2 * σ) ≤ k * t := hg
        _ ≤ 2 * (S.card - 2 * σ) * t := Nat.mul_le_mul_right _ hθ
        _ = (2 * t) * (S.card - 2 * σ) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hliftE : ∀ v, ∀ e ∈ lift v, e ∈ E ∧ ok v e ∧ col e = root v * g⁻¹ := by
    intro v e he
    rw [hlift, liftAt, mem_filter] at he
    exact ⟨he.1, he.2.1, he.2.2⟩
  have hliftH : ∀ v, ∀ e ∈ lift v, ∀ z ∈ e, z ∈ H := by
    intro v e he z hz
    exact (mem_filter.1 (hliftE v e he).1).2 z hz
  have hliftq : ∀ v, (lift v).card ≤ q := fun v =>
    (card_le_card (liftAt_subset_class E col root ok g v)).trans (hcolClass _)
  have hliftdisj : ∀ v ∈ S, ∀ v' ∈ S, v ≠ v' → Disjoint (lift v) (lift v') :=
    fun v hv v' hv' hvv => liftAt_disjoint E col root ok g (fun h => hvv (hroot hv hv' h))
  have hMH : PaperIV.MultiHostTriangleLift.IsMultiExteriorHub G (fun i : S => (i : V))
      (fun i => lift i) :=
    { hub := fun i =>
        { edges := fun e he => by
            rw [PaperIV.Model.mem_graphEdges]
            exact SimpleGraph.mem_edgeFinset.1 (mem_filter.1 (hliftE i e he).1).1
          matching := fun e he f hf hef => hcolProper e (hliftE i e he).1 f (hliftE i f hf).1 hef
            ((hliftE i e he).2.2.trans (hliftE i f hf).2.2.symm)
          hubAdj := fun e he a ha => ((hliftE i e he).2.1 a (Sym2.mem_toFinset.2 ha)).1 }
      hostInj := Subtype.val_injective
      exterior := fun i j e he a ha h => hSH' a (h ▸ j.2) (hliftH i e he a ha)
      baseDisjoint := fun i j hij => hliftdisj i i.2 j j.2 (fun h => hij (Subtype.ext h)) }
  /- 3. phase II: lists, dyadic Galvin colouring, hosted triangles -/
  set used : V → Finset V := fun v => (lift v).biUnion Sym2.toFinset with hused
  have husedCard : ∀ v, (used v).card ≤ 2 * q := by
    intro v
    calc (used v).card ≤ ∑ e ∈ lift v, e.toFinset.card := card_biUnion_le
      _ ≤ ∑ _e ∈ lift v, 2 := sum_le_sum fun e _ => PaperIV.LiftedPieces.card_toFinset_sym2_le e
      _ = 2 * (lift v).card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * q := by have := hliftq v; omega
  set Lst : Sym2 V → Finset V := fun e =>
    H.filter fun h => ∀ z ∈ e.toFinset, okL z h ∧ h ∉ used z with hLst
  have hLstCard : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      3 * ((S.card + 1) / 2) ≤ (Lst s(u, v)).card + 2 := by
    intro u hu v hv _
    have hsub : H ⊆ Lst s(u, v) ∪ (((H.filter fun x => ¬ okL u x) ∪ used u) ∪
        ((H.filter fun x => ¬ okL v x) ∪ used v)) := by
      intro h hh
      by_cases h1 : okL u h ∧ h ∉ used u ∧ okL v h ∧ h ∉ used v
      · refine mem_union_left _ (mem_filter.2 ⟨hh, fun z hz => ?_⟩)
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact ⟨h1.1, h1.2.1⟩
        · exact ⟨h1.2.2.1, h1.2.2.2⟩
      · refine mem_union_right _ ?_
        by_cases a1 : okL u h
        · by_cases a2 : h ∈ used u
          · exact mem_union_left _ (mem_union_right _ a2)
          · by_cases a3 : okL v h
            · have a4 : h ∈ used v := by
                by_contra a4; exact h1 ⟨a1, a2, a3, a4⟩
              exact mem_union_right _ (mem_union_right _ a4)
            · exact mem_union_right _ (mem_union_left _ (mem_filter.2 ⟨hh, a3⟩))
        · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hh, a1⟩))
    have e1 := card_le_card hsub
    have e2 := card_union_le (Lst s(u, v)) (((H.filter fun x => ¬ okL u x) ∪ used u) ∪
        ((H.filter fun x => ¬ okL v x) ∪ used v))
    have e3 := card_union_le ((H.filter fun x => ¬ okL u x) ∪ used u)
        ((H.filter fun x => ¬ okL v x) ∪ used v)
    have e4 := card_union_le (H.filter fun x => ¬ okL u x) (used u)
    have e5 := card_union_le (H.filter fun x => ¬ okL v x) (used v)
    have e6 := hbadCore u hu
    have e7 := hbadCore v hv
    have e8 := husedCard u
    have e9 := husedCard v
    omega
  obtain ⟨c, hc⟩ := PaperIV.DyadicHosting.dyadic_list_colouring S Lst hLstCard
  have hcL : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u v ∈ H ∧ okL u (c u v) ∧ c u v ∉ used u ∧
      okL v (c u v) ∧ c u v ∉ used v := by
    intro u hu v hv huv
    have hm := (hc.1 u hu v hv huv.ne).2
    rw [hLst, mem_filter] at hm
    have hu' := hm.2 u (by simp)
    have hv' := hm.2 v (by simp)
    exact ⟨hm.1, hu'.1, hu'.2, hv'.1, hv'.2⟩
  have hHA : HostAssignment G S c := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv huv; exact (hc.1 u hu v hv huv.ne).1
    · intro u hu v hv huv
      obtain ⟨h1, h2, -, h4, -⟩ := hcL u hu v hv huv
      exact ⟨fun h => hSH' _ h h1, h2.1, h4.1⟩
    · intro u hu v hv v' hv' huv huv' hvv'
      exact hc.2 u hu v hv v' hv' huv.ne huv'.ne hvv'
  /- 4. the three families and the ledger -/
  set Tabs := absorptionTriangles W M with hTabs
  set TI := PaperIV.MultiHostTriangleLift.multiLiftedPacking (fun i : S => (i : V))
    (fun i => lift i) with hTI
  set TII := hostedTriangles G S c with hTII
  have hTIpack := PaperIV.MultiHostTriangleLift.isPacking_multiLiftedPacking hMH
  have hTIcard : TI.card = t := by
    rw [hTI, PaperIV.MultiHostTriangleLift.card_multiLiftedPacking hMH, ht]
    exact Finset.sum_coe_sort S (fun v => (lift v).card)
  have hTImem : ∀ K ∈ TI, ∃ v ∈ S, ∃ e ∈ lift v,
      K = PaperIV.ExteriorTriangleLift.triangle v e := by
    intro K hK
    obtain ⟨i, e, he, rfl⟩ := PaperIV.MultiHostTriangleLift.mem_multiLiftedPacking.1 hK
    exact ⟨i, i.2, e, he, rfl⟩
  have hTIclique : ∀ K ∈ TI, (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ K.card = 3 := by
    intro K hK
    refine ⟨fun a ha b hb hab => (hTIpack.pieces _ hK).clique (mem_coe.2 ha) (mem_coe.2 hb) hab,
      ?_⟩
    obtain ⟨i, e, he, rfl⟩ := PaperIV.MultiHostTriangleLift.mem_multiLiftedPacking.1 hK
    exact PaperIV.ExteriorTriangleLift.card_triangle
      (PaperIV.Model.not_isDiag_of_mem_graphEdges G ((hMH.hub i).edges e he))
      (PaperIV.ExteriorTriangleLift.notMem_of_hub (hMH.hub i) he)
  have hTIinter : ∀ K ∈ TI, ∀ L ∈ TI, K ≠ L → (K ∩ L).card ≤ 1 := by
    intro K hK L hL hKL
    have hd := hTIpack.edgeDisjoint K hK L hL hKL
    apply card_inter_le_one_of
    intro x hx y hy hxL hyL
    by_contra hxy
    exact disjoint_left.1 hd (PaperIV.Model.mem_pieceEdges_mk.2 ⟨hx, hy, hxy⟩)
      (PaperIV.Model.mem_pieceEdges_mk.2 ⟨hxL, hyL, hxy⟩)
  have hAB : ∀ K ∈ Tabs, ∀ L ∈ TI, (K ∩ L).card ≤ 1 := by
    intro K hK L hL
    obtain ⟨w, hw, p, hp, rfl⟩ := mem_absorptionTriangles.1 hK
    obtain ⟨v, hv, e, he, rfl⟩ := hTImem L hL
    obtain ⟨h1, h2, -⟩ := hM1 w hw p hp
    refine abs_inter_lift S H hSH (fun h => disjoint_left.1 hSW h hw)
      (fun h => disjoint_left.1 hHW h hw) h1 h2 hv (hliftH v e he) ?_
    intro hpe hpv
    have hok := (hliftE v e he).2.1 p.2 (Sym2.mem_toFinset.2 hpe)
    apply hok.2
    rw [← hpv]
    exact hFmem w hw p hp
  have hAC : ∀ K ∈ Tabs, ∀ L ∈ TII, (K ∩ L).card ≤ 1 := by
    intro K hK L hL
    obtain ⟨w, hw, p, hp, rfl⟩ := mem_absorptionTriangles.1 hK
    obtain ⟨u, u', hu, hu', huu, rfl⟩ := exists_of_mem_hostedTriangles hL
    obtain ⟨h1, h2, -⟩ := hM1 w hw p hp
    obtain ⟨hc1, hc2, -, hc4, -⟩ := hcL u hu u' hu' huu
    refine abs_inter_hosted S H hSH (fun h => disjoint_left.1 hSW h hw)
      (fun h => disjoint_left.1 hHW h hw) h1 h2 hu hu' hc1 ?_
    intro hpc hpu
    have hpF := hFmem w hw p hp
    rcases hpu with hpu | hpu
    · apply hc2.2; rw [← hpc, ← hpu]; exact hpF
    · apply hc4.2; rw [← hpc, ← hpu]; exact hpF
  have hBC : ∀ K ∈ TI, ∀ L ∈ TII, (K ∩ L).card ≤ 1 := by
    intro K hK L hL
    obtain ⟨v, hv, e, he, rfl⟩ := hTImem K hK
    obtain ⟨u, u', hu, hu', huu, rfl⟩ := exists_of_mem_hostedTriangles hL
    obtain ⟨hc1, -, hc3, -, hc5⟩ := hcL u hu u' hu' huu
    refine lift_inter_hosted S H hSH hv (hliftH v e he) hu hu' hc1 ?_
    intro hce hvu
    have hmem : c u u' ∈ used v := mem_biUnion.2 ⟨e, he, Sym2.mem_toFinset.2 hce⟩
    rcases hvu with hvu | hvu
    · rw [hvu] at hmem; exact hc3 hmem
    · rw [hvu] at hmem; exact hc5 hmem
  obtain ⟨Q, hQ4, hQ⟩ := exists_partition_of_three_families (G := G) Tabs TI TII
    (absorptionTriangles_clique S H W hSH hSW hHW M hM1) hTIclique
    (fun K hK => hostedTriangles_isClique hHA hK)
    (absorptionTriangles_inter S H W hSH hSW hHW M hM1 hM2 hM3) hTIinter
    (fun K hK L hL hKL => hostedTriangles_inter hHA hK hL hKL) hAB hAC hBC
  refine ⟨Q, hQ4, ?_⟩
  have hcA := card_absorptionTriangles S H W hSH hSW hHW M hM1
  have hcC := card_hostedTriangles hHA
  have hsplit := card_edgeFinset_le_parts (G := G) S H W hSH hcov
  have hcross : crossCount G S H ≤ S.card * H.card := by
    unfold crossCount; rw [← card_product]; exact card_filter_le _ _
  have hmin : ∑ w ∈ W, min (S.filter (G.Adj w)).card (H.filter (G.Adj w)).card ≤
      ∑ w ∈ W, (M w).card + W.card * (W.card + Nat.sqrt D) := by
    have := sum_le_sum hM4
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at this
    rw [mul_add]
    omega
  rw [hcA, hTIcard, hcC] at hQ
  have h2W : 2 * W.card * (W.card + Nat.sqrt D) = 2 * (W.card * (W.card + Nat.sqrt D)) := by
    ring
  rw [h2W]
  have hEH : (inEdges G H).card = E.card := rfl
  omega

end A4S1.Indep
