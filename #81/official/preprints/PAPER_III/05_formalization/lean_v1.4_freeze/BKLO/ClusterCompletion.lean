/-
# Completing a sparse reservoir to a family of edge-disjoint `K₇` clusters.

`BKLO/TriangleCompletion.lean` embeds the sparse pair-covering graph reservoir of
`BKLO/GreedyPairCover.lean` into an edge-disjoint family of *triangles*.  For the designed
reservoir of `BKLO/ClusterReservoir.lean` the same has to be done with `K₇`s: every reserved edge
must be completed to a `7`-set all of whose `21` edges are host edges and are not used by any other
cluster.

The construction is the same greedy, with an inner greedy that grows the edge `xy` to a `7`-clique
five vertices at a time: each new vertex is chosen in the common neighbourhood of the vertices
picked so far, outside the vertices already joined to them by used edges, and outside the (few)
vertices that already carry a large load.  Two ingredients are new:

* `BKLO.card_commonNbhdIn_dense` — in a host of minimum degree `(9/10+γ)|S|`, *any* seven vertices
  have at least `(3/10)|S|` common neighbours (the seven non-neighbourhoods have total size at most
  `(7/10)|S|`);
* `BKLO.exists_clique_ext` — the inner greedy, in the form of an induction on the number of
  vertices still to be added.

Everything here is `sorry`-free.  The result exported is `BKLO.clusterReservoirExistence_holds`:
`BKLO.ClusterReservoirExistence` — a sparse pair-covering cluster reservoir exists in every large
dense host.
-/
import BKLO.ClusterReservoir
import BKLO.TriangleCompletion

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Common neighbourhoods of a set of vertices -/

/-- The common neighbours, inside `S`, of all vertices of `T`. -/
def commonNbhdIn (E : Finset (Sym2 V)) (T S : Finset V) : Finset V :=
  S.filter (fun z => ∀ x ∈ T, s(x, z) ∈ E)

theorem mem_commonNbhdIn {E : Finset (Sym2 V)} {T S : Finset V} {z : V} :
    z ∈ commonNbhdIn E T S ↔ z ∈ S ∧ ∀ x ∈ T, s(x, z) ∈ E := by
  simp [commonNbhdIn]

/-- Counting: the vertices of `S` outside the common neighbourhood of `T` are covered by the
non-neighbourhoods of the members of `T`. -/
theorem card_commonNbhdIn_ge (E : Finset (Sym2 V)) (T S : Finset V) :
    S.card ≤ (commonNbhdIn E T S).card + ∑ x ∈ T, (S.card - degTo E x S) := by
  classical
  have hsub : S ⊆ commonNbhdIn E T S ∪ T.biUnion (fun x => S \ nbhdIn E x S) := by
    intro z hz
    by_cases hc : ∀ x ∈ T, s(x, z) ∈ E
    · exact Finset.mem_union_left _ (mem_commonNbhdIn.2 ⟨hz, hc⟩)
    · push_neg at hc
      obtain ⟨x, hx, hxz⟩ := hc
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
      exact Finset.mem_sdiff.2 ⟨hz, fun h => hxz (mem_nbhdIn.1 h).2⟩
  calc S.card ≤ (commonNbhdIn E T S ∪ T.biUnion (fun x => S \ nbhdIn E x S)).card :=
        Finset.card_le_card hsub
    _ ≤ (commonNbhdIn E T S).card + (T.biUnion (fun x => S \ nbhdIn E x S)).card :=
        Finset.card_union_le _ _
    _ ≤ (commonNbhdIn E T S).card + ∑ x ∈ T, (S \ nbhdIn E x S).card :=
        Nat.add_le_add_left (Finset.card_biUnion_le) _
    _ = (commonNbhdIn E T S).card + ∑ x ∈ T, (S.card - degTo E x S) := by
        refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
        rw [Finset.card_sdiff_of_subset (nbhdIn_subset E x S), degTo]

/-- **Seven vertices have many common neighbours.**  In a host of minimum degree `(9/10+γ)|S|`,
any set of at most seven vertices has at least `(3/10)|S|` common neighbours inside `S`, even after
an arbitrary set `W` has been removed. -/
theorem card_commonNbhdIn_dense {E : Finset (Sym2 V)} {S : Finset V} {γ : ℝ}
    (hES : E ⊆ cliqueEdges S) (hγ : 0 ≤ γ)
    (hdeg : ∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ))
    {T : Finset V} (hTS : T ⊆ S) (hT : T.card ≤ 7) (W : Finset V) :
    3 / 10 * (S.card : ℝ) - (W.card : ℝ) ≤ ((commonNbhdIn E T S \ W).card : ℝ) := by
  classical
  have hn0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hdegle : ∀ x ∈ T, degTo E x S ≤ S.card := fun x _ =>
    Finset.card_le_card (nbhdIn_subset E x S)
  have h1 : S.card ≤ (commonNbhdIn E T S).card + ∑ x ∈ T, (S.card - degTo E x S) :=
    card_commonNbhdIn_ge E T S
  have h2 : ∀ x ∈ T, (((S.card - degTo E x S : ℕ) : ℝ)) ≤ 1 / 10 * (S.card : ℝ) := by
    intro x hx
    rw [Nat.cast_sub (hdegle x hx)]
    have h3 : (edeg E x : ℝ) ≤ (degTo E x S : ℝ) := by exact_mod_cast edeg_le_degTo hES x
    have h4 := hdeg x (hTS hx)
    nlinarith
  have h5 : ∑ x ∈ T, ((S.card - degTo E x S : ℕ) : ℝ) ≤ 7 * (1 / 10 * (S.card : ℝ)) := by
    calc ∑ x ∈ T, ((S.card - degTo E x S : ℕ) : ℝ)
        ≤ ∑ _x ∈ T, 1 / 10 * (S.card : ℝ) := Finset.sum_le_sum h2
      _ = (T.card : ℝ) * (1 / 10 * (S.card : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 7 * (1 / 10 * (S.card : ℝ)) := by
          have : (T.card : ℝ) ≤ 7 := by exact_mod_cast hT
          nlinarith
  have h6 : (S.card : ℝ) ≤ ((commonNbhdIn E T S).card : ℝ) + 7 * (1 / 10 * (S.card : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).2 h1
    push_cast at this
    linarith
  have h7 : (commonNbhdIn E T S).card ≤ (commonNbhdIn E T S \ W).card + W.card :=
    Finset.card_le_card_sdiff_add_card
  have h8 : ((commonNbhdIn E T S).card : ℝ) ≤ ((commonNbhdIn E T S \ W).card : ℝ) + (W.card : ℝ) := by
    exact_mod_cast h7
  linarith

/-! ### The edge count of a clique -/

/-- The edge degree inside a clique: every vertex of `t` has degree `|t| - 1`. -/
theorem edeg_cliqueEdges_card {t : Finset V} (v : V) :
    edeg (cliqueEdges t) v = if v ∈ t then t.card - 1 else 0 := by
  classical
  by_cases hv : v ∈ t
  · rw [if_pos hv]
    have hcard : (t.erase v).card = t.card - 1 := Finset.card_erase_of_mem hv
    have hfil : (cliqueEdges t).filter (fun e => v ∈ e) = (t.erase v).image (fun u => s(v, u)) := by
      ext e
      induction e using Sym2.ind with
      | _ p q =>
        simp only [Finset.mem_filter, mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq,
          Finset.mem_image, Finset.mem_erase, Sym2.eq_iff]
        constructor
        · rintro ⟨⟨hmem, hne⟩, hvpq⟩
          rcases hvpq with rfl | rfl
          · exact ⟨q, ⟨fun h => hne h.symm, hmem q (Or.inr rfl)⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨p, ⟨fun h => hne h, hmem p (Or.inl rfl)⟩, Or.inr ⟨rfl, rfl⟩⟩
        · rintro ⟨u, ⟨hu1, hu2⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
          · refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩
            · rintro z (rfl | rfl)
              exacts [hv, hu2]
            · exact fun h => hu1 h.symm
          · refine ⟨⟨?_, ?_⟩, Or.inr rfl⟩
            · rintro z (rfl | rfl)
              exacts [hu2, hv]
            · exact fun h => hu1 h
    have hinj : Set.InjOn (fun u => s(v, u)) (t.erase v) := by
      intro a _ c _ hac
      simp only [Sym2.eq_iff] at hac
      rcases hac with ⟨_, h⟩ | ⟨h1, h2⟩
      · exact h
      · exact h2.trans h1
    rw [edeg, hfil, Finset.card_image_of_injOn hinj, hcard]
  · rw [if_neg hv, edeg]
    have hempty : (cliqueEdges t).filter (fun e => v ∈ e) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun e he hve => hv ?_
      exact (mem_cliqueEdgesV.1 he).1 v hve
    rw [hempty, Finset.card_empty]

/-- Handshake inside a clique. -/
theorem two_mul_card_cliqueEdges (t : Finset V) :
    2 * (cliqueEdges t).card = t.card * (t.card - 1) := by
  classical
  have h := sum_edeg_eq_two_mul (A := cliqueEdges t) (S := t) (Finset.Subset.refl _)
  rw [Finset.sum_congr rfl (fun v hv => by
    rw [edeg_cliqueEdges_card v, if_pos hv]), Finset.sum_const, smul_eq_mul] at h
  omega

theorem card_cliqueEdges_seven {t : Finset V} (h : t.card = 7) : (cliqueEdges t).card = 21 := by
  have := two_mul_card_cliqueEdges t
  rw [h] at this
  omega

theorem edeg_cliqueEdges_seven {t : Finset V} (h : t.card = 7) (v : V) :
    edeg (cliqueEdges t) v = if v ∈ t then 6 else 0 := by
  rw [edeg_cliqueEdges_card v, h]

/-! ### Growing a clique -/

theorem cliqueEdges_insert {u : V} {A : Finset V} (hu : u ∉ A) :
    cliqueEdges (insert u A) = cliqueEdges A ∪ A.image (fun a => s(a, u)) := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ p q =>
    simp only [Finset.mem_union, mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq,
      Finset.mem_insert, Finset.mem_image, Sym2.eq_iff]
    constructor
    · rintro ⟨hmem, hne⟩
      have hp := hmem p (Or.inl rfl)
      have hq := hmem q (Or.inr rfl)
      rcases hp with rfl | hp
      · rcases hq with rfl | hq
        · exact absurd rfl hne
        · exact Or.inr ⟨q, hq, Or.inr ⟨rfl, rfl⟩⟩
      · rcases hq with rfl | hq
        · exact Or.inr ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩
        · refine Or.inl ⟨?_, hne⟩
          rintro z (rfl | rfl)
          exacts [hp, hq]
    · rintro (⟨hmem, hne⟩ | ⟨a, ha, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩)
      · exact ⟨fun z hz => Or.inr (hmem z hz), hne⟩
      · refine ⟨?_, ?_⟩
        · rintro z (rfl | rfl)
          exacts [Or.inr ha, Or.inl rfl]
        · rintro rfl
          exact hu ha
      · refine ⟨?_, ?_⟩
        · rintro z (rfl | rfl)
          exacts [Or.inl rfl, Or.inr ha]
        · rintro rfl
          exact hu ha

@[simp] theorem cliqueEdges_singleton (v : V) : cliqueEdges ({v} : Finset V) = ∅ := by
  ext e
  induction e using Sym2.ind with
  | _ p q =>
    simp only [mem_cliqueEdgesV, Sym2.mem_iff, Finset.mem_singleton, Sym2.isDiag_iff_proj_eq,
      Finset.notMem_empty, iff_false, not_and]
    intro hmem
    have hp := hmem p (Or.inl rfl)
    have hq := hmem q (Or.inr rfl)
    simp [hp, hq]

theorem cliqueEdges_pair {x y : V} (hxy : x ≠ y) :
    cliqueEdges ({x, y} : Finset V) = {s(x, y)} := by
  rw [cliqueEdges_insert (by simpa using hxy)]
  simp [Sym2.eq_swap]

/-- **The inner greedy: growing an edge to a clique.**  If any at most seven vertices have a common
neighbour outside every set of size `L`, then a clique `A` of the host with at most `7 - k`
vertices can be extended by `k` further vertices, avoiding a prescribed set `W` and keeping all the
new edges out of the used set `F`. -/
theorem exists_clique_ext {E : Finset (Sym2 V)} {S : Finset V} {F : Finset (Sym2 V)} {b L : ℕ}
    (hcn : ∀ T : Finset V, T ⊆ S → T.card ≤ 7 → ∀ W : Finset V, W.card ≤ L →
      (commonNbhdIn E T S \ W).Nonempty)
    (hF : ∀ v : V, edeg F v ≤ b) :
    ∀ k : ℕ, ∀ A W : Finset V, A ⊆ S → A.card + k ≤ 7 → cliqueEdges A ⊆ E →
      W.card + 7 + 7 * b ≤ L →
      ∃ B : Finset V, B.card = k ∧ B ⊆ S ∧ Disjoint A B ∧ Disjoint B W ∧
        cliqueEdges (A ∪ B) ⊆ E ∧ Disjoint (cliqueEdges (A ∪ B) \ cliqueEdges A) F := by
  classical
  intro k
  induction k with
  | zero =>
    intro A W hAS _ hAE _
    exact ⟨∅, by simp, by simp, by simp, by simp, by simpa using hAE, by simp⟩
  | succ k ih =>
    intro A W hAS hAk hAE hW
    -- the forbidden set for the new vertex
    set Wbig : Finset V := W ∪ A ∪ A.biUnion (fun a => resNbhd F S a) with hWbig
    have hAcard : A.card ≤ 7 := by omega
    have hbi : (A.biUnion (fun a => resNbhd F S a)).card ≤ 7 * b := by
      calc (A.biUnion (fun a => resNbhd F S a)).card
          ≤ ∑ a ∈ A, (resNbhd F S a).card := Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ A, b := Finset.sum_le_sum fun a _ =>
            le_trans (card_resNbhd_le F S a) (hF a)
        _ = A.card * b := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 7 * b := Nat.mul_le_mul_right _ hAcard
    have hWbigcard : Wbig.card ≤ L := by
      have h1 : Wbig.card ≤ (W ∪ A).card + (A.biUnion (fun a => resNbhd F S a)).card :=
        Finset.card_union_le _ _
      have h2 : (W ∪ A).card ≤ W.card + A.card := Finset.card_union_le _ _
      omega
    obtain ⟨u, hu⟩ := hcn A hAS hAcard Wbig hWbigcard
    rw [Finset.mem_sdiff, mem_commonNbhdIn] at hu
    obtain ⟨⟨huS, huE⟩, huW⟩ := hu
    have huWno : u ∉ W := fun h => huW (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have huA : u ∉ A := fun h => huW (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have huF : ∀ a ∈ A, s(a, u) ∉ F := by
      intro a ha hmem
      exact huW (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha,
        Finset.mem_filter.2 ⟨huS, hmem⟩⟩))
    -- the enlarged clique
    set A' : Finset V := insert u A with hA'
    have hA'card : A'.card = A.card + 1 := by rw [hA', Finset.card_insert_of_notMem huA]
    have hA'S : A' ⊆ S := by
      intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      exacts [huS, hAS hv]
    have hA'edges : cliqueEdges A' = cliqueEdges A ∪ A.image (fun a => s(a, u)) :=
      cliqueEdges_insert huA
    have hA'E : cliqueEdges A' ⊆ E := by
      rw [hA'edges]
      refine Finset.union_subset hAE ?_
      intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
      exact huE a ha
    obtain ⟨B', hB'card, hB'S, hAB', hB'W, hB'E, hB'F⟩ :=
      ih A' W hA'S (by omega) hA'E hW
    have huB' : u ∉ B' := fun h =>
      (Finset.disjoint_left.1 hAB') (Finset.mem_insert_self u A) h
    refine ⟨insert u B', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem huB', hB'card]
    · intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      exacts [huS, hB'S hv]
    · refine Finset.disjoint_left.2 ?_
      intro v hv hv'
      rcases Finset.mem_insert.1 hv' with rfl | hv'
      · exact huA hv
      · exact (Finset.disjoint_left.1 hAB') (Finset.mem_insert_of_mem hv) hv'
    · refine Finset.disjoint_left.2 ?_
      intro v hv hv'
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact huWno hv'
      · exact (Finset.disjoint_left.1 hB'W) hv hv'
    · have hunion : A ∪ insert u B' = A' ∪ B' := by
        rw [hA']
        ext v
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hunion]; exact hB'E
    · have hunion : A ∪ insert u B' = A' ∪ B' := by
        rw [hA']
        ext v
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hunion]
      refine Finset.disjoint_left.2 ?_
      intro e he heF
      rw [Finset.mem_sdiff] at he
      by_cases hA'mem : e ∈ cliqueEdges A'
      · rw [hA'edges, Finset.mem_union] at hA'mem
        rcases hA'mem with h | h
        · exact he.2 h
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
          exact huF a ha heF
      · exact (Finset.disjoint_left.1 hB'F) (Finset.mem_sdiff.2 ⟨he.1, hA'mem⟩) heF

/-! ### The outer greedy -/

/-- **Greedy cluster completion (induction).**  Processing the edges of `R` one at a time, each
edge is completed to a `7`-clique by five fresh vertices; the invariant
`edeg (famEdges 𝒞) v + 6 * edeg R v ≤ b` is preserved. -/
theorem cluster_complete_induction {E : Finset (Sym2 V)} {S : Finset V} {b M L : ℕ}
    (hES : E ⊆ cliqueEdges S) (hb : 6 ≤ b)
    (hL : 42 * M + (b - 5) * (7 + 7 * b) ≤ (b - 5) * L)
    (hcn : ∀ T : Finset V, T ⊆ S → T.card ≤ 7 → ∀ W : Finset V, W.card ≤ L →
      (commonNbhdIn E T S \ W).Nonempty) :
    ∀ N : ℕ, ∀ (R : Finset (Sym2 V)) (𝒞 : Finset (Finset V)),
      R.card ≤ N → R ⊆ E → ClusterFamilyIn E 𝒞 → Disjoint (famEdges 𝒞) R →
      𝒞.card + R.card ≤ M →
      (∀ v, edeg (famEdges 𝒞) v + 6 * edeg R v ≤ b) →
      ∃ 𝒞' : Finset (Finset V), ClusterFamilyIn E 𝒞' ∧ 𝒞 ⊆ 𝒞' ∧ R ⊆ famEdges 𝒞' ∧
        𝒞'.card ≤ M ∧ ∀ v, edeg (famEdges 𝒞') v ≤ b := by
  classical
  intro N
  induction N with
  | zero =>
    intro R 𝒞 hcard _ h𝒞 _ hM hdeg
    have hR : R = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    subst hR
    refine ⟨𝒞, h𝒞, Finset.Subset.refl _, by simp, by omega, fun v => ?_⟩
    have := hdeg v
    rw [edeg_empty] at this
    omega
  | succ N ih =>
    intro R 𝒞 hcard hRE h𝒞 hdisj hM hdeg
    rcases R.eq_empty_or_nonempty with rfl | hne
    · refine ⟨𝒞, h𝒞, Finset.Subset.refl _, by simp, by omega, fun v => ?_⟩
      have := hdeg v
      rw [edeg_empty] at this
      omega
    obtain ⟨e0, he0⟩ := hne
    revert he0
    induction e0 using Sym2.ind with
    | _ x y =>
      intro he0
      have hxyE : s(x, y) ∈ cliqueEdges S := hES (hRE he0)
      obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hxyE
      have hxy : x ≠ y := by simpa [Sym2.isDiag_iff_proj_eq] using hnd
      have hx : x ∈ S := hmem x (by simp)
      have hy : y ∈ S := hmem y (by simp)
      -- the load function and the overloaded vertices
      set g : V → ℕ := fun v => edeg (famEdges 𝒞) v + 6 * edeg R v with hgdef
      set W₁ : Finset V := S.filter (fun v => b - 5 ≤ g v) with hW₁
      have hfamS : famEdges 𝒞 ⊆ cliqueEdges S := by
        intro e he
        obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.1 he
        exact hES (h𝒞.2.1 C hC heC)
      have hfamcard : (famEdges 𝒞).card ≤ 21 * 𝒞.card := by
        calc (famEdges 𝒞).card ≤ ∑ C ∈ 𝒞, (cliqueEdges C).card := Finset.card_biUnion_le
          _ = ∑ _C ∈ 𝒞, 21 :=
              Finset.sum_congr rfl fun C hC => card_cliqueEdges_seven (h𝒞.1 C hC)
          _ = 21 * 𝒞.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      have hsum : ∑ v ∈ S, g v ≤ 42 * M := by
        have h1 : ∑ v ∈ S, g v = 2 * (famEdges 𝒞).card + 6 * (2 * R.card) := by
          rw [hgdef]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_edeg_eq_two_mul hfamS,
            sum_edeg_eq_two_mul (hRE.trans hES)]
        omega
      have hW₁card : (b - 5) * W₁.card ≤ 42 * M := by
        have h1 : (b - 5) * W₁.card ≤ ∑ v ∈ W₁, g v := by
          rw [Finset.card_eq_sum_ones, Finset.mul_sum]
          refine Finset.sum_le_sum fun v hv => ?_
          simpa using (Finset.mem_filter.1 hv).2
        have h2 : ∑ v ∈ W₁, g v ≤ ∑ v ∈ S, g v :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        omega
      have hb5 : 0 < b - 5 := by omega
      have hWcard : W₁.card + 7 + 7 * b ≤ L := by
        have hmul : (b - 5) * (W₁.card + 7 + 7 * b) ≤ (b - 5) * L := by
          have : (b - 5) * (W₁.card + 7 + 7 * b)
              = (b - 5) * W₁.card + (b - 5) * (7 + 7 * b) := by ring
          omega
        exact Nat.le_of_mul_le_mul_left hmul hb5
      -- the used edges
      set F : Finset (Sym2 V) := famEdges 𝒞 ∪ R with hF
      have hFdeg : ∀ v : V, edeg F v ≤ b := by
        intro v
        have h1 : edeg F v ≤ edeg (famEdges 𝒞) v + edeg R v := edeg_union_le _ _ _
        have := hdeg v
        omega
      -- grow the edge to a `7`-clique
      have hApair : ({x, y} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
      have hAS : ({x, y} : Finset V) ⊆ S := by
        intro v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hx
        · rw [Finset.mem_singleton] at hv; exact hv ▸ hy
      have hAE : cliqueEdges ({x, y} : Finset V) ⊆ E := by
        rw [cliqueEdges_pair hxy]
        intro e he
        rw [Finset.mem_singleton] at he
        exact he ▸ hRE he0
      obtain ⟨B, hBcard, hBS, hAB, hBW, hCE, hCF⟩ :=
        exists_clique_ext hcn hFdeg 5 ({x, y} : Finset V) W₁ hAS (by omega) hAE hWcard
      set C : Finset V := ({x, y} : Finset V) ∪ B with hC
      have hCcard : C.card = 7 := by
        rw [hC, Finset.card_union_of_disjoint hAB, hApair, hBcard]
      have hxC : x ∈ C := Finset.mem_union_left _ (by simp)
      have hyC : y ∈ C := Finset.mem_union_left _ (by simp)
      have hxyC : s(x, y) ∈ cliqueEdges C := by
        refine mem_cliqueEdgesV.2 ⟨?_, hnd⟩
        rintro z hz
        simp only [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        exacts [hxC, hyC]
      -- the new cluster is edge-disjoint from the old ones
      have hCsplit : cliqueEdges C ⊆ insert s(x, y) (cliqueEdges C \ cliqueEdges ({x, y})) := by
        intro e he
        by_cases hmemA : e ∈ cliqueEdges ({x, y} : Finset V)
        · rw [cliqueEdges_pair hxy, Finset.mem_singleton] at hmemA
          exact Finset.mem_insert.2 (Or.inl hmemA)
        · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨he, hmemA⟩)
      have hCdisjfam : Disjoint (cliqueEdges C) (famEdges 𝒞) := by
        refine Finset.disjoint_left.2 fun e he hefam => ?_
        rcases Finset.mem_insert.1 (hCsplit he) with rfl | he'
        · exact (Finset.disjoint_left.1 hdisj) hefam he0
        · exact (Finset.disjoint_left.1 hCF) he' (Finset.mem_union_left _ hefam)
      have hCnot : C ∉ 𝒞 := by
        intro hmemC
        exact (Finset.disjoint_left.1 hCdisjfam) hxyC (Finset.mem_biUnion.2 ⟨C, hmemC, hxyC⟩)
      set 𝒞' : Finset (Finset V) := insert C 𝒞 with h𝒞'
      have hfam' : famEdges 𝒞' = cliqueEdges C ∪ famEdges 𝒞 := famEdges_insert C 𝒞
      have h𝒞'fam : ClusterFamilyIn E 𝒞' := by
        refine ⟨?_, ?_, ?_⟩
        · intro D hD
          rcases Finset.mem_insert.1 hD with rfl | hD
          · exact hCcard
          · exact h𝒞.1 D hD
        · intro D hD
          rcases Finset.mem_insert.1 hD with rfl | hD
          · exact hCE
          · exact h𝒞.2.1 D hD
        · intro D hD D' hD' hne
          rcases Finset.mem_insert.1 hD with rfl | hD <;>
            rcases Finset.mem_insert.1 hD' with rfl | hD'
          · exact absurd rfl hne
          · exact Finset.disjoint_of_subset_right
              (fun e he => Finset.mem_biUnion.2 ⟨D', hD', he⟩) hCdisjfam
          · exact (Finset.disjoint_of_subset_right
              (fun e he => Finset.mem_biUnion.2 ⟨D, hD, he⟩) hCdisjfam).symm
          · exact h𝒞.2.2 D hD D' hD' hne
      -- the remaining edges
      set R' : Finset (Sym2 V) := R.erase s(x, y) with hR'
      have hRpos : 0 < R.card := Finset.card_pos.2 ⟨_, he0⟩
      have hR'card : R'.card = R.card - 1 := Finset.card_erase_of_mem he0
      have hR'N : R'.card ≤ N := by omega
      have hR'E : R' ⊆ E := (Finset.erase_subset _ _).trans hRE
      have hdisj' : Disjoint (famEdges 𝒞') R' := by
        rw [hfam']
        refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
        · refine Finset.disjoint_left.2 fun e he heR' => ?_
          rcases Finset.mem_insert.1 (hCsplit he) with rfl | he'
          · exact (Finset.mem_erase.1 heR').1 rfl
          · exact (Finset.disjoint_left.1 hCF) he'
              (Finset.mem_union_right _ (Finset.mem_of_mem_erase heR'))
        · exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hdisj
      have hMcard : 𝒞'.card + R'.card ≤ M := by
        have h1 : 𝒞'.card = 𝒞.card + 1 := by rw [h𝒞', Finset.card_insert_of_notMem hCnot]
        omega
      have hdeg' : ∀ v, edeg (famEdges 𝒞') v + 6 * edeg R' v ≤ b := by
        intro v
        have hd1 : edeg (famEdges 𝒞') v = edeg (cliqueEdges C) v + edeg (famEdges 𝒞) v := by
          rw [hfam', edeg_union_of_disjoint hCdisjfam]
        have hd2 : edeg (cliqueEdges C) v = if v ∈ C then 6 else 0 :=
          edeg_cliqueEdges_seven hCcard v
        have hd3 : edeg R v = edeg R' v + (if v ∈ s(x, y) then 1 else 0) := edeg_erase he0 v
        have hdv := hdeg v
        by_cases hvC : v ∈ C
        · rw [hd1, hd2, if_pos hvC]
          by_cases hvxy : v ∈ s(x, y)
          · rw [hd3, if_pos hvxy] at hdv
            omega
          · -- `v` is one of the five fresh vertices, so it was not overloaded
            have hvB : v ∈ B := by
              rcases Finset.mem_union.1 hvC with hvA | hvB
              · exfalso
                rcases Finset.mem_insert.1 hvA with rfl | hvA
                · exact hvxy (by simp)
                · rw [Finset.mem_singleton] at hvA
                  exact hvxy (by rw [hvA]; simp)
              · exact hvB
            have hvW₁ : v ∉ W₁ := fun h => (Finset.disjoint_left.1 hBW) hvB h
            have hvS : v ∈ S := hBS hvB
            have hgv : ¬ (b - 5 ≤ g v) := fun h => hvW₁ (Finset.mem_filter.2 ⟨hvS, h⟩)
            have hgv' : g v + 6 ≤ b := by omega
            rw [hd3, if_neg hvxy] at hdv
            rw [hgdef] at hgv'
            simp only at hgv'
            omega
        · rw [hd1, hd2, if_neg hvC]
          have : edeg R' v ≤ edeg R v := edeg_mono (Finset.erase_subset _ _) v
          omega
      obtain ⟨𝒞'', h𝒞''fam, h𝒞'𝒞'', hR'sub, h𝒞''card, h𝒞''deg⟩ :=
        ih R' 𝒞' hR'N hR'E h𝒞'fam hdisj' hMcard hdeg'
      refine ⟨𝒞'', h𝒞''fam, ?_, ?_, h𝒞''card, h𝒞''deg⟩
      · exact (Finset.subset_insert _ _).trans h𝒞'𝒞''
      · intro e he
        by_cases hee : e = s(x, y)
        · subst hee
          exact Finset.mem_biUnion.2 ⟨C, h𝒞'𝒞'' (Finset.mem_insert_self C 𝒞), hxyC⟩
        · exact hR'sub (Finset.mem_erase.2 ⟨hee, he⟩)

/-- **Greedy cluster completion.**  A sparse subgraph of a host in which any seven vertices have a
common neighbour outside any small exceptional set embeds into the edge set of an edge-disjoint
family of `K₇`s whose maximum degree is still at most `b`. -/
theorem exists_cluster_completion {E : Finset (Sym2 V)} {S : Finset V} {b M L : ℕ}
    (hES : E ⊆ cliqueEdges S) (hb : 6 ≤ b)
    (hL : 42 * M + (b - 5) * (7 + 7 * b) ≤ (b - 5) * L)
    (hcn : ∀ T : Finset V, T ⊆ S → T.card ≤ 7 → ∀ W : Finset V, W.card ≤ L →
      (commonNbhdIn E T S \ W).Nonempty)
    {R : Finset (Sym2 V)} (hRE : R ⊆ E) (hM : R.card ≤ M)
    (hRdeg : ∀ v, 6 * edeg R v ≤ b) :
    ∃ 𝒞 : Finset (Finset V), ClusterFamilyIn E 𝒞 ∧ R ⊆ famEdges 𝒞 ∧
      ∀ v, edeg (famEdges 𝒞) v ≤ b := by
  classical
  obtain ⟨𝒞, h𝒞, _, hsub, _, hdeg⟩ :=
    cluster_complete_induction hES hb hL hcn R.card R ∅ (le_refl _) hRE
      ⟨by simp, by simp, by simp⟩ (by simp [famEdges]) (by simpa using hM)
      (fun v => by simpa [famEdges, edeg_empty] using hRdeg v)
  exact ⟨𝒞, h𝒞, hsub, hdeg⟩

/-! ### A sparse pair-covering cluster reservoir -/

set_option maxHeartbeats 2000000 in
/-- **A sparse pair-covering cluster reservoir** (the case of small `γ`). -/
theorem clusterReservoirExistence_small {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1 / 20) (K : ℕ) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ 𝒞 : Finset (Finset V), ClusterFamilyIn E 𝒞 ∧
        (∀ v : V, (edeg (famEdges 𝒞) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card := by
  classical
  obtain ⟨n₁, hpc⟩ := exists_sparse_pairCovering (γ := γ / 1000) (by linarith) K
  refine ⟨max n₁ (max ⌈(40000 : ℝ) / γ⌉₊ 100000), ?_⟩
  intro V _ E S hn hES hdeg
  set n := S.card with hndef
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : ⌈(40000 : ℝ) / γ⌉₊ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : 100000 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnR : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hγn : (40000 : ℝ) ≤ γ * (n : ℝ) := by
    have h1 : (40000 : ℝ) / γ ≤ (⌈(40000 : ℝ) / γ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(40000 : ℝ) / γ⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have h3 : (40000 : ℝ) / γ ≤ (n : ℝ) := le_trans h1 h2
    have := mul_le_mul_of_nonneg_left h3 hγ.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hγ)] at this
  -- the sparse pair-covering graph reservoir
  obtain ⟨R, hRE, hRdeg, hRcov⟩ := hpc E S hn1 hES (fun v hv => by
    have := hdeg v hv
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith)
  -- the parameters
  set d : ℕ := ⌈γ * (n : ℝ) / 1000⌉₊ with hddef
  have hd1 : 1 ≤ d := Nat.one_le_ceil_iff.2 (by positivity)
  have hdup : (d : ℝ) ≤ γ * (n : ℝ) / 1000 + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hdR : ∀ v : V, edeg R v ≤ d := by
    intro v
    have h1 : (edeg R v : ℝ) ≤ γ / 1000 * (n : ℝ) := hRdeg v
    have h2 : (edeg R v : ℝ) ≤ (d : ℝ) :=
      le_trans (by linarith) (Nat.le_ceil (γ * (n : ℝ) / 1000))
    exact_mod_cast h2
  set b : ℕ := 168 * d + 12 with hbdef
  set L : ℕ := n / 4 with hLdef
  have h4L : 4 * L ≤ n := by rw [hLdef]; omega
  have hL4 : n ≤ 4 * L + 3 := by rw [hLdef]; omega
  have hLr : (4 : ℝ) * (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast h4L
  have hLr' : (n : ℝ) ≤ 4 * (L : ℝ) + 3 := by exact_mod_cast hL4
  have hγnsmall : γ * (n : ℝ) ≤ (n : ℝ) / 20 := by nlinarith
  -- the reservoir is small enough for the completion
  have hL2400 : 2400 * d + 4000 ≤ L := by
    have : ((2400 * d + 4000 : ℕ) : ℝ) ≤ (L : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hRcard : 2 * R.card ≤ d * n := by
    have h1 : ∑ v ∈ S, edeg R v = 2 * R.card := sum_edeg_eq_two_mul (hRE.trans hES)
    have h2 : ∑ v ∈ S, edeg R v ≤ ∑ _v ∈ S, d := Finset.sum_le_sum fun v _ => hdR v
    rw [Finset.sum_const, smul_eq_mul] at h2
    calc 2 * R.card = ∑ v ∈ S, edeg R v := h1.symm
      _ ≤ S.card * d := h2
      _ = d * n := by rw [← hndef]; ring
  have hb6 : 6 ≤ b := by omega
  have hb5 : b - 5 = 168 * d + 7 := by omega
  have hLbig : 42 * R.card + (b - 5) * (7 + 7 * b) ≤ (b - 5) * L := by
    rw [hb5, hbdef]
    nlinarith only [hRcard, h4L, hL4, hL2400, hd1]
  -- every seven vertices have a common neighbour outside any set of size `L`
  have hcn : ∀ T : Finset V, T ⊆ S → T.card ≤ 7 → ∀ W : Finset V, W.card ≤ L →
      (commonNbhdIn E T S \ W).Nonempty := by
    intro T hTS hT W hW
    have hdense := card_commonNbhdIn_dense hES hγ.le hdeg hTS hT W
    have hWr : (W.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hW
    have hpos : (0 : ℝ) < ((commonNbhdIn E T S \ W).card : ℝ) := by linarith
    have : 0 < (commonNbhdIn E T S \ W).card := by exact_mod_cast hpos
    exact Finset.card_pos.1 this
  obtain ⟨𝒞, h𝒞, hR𝒞, h𝒞deg⟩ :=
    exists_cluster_completion hES hb6 hLbig hcn hRE (le_refl _) (fun v => by
      have := hdR v
      omega)
  refine ⟨𝒞, h𝒞, fun v => ?_, ?_⟩
  · have h1 : (edeg (famEdges 𝒞) v : ℝ) ≤ (b : ℝ) := by exact_mod_cast h𝒞deg v
    have h2 : ((b : ℕ) : ℝ) = 168 * (d : ℝ) + 12 := by rw [hbdef]; push_cast; ring
    rw [h2] at h1
    linarith
  · intro e he
    exact le_trans (hRcov e he) (Finset.card_le_card (apexSet_mono hR𝒞 S e))

/-- **A sparse pair-covering cluster reservoir.**

For every `γ > 0` and every constant `K`, every large dense host contains an edge-disjoint family
of `K₇`s whose edge set has maximum degree at most `γ|S|` and in which every pair of vertices of
`S` has at least `K` common reserved neighbours.  Equipped with the Fano planes of
`BKLO/Fano.lean`, this is the first of the two clauses that the target needs. -/
theorem clusterReservoirExistence_holds : ClusterReservoirExistence := by
  intro γ hγ K
  obtain ⟨n₀, h⟩ := clusterReservoirExistence_small (γ := min γ (1 / 20))
    (lt_min hγ (by norm_num)) (min_le_right _ _) K
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES hdeg
  have hmin : min γ (1 / 20) ≤ γ := min_le_left _ _
  have h0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨𝒞, h𝒞, h𝒞deg, h𝒞cov⟩ := h E S hn hES (fun v hv => by
    have hv' := hdeg v hv
    nlinarith)
  refine ⟨𝒞, h𝒞, fun v => ?_, h𝒞cov⟩
  have hv := h𝒞deg v
  nlinarith

/-- **The target follows from the routing statement alone.**  The cluster reservoir it needs is
now constructed. -/
theorem absorberDenseK3BoundedLeftover_of_routing (hroute : ClusterUsageRouting) :
    AbsorberDenseK3BoundedLeftover :=
  absorberDenseK3BoundedLeftover_of_cluster clusterReservoirExistence_holds hroute

end BKLO
