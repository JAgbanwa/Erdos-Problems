/-
# BKLO Lemma 10.6 (`r = 2`), first half: the transformation step, repaired and proved.

`BKLO.TransformStepK3` (see `BKLO/Section10DegreeReduction.lean`) transcribes the first half of the
proof of BKLO Lemma 10.6 for `r = 2` but *omits* the part `1/k ≪ ε` of the paper's hierarchy
`1/n ≪ η ≪ γ ≪ 1/k ≪ ε`.  As `BKLO.not_transformStepK3` shows, that omission makes the statement
false (already for `k = 2`, where the crossing graph is bipartite).

This file

* isolates the statement for a fixed pair `(ε, k)` as `BKLO.TransformStepK3At`;
* states the **repaired** transformation step `BKLO.TransformStepK3Res`, which is
  `TransformStepK3At δ ε k` for all `ε ≤ 1/3` and all `k` with `1/k ≤ ε/8` (the paper's
  `1/k ≪ ε`);
* transcribes the one genuinely external ingredient of the paper's proof, the approximate
  decomposition threshold `δ_F^η` for `F = K₃`, as `BKLO.ApproxTriDecompMinDeg δ`:
  *for every `η > 0`, every large graph with minimum degree at least `δn` has an edge-disjoint
  triangle family leaving at most `ηn²` edges uncovered*.  In the paper `δ` is *defined* as
  `max{δ_F^η, 1 − 1/(r+1)}`, so `ApproxTriDecompMinDeg δ` is exactly the content of `δ ≥ δ_F^η`;
* **proves** `ApproxTriDecompMinDeg δ → TransformStepK3Res δ`
  (`BKLO.transformStepK3Res_of_approxTriDecomp`).

## The proof

Let `C := G[P]` be the crossing graph.  Because `P` is a `(k, δ+ε)`-partition and `1/k ≤ ε/8`,
every vertex has `d_C(v) ≥ (δ+ε)(n − |W_v|) ≥ δn` (`BKLO.edeg_crossParts_ge`), so the approximate
decomposition input applies to `C` with a small `η := c²`, where `c := min (β/2) (γ/5)`.  Let `T`
be the resulting triangle family and `G₀ := C − ⋃T` the uncovered graph, `e(G₀) ≤ c²n²`.  Put

* `B := {v : d_{G₀}(v) > cn}`;  double counting gives `|B| ≤ 2cn ≤ βn`;
* `T' := {t ∈ T : t ∩ B = ∅}` and `H' := C − ⋃T'`.

Then `C − H' = ⋃T'` is triangle-decomposable, every crossing edge meeting `B` lies in `H'`, and
for `v ∉ B`

`d_{H'}(v) ≤ d_{G₀}(v) + 2·#{t ∈ T \ T' : v ∈ t} ≤ cn + 2|B| ≤ 5cn ≤ γn`,

using that the triangles of `T` are edge-disjoint, so at most one of them contains any given edge
`vb` with `b ∈ B`; this replaces the paper's rerouting of the copies of `F` meeting `B` (its
random subgraph `G'` and its Lemma 5.2), which is not needed to obtain the conclusion in the form
required by `TransformStepK3`.

Everything here is `sorry`-free.
-/
import BKLO.Section10DegreeReduction

open Finset

namespace BKLO

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Elementary degree lemmas -/

omit [Fintype V] in
theorem edeg_union_le_ts (E F : Finset (Sym2 V)) (v : V) :
    edeg (E ∪ F) v ≤ edeg E v + edeg F v := by
  classical
  have h : (E ∪ F).filter (fun e => v ∈ e) =
      E.filter (fun e => v ∈ e) ∪ F.filter (fun e => v ∈ e) := Finset.filter_union _ _ _
  unfold edeg
  rw [h]
  exact Finset.card_union_le _ _

omit [Fintype V] in
/-- The degree of `v` in the edge set of a triangle family is at most twice the number of
triangles of the family containing `v`. -/
theorem edeg_famEdges_le {S : Finset (Finset V)} (h3 : ∀ t ∈ S, t.card = 3) (v : V) :
    edeg (famEdges S) v ≤ 2 * (S.filter (fun t => v ∈ t)).card := by
  classical
  have hsub : (famEdges S).filter (fun e => v ∈ e) ⊆
      (S.filter (fun t => v ∈ t)).biUnion
        (fun t => (cliqueEdges t).filter (fun e => v ∈ e)) := by
    intro e he
    obtain ⟨hef, hve⟩ := Finset.mem_filter.1 he
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hef
    have hvt : v ∈ t := (mem_cliqueEdgesV.1 het).1 v hve
    exact Finset.mem_biUnion.2 ⟨t, Finset.mem_filter.2 ⟨ht, hvt⟩, Finset.mem_filter.2 ⟨het, hve⟩⟩
  calc edeg (famEdges S) v ≤ ((S.filter (fun t => v ∈ t)).biUnion
          (fun t => (cliqueEdges t).filter (fun e => v ∈ e))).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ S.filter (fun t => v ∈ t), ((cliqueEdges t).filter (fun e => v ∈ e)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ S.filter (fun t => v ∈ t), 2 := by
        refine Finset.sum_le_sum fun t ht => ?_
        obtain ⟨htS, hvt⟩ := Finset.mem_filter.1 ht
        have : edeg (cliqueEdges t) v = 2 := by
          rw [edeg_cliqueEdges (h3 t htS) v, if_pos hvt]
        exact le_of_eq this
    _ = 2 * (S.filter (fun t => v ∈ t)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Since the triangles of an edge-disjoint family are edge-disjoint, a vertex `v ∉ B` lies in at
most `|B|` triangles of the family that meet `B`. -/
theorem card_triangles_meeting_le {T : Finset (Finset V)} {B : Finset V} {v : V}
    (hdisj : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t'))
    (hvB : v ∉ B) :
    ((T.filter (fun t => ¬ ∀ u ∈ t, u ∉ B)).filter (fun t => v ∈ t)).card ≤ B.card := by
  classical
  set S := (T.filter (fun t => ¬ ∀ u ∈ t, u ∉ B)).filter (fun t => v ∈ t) with hS
  have hex : ∀ t ∈ S, ∃ b, b ∈ t ∧ b ∈ B := by
    intro t ht
    have ht' := (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2
    push_neg at ht'
    obtain ⟨b, hb1, hb2⟩ := ht'
    exact ⟨b, hb1, hb2⟩
  set f : Finset V → V := fun t => if h : ∃ b, b ∈ t ∧ b ∈ B then h.choose else v with hf
  have hfspec : ∀ t ∈ S, f t ∈ t ∧ f t ∈ B := by
    intro t ht
    have h := hex t ht
    simp only [hf, dif_pos h]
    exact h.choose_spec
  refine Finset.card_le_card_of_injOn f (fun t ht => (hfspec t ht).2) ?_
  intro t₁ h₁ t₂ h₂ heq
  by_contra hne
  have hb₁ := hfspec t₁ h₁
  have hb₂ := hfspec t₂ h₂
  have hbt₂ : f t₁ ∈ t₂ := by rw [heq]; exact hb₂.1
  have hvb : v ≠ f t₁ := fun h => hvB (h ▸ hb₁.2)
  have hv₁ : v ∈ t₁ := (Finset.mem_filter.1 h₁).2
  have hv₂ : v ∈ t₂ := (Finset.mem_filter.1 h₂).2
  have hmem : ∀ t : Finset V, v ∈ t → f t₁ ∈ t → s(v, f t₁) ∈ cliqueEdges t := by
    intro t hvt hbt
    refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
    · intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact hvt
      · exact hbt
    · simpa [Sym2.isDiag_iff_proj_eq] using hvb
  have hT₁ : t₁ ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 h₁).1).1
  have hT₂ : t₂ ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 h₂).1).1
  exact (Finset.disjoint_left.1 (hdisj t₁ hT₁ t₂ hT₂ hne)) (hmem t₁ hv₁ hb₁.1)
    (hmem t₂ hv₂ hbt₂)

/-- **Handshake.**  A loopless edge set has degree sum `2|E|`. -/
theorem sum_edeg_univ {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    ∑ v ∈ (Finset.univ : Finset V), edeg E v = 2 * E.card := by
  classical
  have h1 : ∑ v ∈ (Finset.univ : Finset V), edeg E v
      = ∑ e ∈ E, ((Finset.univ : Finset V).filter (fun v => v ∈ e)).card := by
    unfold edeg
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : ∀ e ∈ E, ((Finset.univ : Finset V).filter (fun v => v ∈ e)).card = 2 := by
    intro e he
    have hnd : ¬ e.IsDiag := hE e he
    clear he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := by
        intro h
        exact hnd (by simp [Sym2.isDiag_iff_proj_eq, h])
      have hfil : (Finset.univ : Finset V).filter (fun v => v ∈ s(x, y)) = {x, y} := by
        ext v
        simp
      rw [hfil, Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Double counting the vertices of large degree.**  If `E` has no loops then the set of vertices
of degree more than `c` has size at most `2|E|/c`. -/
theorem card_high_deg_mul_le {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag) {c : ℝ} :
    (((Finset.univ : Finset V).filter (fun v => c < (edeg E v : ℝ))).card : ℝ) * c
      ≤ 2 * (E.card : ℝ) := by
  classical
  set B := (Finset.univ : Finset V).filter (fun v => c < (edeg E v : ℝ)) with hB
  have hhand : ∑ v ∈ (Finset.univ : Finset V), edeg E v = 2 * E.card := sum_edeg_univ hE
  have h1 : (B.card : ℝ) * c ≤ ∑ v ∈ B, (edeg E v : ℝ) := by
    have := Finset.card_nsmul_le_sum B (fun v => (edeg E v : ℝ)) c
      (fun v hv => le_of_lt (Finset.mem_filter.1 hv).2)
    simpa [nsmul_eq_mul, mul_comm] using this
  have h2 : ∑ v ∈ B, (edeg E v : ℝ) ≤ ∑ v ∈ (Finset.univ : Finset V), (edeg E v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun v _ _ => by positivity)
  have h3 : ∑ v ∈ (Finset.univ : Finset V), (edeg E v : ℝ) = 2 * (E.card : ℝ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hhand
  linarith

/-! ### The crossing degree of a `(k, d)`-partition -/

/-- In a `(k, d)`-partition, every vertex `v` has crossing degree at least `d(n − |W_v|)`, where
`W_v` is the part containing `v`. -/
theorem edeg_crossParts_ge {k : ℕ} {d : ℝ} {P : Finset (Finset V)} {E : Finset (Sym2 V)}
    (h : IsKDeltaPartition k d P E Finset.univ) (v : V) :
    ∃ W₀ ∈ P, v ∈ W₀ ∧
      d * ((Fintype.card V : ℝ) - (W₀.card : ℝ)) ≤ (edeg (crossParts E P) v : ℝ) := by
  classical
  obtain ⟨hEq, hdeg⟩ := h
  have hv : v ∈ P.biUnion id := by rw [hEq.cover]; exact Finset.mem_univ v
  obtain ⟨W₀, hW₀, hvW₀⟩ := Finset.mem_biUnion.1 hv
  refine ⟨W₀, hW₀, hvW₀, ?_⟩
  set N := (P.erase W₀).biUnion (fun W => nbhdIn E v W) with hN
  have hdisjN : ∀ W ∈ P.erase W₀, ∀ W' ∈ P.erase W₀, W ≠ W' →
      Disjoint (nbhdIn E v W) (nbhdIn E v W') := by
    intro W hW W' hW' hne
    exact Finset.disjoint_of_subset_left (nbhdIn_subset _ _ _)
      (Finset.disjoint_of_subset_right (nbhdIn_subset _ _ _)
        (hEq.pairwise_disjoint W (Finset.mem_of_mem_erase hW) W'
          (Finset.mem_of_mem_erase hW') hne))
  have hcardN : N.card = ∑ W ∈ P.erase W₀, degTo E v W := Finset.card_biUnion hdisjN
  -- `N` embeds in the crossing star at `v`
  have hsub : N.image (fun y => s(v, y)) ⊆ (crossParts E P).filter (fun e => v ∈ e) := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨W, hW, hyW⟩ := Finset.mem_biUnion.1 hy
    have hyW' : y ∈ W := (nbhdIn_subset E v W) hyW
    have hE : s(v, y) ∈ E := (mem_nbhdIn.1 hyW).2
    refine Finset.mem_filter.2 ⟨mem_crossParts.2 ⟨hE, ?_⟩, by simp⟩
    rintro ⟨W', hW', hall⟩
    have h1 : v ∈ W' := hall v (by simp)
    have h2 : y ∈ W' := hall y (by simp)
    have e1 : W' = W₀ := eq_of_mem_parts hEq hW' hW₀ h1 hvW₀
    have e2 : W' = W := eq_of_mem_parts hEq hW' (Finset.mem_of_mem_erase hW) h2 hyW'
    exact (Finset.ne_of_mem_erase hW) (e2 ▸ e1)
  have hinj : Set.InjOn (fun y => s(v, y)) N := by
    intro x _ y _ hxy
    simp only [Sym2.eq_iff] at hxy
    rcases hxy with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  have hNle : N.card ≤ edeg (crossParts E P) v := by
    calc N.card = (N.image (fun y => s(v, y))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ edeg (crossParts E P) v := Finset.card_le_card hsub
  -- the sum of the sizes of the other parts is `n - |W₀|`
  have htot : ∑ W ∈ P, W.card = Fintype.card V := by
    have hcb := Finset.card_biUnion
      (s := P) (t := (id : Finset V → Finset V))
      (fun W hW W' hW' hne => hEq.pairwise_disjoint W hW W' hW' hne)
    rw [hEq.cover, Finset.card_univ] at hcb
    exact hcb.symm
  have hsplit : (W₀.card : ℝ) + ∑ W ∈ P.erase W₀, (W.card : ℝ) = (Fintype.card V : ℝ) := by
    rw [Finset.add_sum_erase P (fun W => (W.card : ℝ)) hW₀, ← Nat.cast_sum]
    exact_mod_cast htot
  have hlow : ∑ W ∈ P.erase W₀, d * (W.card : ℝ) ≤ ∑ W ∈ P.erase W₀, (degTo E v W : ℝ) :=
    Finset.sum_le_sum fun W hW =>
      hdeg v (Finset.mem_univ v) W (Finset.mem_of_mem_erase hW)
  have hsumeq : ∑ W ∈ P.erase W₀, (degTo E v W : ℝ) = (N.card : ℝ) := by
    rw [hcardN]; push_cast; ring
  have hmul : d * ((Fintype.card V : ℝ) - (W₀.card : ℝ))
      = ∑ W ∈ P.erase W₀, d * (W.card : ℝ) := by
    rw [← Finset.mul_sum]
    congr 1
    linarith only [hsplit]
  have hNR : (N.card : ℝ) ≤ (edeg (crossParts E P) v : ℝ) := by exact_mod_cast hNle
  rw [hmul]
  linarith only [hlow, hsumeq, hNR]

/-! ### The transformation step: statements -/

/-- **The repaired transformation step.**  `BKLO.TransformStepK3` with the part `1/k ≪ ε` of the
paper's hierarchy for Lemma 10.6 restored (`1/k ≤ ε/8`, together with `ε ≤ 1/3`, which is implicit
in the paper because `δ + ε ≤ 1` and `δ ≥ 2/3`).  Without it the statement is false; see
`BKLO.not_transformStepK3`. -/
def TransformStepK3Res (δ : ℝ) : Prop :=
  ∀ (ε : ℝ) (k : ℕ), 0 < ε → ε ≤ 1 / 3 → 0 < k → 1 / (k : ℝ) ≤ ε / 8 → TransformStepK3At δ ε k

/-- **The approximate decomposition threshold `δ_F^η` for `F = K₃`.**  For every `η > 0`, every
large graph with minimum degree at least `δn` has an edge-disjoint family of triangles leaving at
most `ηn²` edges uncovered.  In BKLO, `δ := max{δ_F^η, 1 − 1/(r+1)}`, so this is exactly the
content of `δ ≥ δ_F^η`. -/
def ApproxTriDecompMinDeg (δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)),
      n₀ ≤ Fintype.card V → (∀ e ∈ E, ¬ e.IsDiag) →
      (∀ v : V, δ * (Fintype.card V : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ T : Finset (Finset V), TriFamilyIn E T ∧
        ((E \ famEdges T).card : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2

/-! ### The transformation step: proof -/

/-- **The transformation step of BKLO Lemma 10.6 for `r = 2`, at a fixed `(ε, k)`**, from the
approximate decomposition threshold. -/
theorem transformStepK3At_of_approxTriDecomp {δ ε : ℝ} {k : ℕ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 3) (hk : 0 < k)
    (hkε : 1 / (k : ℝ) ≤ ε / 8) (happ : ApproxTriDecompMinDeg δ) :
    TransformStepK3At δ ε k := by
  classical
  intro γ β hγ hβ
  set c : ℝ := min (β / 2) (γ / 5) with hcdef
  have hc : 0 < c := lt_min (by linarith) (by linarith)
  have hcβ : c ≤ β / 2 := min_le_left _ _
  have hcγ : c ≤ γ / 5 := min_le_right _ _
  obtain ⟨n₁, hn₁⟩ := happ (c ^ 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (2 / ε)
  refine ⟨max (max n₁ N₂) 1, ?_⟩
  intro V _ _ E P hn hloop hpart
  simp only [Nat.max_le] at hn
  obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
  set n : ℕ := Fintype.card V with hndef
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn3
  have hεn : (2 : ℝ) ≤ ε * (n : ℝ) := by
    have h1 : (2 : ℝ) / ε ≤ (n : ℝ) := le_trans hN₂ (by exact_mod_cast hn2)
    rw [div_le_iff₀ hε] at h1
    linarith
  set C : Finset (Sym2 V) := crossParts E P with hCdef
  have hCloop : ∀ e ∈ C, ¬ e.IsDiag := fun e he => hloop e (crossParts_subset E P he)
  -- (1)  the crossing graph has minimum degree at least `δn`
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hmindeg : ∀ v : V, δ * (n : ℝ) ≤ (edeg C v : ℝ) := by
    intro v
    obtain ⟨W₀, hW₀, -, hbound⟩ := edeg_crossParts_ge hpart v
    have hWup : (W₀.card : ℝ) ≤ (n : ℝ) / (k : ℝ) + 1 := by
      have h1 : W₀.card ≤ ((Finset.univ : Finset V).card + k - 1) / k := hpart.1.size_upper W₀ hW₀
      have h2 : (((n + k - 1) / k : ℕ) : ℝ) ≤ ((n + k - 1 : ℕ) : ℝ) / (k : ℝ) :=
        cast_div_le (n + k - 1) k hk
      have h3 : ((n + k - 1 : ℕ) : ℝ) = (n : ℝ) + (k : ℝ) - 1 := by
        have : 1 ≤ n + k := by omega
        push_cast [Nat.cast_sub this]
        ring
      have h4 : (W₀.card : ℝ) ≤ (((n + k - 1) / k : ℕ) : ℝ) := by
        have : W₀.card ≤ (n + k - 1) / k := by
          simpa [hndef, Finset.card_univ] using h1
        exact_mod_cast this
      have h5 : ((n : ℝ) + (k : ℝ) - 1) / (k : ℝ) ≤ (n : ℝ) / (k : ℝ) + 1 := by
        rw [div_le_iff₀ hkR]
        have : (0 : ℝ) < (k : ℝ) := hkR
        field_simp
        linarith only [hkR]
      calc (W₀.card : ℝ) ≤ (((n + k - 1) / k : ℕ) : ℝ) := h4
        _ ≤ ((n + k - 1 : ℕ) : ℝ) / (k : ℝ) := h2
        _ = ((n : ℝ) + (k : ℝ) - 1) / (k : ℝ) := by rw [h3]
        _ ≤ (n : ℝ) / (k : ℝ) + 1 := h5
    have hnk : (n : ℝ) / (k : ℝ) ≤ ε * (n : ℝ) / 8 := by
      have h1 : (n : ℝ) / (k : ℝ) = (n : ℝ) * (1 / (k : ℝ)) := by ring
      rw [h1]
      have := mul_le_mul_of_nonneg_left hkε hnR.le
      linarith
    have hpos : (0 : ℝ) ≤ δ + ε := by linarith
    have hstep : δ * (n : ℝ) ≤ (δ + ε) * ((n : ℝ) - (W₀.card : ℝ)) := by
      nlinarith [hWup, hnk, hεn, hnR]
    linarith only [hbound, hstep]
  -- (2)  the approximate decomposition of the crossing graph
  obtain ⟨T, hT, hTcard⟩ := hn₁ (V := V) C (by omega) hCloop hmindeg
  set G₀ : Finset (Sym2 V) := C \ famEdges T with hG₀def
  have hG₀loop : ∀ e ∈ G₀, ¬ e.IsDiag := fun e he => hCloop e (Finset.mem_sdiff.1 he).1
  -- (3)  the exceptional set `B`
  set B : Finset V := (Finset.univ : Finset V).filter (fun v => c * (n : ℝ) < (edeg G₀ v : ℝ))
    with hBdef
  have hBbound : (B.card : ℝ) ≤ 2 * c * (n : ℝ) := by
    have h1 := card_high_deg_mul_le (E := G₀) hG₀loop (c := c * (n : ℝ))
    have h2 : (G₀.card : ℝ) ≤ c ^ 2 * (n : ℝ) ^ 2 := hTcard
    have h3 : (B.card : ℝ) * (c * (n : ℝ)) ≤ 2 * (c ^ 2 * (n : ℝ) ^ 2) := by
      refine le_trans h1 ?_
      linarith
    have hcn : (0 : ℝ) < c * (n : ℝ) := by positivity
    refine le_of_mul_le_mul_right ?_ hcn
    nlinarith only [h3]
  have hBβ : (B.card : ℝ) ≤ β * (n : ℝ) := by
    have : 2 * c ≤ β := by linarith
    nlinarith [hBbound, hnR]
  -- (4)  the triangles avoiding `B`
  set T' : Finset (Finset V) := T.filter (fun t => ∀ u ∈ t, u ∉ B) with hT'def
  have hT'T : T' ⊆ T := Finset.filter_subset _ _
  have hT'fam : TriFamilyIn C T' :=
    ⟨fun t ht => hT.1 t (hT'T ht), fun t ht => hT.2.1 t (hT'T ht),
      fun t ht t' ht' hne => hT.2.2 t (hT'T ht) t' (hT'T ht') hne⟩
  have hfamsub : famEdges T' ⊆ C := famEdges_subset_of_triFamilyIn hT'fam
  set H' : Finset (Sym2 V) := C \ famEdges T' with hH'def
  refine ⟨B, H', hBβ, Finset.sdiff_subset, ?_, ?_, ?_⟩
  · -- the decomposition
    have : C \ H' = famEdges T' := by
      rw [hH'def]
      exact Finset.sdiff_sdiff_eq_self hfamsub
    rw [this]
    exact hT'fam.triDecomp
  · -- every crossing edge at `B` is left over
    intro e he ⟨v, hvB, hve⟩
    refine Finset.mem_sdiff.2 ⟨he, ?_⟩
    intro hc'
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hc'
    have hvt : v ∈ t := (mem_cliqueEdgesV.1 het).1 v hve
    exact (Finset.mem_filter.1 ht).2 v hvt hvB
  · -- the degree bound off `B`
    intro v hvB
    have hlow : (edeg G₀ v : ℝ) ≤ c * (n : ℝ) := by
      by_contra hcon
      exact hvB (Finset.mem_filter.2 ⟨Finset.mem_univ v, lt_of_not_ge (fun h => hcon h)⟩)
    have hsub : H' ⊆ G₀ ∪ famEdges (T \ T') := by
      intro e he
      obtain ⟨heC, heT'⟩ := Finset.mem_sdiff.1 he
      by_cases hT0 : e ∈ famEdges T
      · obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hT0
        have htT' : t ∉ T' := fun hc' => heT' (Finset.mem_biUnion.2 ⟨t, hc', het⟩)
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.2 ⟨t, Finset.mem_sdiff.2 ⟨ht, htT'⟩, het⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨heC, hT0⟩)
    have hdegsplit : edeg H' v ≤ edeg G₀ v + edeg (famEdges (T \ T')) v :=
      le_trans (edeg_mono hsub v) (edeg_union_le_ts _ _ v)
    have hfilter : T \ T' = T.filter (fun t => ¬ ∀ u ∈ t, u ∉ B) := by
      ext t
      simp only [Finset.mem_sdiff, hT'def, Finset.mem_filter]
      tauto
    have hcount : edeg (famEdges (T \ T')) v ≤ 2 * B.card := by
      have h1 : edeg (famEdges (T \ T')) v ≤ 2 * ((T \ T').filter (fun t => v ∈ t)).card :=
        edeg_famEdges_le (fun t ht => hT.1 t (Finset.mem_sdiff.1 ht).1) v
      have h2 : ((T \ T').filter (fun t => v ∈ t)).card ≤ B.card := by
        rw [hfilter]
        exact card_triangles_meeting_le hT.2.2 hvB
      omega
    have hdegR : (edeg H' v : ℝ) ≤ (edeg G₀ v : ℝ) + 2 * (B.card : ℝ) := by
      have : (edeg H' v : ℝ) ≤ (edeg G₀ v : ℝ) + (edeg (famEdges (T \ T')) v : ℝ) := by
        exact_mod_cast hdegsplit
      have h2 : (edeg (famEdges (T \ T')) v : ℝ) ≤ 2 * (B.card : ℝ) := by exact_mod_cast hcount
      linarith
    have h5c : 5 * c ≤ γ := by linarith
    nlinarith [hdegR, hlow, hBbound, hnR]

/-- **The repaired transformation step of BKLO Lemma 10.6 (`r = 2`), proved** from the approximate
decomposition threshold `δ_F^η` (`BKLO.ApproxTriDecompMinDeg`), which in BKLO is what the choice
`δ := max{δ_F^η, 1 − 1/(r+1)}` provides. -/
theorem transformStepK3Res_of_approxTriDecomp {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (happ : ApproxTriDecompMinDeg δ) : TransformStepK3Res δ :=
  fun _ _ hε hε1 hk hkε =>
    transformStepK3At_of_approxTriDecomp hδ0 hδ1 hε hε1 hk hkε happ

/-! ### BKLO Lemma 10.6 for `r = 2`, repaired -/

/-- **BKLO Lemma 10.6 for `r = 2`**, with the paper's `1/k ≪ ε` restored (`1/k ≤ ε/8`).  Apart
from that hypothesis this is `BKLO.Lemma106K3` verbatim. -/
def Lemma106K3Res (δ : ℝ) : Prop :=
  ∀ (γ ε : ℝ) (k : ℕ), 0 < γ → γ ≤ ε / 4 → 0 < ε → ε ≤ 1 / 3 → 0 < k →
    1 / (k : ℝ) ≤ ε / 8 → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) (P : Finset (Finset V)),
        n₀ ≤ Fintype.card V → (∀ e ∈ E, ¬ e.IsDiag) →
        IsKDeltaPartition k (δ + ε) P E Finset.univ →
        ∃ H : Finset (Sym2 V), H ⊆ E ∧
          TriDecomp (E \ H) ∧
          (∀ v : V, (edeg (crossParts H P) v : ℝ) ≤ γ * (Fintype.card V : ℝ)) ∧
          (∀ W ∈ P, ∀ v : V,
            (edeg (edgesIn E W \ edgesIn H W) v : ℝ) ≤ 2 * γ * (W.card : ℝ))

/-- **BKLO Lemma 10.6 for `r = 2` (repaired), from the repaired transformation step and
Lemma 10.4.**  The proof is the paper's second half, `BKLO.lemma106K3_core`. -/
theorem lemma106K3Res_of_transformStepRes {δ : ℝ} (hδ : (2 : ℝ) / 3 ≤ δ)
    (htr : TransformStepK3Res δ) (h104 : Lemma104K3) : Lemma106K3Res δ :=
  fun _ _ _ hγ hγε hε hε1 hk hkε =>
    lemma106K3_core hδ h104 hγ hγε hε hε1 hk (htr _ _ hε hε1 hk hkε)

/-- **BKLO Lemma 10.6 for `r = 2` (repaired), from the two paper inputs.**

The inputs are exactly the two that BKLO's proof of Lemma 10.6 uses and that are not formalised
in this development:

* `happ : ApproxTriDecompMinDeg δ` — the approximate decomposition threshold `δ_F^η` (in the paper
  `δ := max{δ_F^η, 1 − 1/(r+1)}`, so this is the content of `δ ≥ δ_F^η`);
* `h103 : Lemma103K3` — BKLO Lemma 10.3, which yields Lemma 10.4 by
  `BKLO.lemma104K3_of_lemma103K3`.

Everything else — both halves of the proof of Lemma 10.6 — is proved here. -/
theorem lemma106K3Res_of_inputs {δ : ℝ} (hδ : (2 : ℝ) / 3 ≤ δ) (hδ1 : δ ≤ 1)
    (happ : ApproxTriDecompMinDeg δ) (h103 : Lemma103K3) : Lemma106K3Res δ :=
  lemma106K3Res_of_transformStepRes hδ
    (transformStepK3Res_of_approxTriDecomp (by linarith) hδ1 happ)
    (lemma104K3_of_lemma103K3 h103)

end BKLO
