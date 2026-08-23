/-
# The transformation step of BKLO Lemma 10.6 (`r = 2`) under the *weak* hierarchy `1/k ≤ ε`

`BKLO.transformStepK3At_of_approxTriDecomp` proves the transformation step
`BKLO.TransformStepK3At δ ε k` from the approximate-decomposition threshold `δ_F^η`
(`BKLO.ApproxTriDecompMinDeg δ`) under `1/k ≤ ε/8`.  That factor `8` is not needed: this file
proves the same conclusion under the weaker `1/k ≤ ε` (which is the form in which BKLO Lemma 10.12
supplies the hierarchy, see `BKLO.lemma1012K3'At_of_inputs`).

The extra room comes from *balancing the partition before applying the nibble*.  In the original
proof the nibble is applied to the crossing graph `C = G[P]` on all of `V`, and the crossing degree
of a vertex `v` is only `(δ+ε)(n − |W_v|) ≥ (δ+ε)(n − n/k − 1)`; absorbing the additive `1` is what
costs the factor `8`.  Here we first delete, from each part, all but `m := ⌊n/k⌋` vertices, getting
`S* ⊆ V` with all parts of size exactly `m` and `|S*| = km`, and apply the nibble to `C[S*]`
instead (`BKLO.approxTriDecompMinDeg_set`, the vertex-set form of the threshold).  On `S*` the
crossing degree of `v ∈ S*` is at least `(k−1)(m − (1−δ−ε)(m+1)) ≥ δ·km = δ|S*|`, the inequality
holding as soon as `m ≥ k−1` because `kε ≥ 1` and `δ + ε ≤ 1`; the latter is *forced* by the
`(k, δ+ε)`-partition itself.  The at most `k` deleted vertices carry at most `kn` edges, which is
absorbed in the nibble's error term for large `n`.

Everything here is `sorry`-free.
-/
import BKLO.SubtypeTransport

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### The crossing degree inside a balanced selection -/

/-- If `f W ⊆ W` selects a subset of each part and `v ∈ f W₀`, then the degree of `v` in the
crossing graph induced on the selection `⋃_{W ∈ P} f W` is at least `∑_{W ≠ W₀} d_E(v, f W)`. -/
theorem sum_degTo_le_edeg_edgesIn_crossParts {P : Finset (Finset V)} {E : Finset (Sym2 V)}
    (hdisj : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint W W')
    (f : Finset V → Finset V) (hf : ∀ W ∈ P, f W ⊆ W)
    {W₀ : Finset V} (hW₀ : W₀ ∈ P) {v : V} (hv : v ∈ f W₀) :
    ∑ W ∈ P.erase W₀, degTo E v (f W)
      ≤ edeg (edgesIn (crossParts E P) (P.biUnion f)) v := by
  classical
  set S : Finset V := P.biUnion f with hS
  set N := (P.erase W₀).biUnion (fun W => nbhdIn E v (f W)) with hN
  have hdisjN : ∀ W ∈ P.erase W₀, ∀ W' ∈ P.erase W₀, W ≠ W' →
      Disjoint (nbhdIn E v (f W)) (nbhdIn E v (f W')) := by
    intro W hW W' hW' hne
    refine Finset.disjoint_of_subset_left ((nbhdIn_subset _ _ _).trans (hf W (Finset.mem_of_mem_erase hW)))
      (Finset.disjoint_of_subset_right ((nbhdIn_subset _ _ _).trans (hf W' (Finset.mem_of_mem_erase hW')))
        (hdisj W (Finset.mem_of_mem_erase hW) W' (Finset.mem_of_mem_erase hW') hne))
  have hcardN : N.card = ∑ W ∈ P.erase W₀, degTo E v (f W) := Finset.card_biUnion hdisjN
  have hvS : v ∈ S := Finset.mem_biUnion.2 ⟨W₀, hW₀, hv⟩
  have hsub : N.image (fun y => s(v, y)) ⊆
      (edgesIn (crossParts E P) S).filter (fun e => v ∈ e) := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨W, hW, hyW⟩ := Finset.mem_biUnion.1 hy
    have hWP : W ∈ P := Finset.mem_of_mem_erase hW
    have hyfW : y ∈ f W := (nbhdIn_subset E v (f W)) hyW
    have hyW' : y ∈ W := hf W hWP hyfW
    have hvW₀ : v ∈ W₀ := hf W₀ hW₀ hv
    have hE : s(v, y) ∈ E := (mem_nbhdIn.1 hyW).2
    have hyS : y ∈ S := Finset.mem_biUnion.2 ⟨W, hWP, hyfW⟩
    refine Finset.mem_filter.2 ⟨mem_edgesIn.2 ⟨mem_crossParts.2 ⟨hE, ?_⟩, ?_⟩, by simp⟩
    · rintro ⟨W', hW', hall⟩
      have h1 : v ∈ W' := hall v (by simp)
      have h2 : y ∈ W' := hall y (by simp)
      have hne : W ≠ W₀ := Finset.ne_of_mem_erase hW
      by_cases hWW' : W' = W₀
      · rw [hWW'] at h2
        exact (Finset.disjoint_left.1 (hdisj W hWP W₀ hW₀ hne)) hyW' h2
      · exact (Finset.disjoint_left.1 (hdisj W' hW' W₀ hW₀ hWW')) h1 hvW₀
    · intro u hu
      rcases Sym2.mem_iff.1 hu with rfl | rfl
      exacts [hvS, hyS]
  have hinj : Set.InjOn (fun y => s(v, y)) N := by
    intro x _ y _ hxy
    simp only [Sym2.eq_iff] at hxy
    rcases hxy with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  calc ∑ W ∈ P.erase W₀, degTo E v (f W) = N.card := hcardN.symm
    _ = (N.image (fun y => s(v, y))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((edgesIn (crossParts E P) S).filter (fun e => v ∈ e)).card := Finset.card_le_card hsub
    _ = edeg (edgesIn (crossParts E P) S) v := rfl

/-! ### Elementary counting -/

/-- A loopless edge set on a finite vertex type has all degrees at most `n`. -/
theorem edeg_le_card [Fintype V] {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag) (v : V) :
    edeg E v ≤ Fintype.card V := by
  classical
  have hsub : E ⊆ cliqueEdges (Finset.univ : Finset V) := by
    intro e he
    exact mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x, hE e he⟩
  calc edeg E v ≤ edeg (cliqueEdges (Finset.univ : Finset V)) v := edeg_mono hsub v
    _ ≤ (Finset.univ : Finset V).card := edeg_cliqueEdges_le _ v
    _ = Fintype.card V := Finset.card_univ

/-- The edges of `E` that are not induced on `S` are at most `|Sᶜ|·n` many. -/
theorem card_sdiff_edgesIn_le [Fintype V] {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (S : Finset V) :
    (E \ edgesIn E S).card ≤ (Finset.univ \ S).card * Fintype.card V := by
  classical
  have hsub : E \ edgesIn E S ⊆
      (Finset.univ \ S).biUnion (fun v => E.filter (fun e => v ∈ e)) := by
    intro e he
    obtain ⟨heE, henot⟩ := Finset.mem_sdiff.1 he
    have : ¬ (∀ v ∈ e, v ∈ S) := fun hall => henot (mem_edgesIn.2 ⟨heE, hall⟩)
    push_neg at this
    obtain ⟨v, hve, hvS⟩ := this
    exact Finset.mem_biUnion.2 ⟨v, Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hvS⟩,
      Finset.mem_filter.2 ⟨heE, hve⟩⟩
  calc (E \ edgesIn E S).card
      ≤ ((Finset.univ \ S).biUnion (fun v => E.filter (fun e => v ∈ e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.univ \ S, (E.filter (fun e => v ∈ e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ Finset.univ \ S, Fintype.card V :=
        Finset.sum_le_sum fun v _ => edeg_le_card hE v
    _ = (Finset.univ \ S).card * Fintype.card V := by
        rw [Finset.sum_const, smul_eq_mul]

/-! ### The transformation step -/

set_option maxHeartbeats 400000 in
/-- **The transformation step of BKLO Lemma 10.6 for `r = 2`, at a fixed `(ε, k)`, under the weak
hierarchy `1/k ≤ ε`**, from the approximate decomposition threshold.

This is `BKLO.transformStepK3At_of_approxTriDecomp` with `1/k ≤ ε/8` weakened to `1/k ≤ ε`.  The
hypotheses `0 ≤ δ` and `δ ≤ 1` of that version are not needed here: `δ + ε ≤ 1` is *forced* by the
`(k, δ+ε)`-partition, since a vertex has degree at most `|W| - 1` into its own part `W`. -/
theorem transformStepK3At_of_approxTriDecomp_weak {δ ε : ℝ} {k : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 3) (hk : 0 < k)
    (hkε : 1 / (k : ℝ) ≤ ε) (happ : ApproxTriDecompMinDeg δ) :
    TransformStepK3At δ ε k := by
  classical
  intro γ β hγ hβ
  set c : ℝ := min (β / 2) (γ / 5) with hcdef
  have hc : 0 < c := lt_min (by linarith) (by linarith)
  have hcβ : c ≤ β / 2 := min_le_left _ _
  have hcγ : c ≤ γ / 5 := min_le_right _ _
  obtain ⟨n₁, hn₁⟩ := approxTriDecompMinDeg_set happ (η := c ^ 2 / 2) (by positivity)
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge (4 * (k : ℝ) / c ^ 2)
  refine ⟨max (max (n₁ + k) (k * k)) (max N₃ 1), ?_⟩
  intro V _ _ E P hn hloop hpart
  simp only [Nat.max_le] at hn
  obtain ⟨⟨hna, hnb⟩, hnc, hnd⟩ := hn
  set n : ℕ := Fintype.card V with hndef
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnd
  have hkε' : (1 : ℝ) ≤ (k : ℝ) * ε := by
    rw [div_le_iff₀ hkR] at hkε; linarith
  obtain ⟨hEq, hdeg⟩ := hpart
  set C : Finset (Sym2 V) := crossParts E P with hCdef
  have hCloop : ∀ e ∈ C, ¬ e.IsDiag := fun e he => hloop e (crossParts_subset E P he)
  -- the balanced selection
  set m : ℕ := n / k with hmdef
  have hmle : ∀ W ∈ P, m ≤ W.card := by
    intro W hW
    have := hEq.size_lower W hW
    rwa [Finset.card_univ, ← hndef, ← hmdef] at this
  have hWup : ∀ W ∈ P, W.card ≤ m + 1 := by
    intro W hW
    have h1 := hEq.size_upper W hW
    rw [Finset.card_univ, ← hndef] at h1
    have h2 : (n + k - 1) / k ≤ m + 1 := by
      rw [hmdef]
      have : n + k - 1 ≤ n + k := by omega
      calc (n + k - 1) / k ≤ (n + k) / k := Nat.div_le_div_right this
        _ = n / k + 1 := by rw [Nat.add_div_right n hk]
    omega
  have hchoice : ∀ W ∈ P, ∃ t ⊆ W, t.card = m := fun W hW =>
    Finset.exists_subset_card_eq (hmle W hW)
  choose! f hfsub hfcard using hchoice
  set S : Finset V := P.biUnion f with hSdef
  have hfdisj : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint (f W) (f W') := by
    intro W hW W' hW' hne
    exact Finset.disjoint_of_subset_left (hfsub W hW)
      (Finset.disjoint_of_subset_right (hfsub W' hW') (hEq.pairwise_disjoint W hW W' hW' hne))
  have hScard : S.card = k * m := by
    rw [hSdef, Finset.card_biUnion hfdisj,
      Finset.sum_congr rfl (fun W hW => hfcard W hW), Finset.sum_const, smul_eq_mul,
      hEq.card_parts]
  -- `m` is large
  have hmk : k - 1 ≤ m := by
    have : (k - 1) * k ≤ n := by
      have : k * k ≤ n := hnb
      exact le_trans (Nat.mul_le_mul (Nat.sub_le k 1) (le_refl k)) this
    rw [hmdef]
    exact (Nat.le_div_iff_mul_le hk).2 this
  have hm1 : 1 ≤ m := by
    have : k * k ≤ n := hnb
    have hk1 : 1 ≤ k := hk
    rw [hmdef]
    exact (Nat.le_div_iff_mul_le hk).2 (by nlinarith only [this, hk1])
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmkR : (k : ℝ) - 1 ≤ (m : ℝ) := by
    have : ((k - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmk
    have hk1 : (1 : ℕ) ≤ k := hk
    rwa [Nat.cast_sub hk1, Nat.cast_one] at this
  -- `δ + ε ≤ 1` is forced by the partition
  have hd1 : δ + ε ≤ 1 := by
    obtain ⟨W₀, hW₀⟩ : ∃ W₀, W₀ ∈ P := by
      have : P.card = k := hEq.card_parts
      have : 0 < P.card := by omega
      exact Finset.card_pos.1 this |>.imp fun _ h => h
    have hWpos : 0 < W₀.card := lt_of_lt_of_le hm1 (hmle W₀ hW₀)
    obtain ⟨x, hx⟩ := Finset.card_pos.1 hWpos
    have h1 := hdeg x (Finset.mem_univ x) W₀ hW₀
    have h2 : nbhdIn E x W₀ ⊆ W₀.erase x := by
      intro y hy
      obtain ⟨hyW, hxy⟩ := mem_nbhdIn.1 hy
      refine Finset.mem_erase.2 ⟨?_, hyW⟩
      rintro rfl
      exact hloop _ hxy (by simp [Sym2.isDiag_iff_proj_eq])
    have h3 : degTo E x W₀ ≤ W₀.card - 1 := by
      have := Finset.card_le_card h2
      rwa [Finset.card_erase_of_mem hx] at this
    have h4 : (degTo E x W₀ : ℝ) ≤ (W₀.card : ℝ) - 1 := by
      have h5 : (1 : ℕ) ≤ W₀.card := hWpos
      have : ((W₀.card - 1 : ℕ) : ℝ) = (W₀.card : ℝ) - 1 := by
        rw [Nat.cast_sub h5, Nat.cast_one]
      rw [← this]; exact_mod_cast h3
    have hWR : (1 : ℝ) ≤ (W₀.card : ℝ) := by exact_mod_cast hWpos
    nlinarith only [h1, h4, hWR]
  -- the minimum degree of the crossing graph induced on `S`
  have hmindeg : ∀ v ∈ S, δ * (S.card : ℝ) ≤ (edeg (edgesIn C S) v : ℝ) := by
    intro v hv
    obtain ⟨W₀, hW₀, hvW₀⟩ := Finset.mem_biUnion.1 hv
    have hstep := sum_degTo_le_edeg_edgesIn_crossParts (E := E) hEq.pairwise_disjoint f hfsub hW₀ hvW₀
    have hterm : ∀ W ∈ P.erase W₀,
        (m : ℝ) - (1 - δ - ε) * ((m : ℝ) + 1) ≤ (degTo E v (f W) : ℝ) := by
      intro W hW
      have hWP : W ∈ P := Finset.mem_of_mem_erase hW
      have h1 : (δ + ε) * (W.card : ℝ) ≤ (degTo E v W : ℝ) := hdeg v (Finset.mem_univ v) W hWP
      have h2 : degTo E v W ≤ degTo E v (f W) + (W.card - m) := by
        have hsub : nbhdIn E v W ⊆ nbhdIn E v (f W) ∪ (W \ f W) := by
          intro y hy
          obtain ⟨hyW, hyE⟩ := mem_nbhdIn.1 hy
          by_cases hyf : y ∈ f W
          · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hyf, hyE⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hyW, hyf⟩)
        have h3 : (W \ f W).card = W.card - m := by
          rw [Finset.card_sdiff_of_subset (hfsub W hWP), hfcard W hWP]
        calc degTo E v W ≤ (nbhdIn E v (f W) ∪ (W \ f W)).card := Finset.card_le_card hsub
          _ ≤ degTo E v (f W) + (W \ f W).card := Finset.card_union_le _ _
          _ = degTo E v (f W) + (W.card - m) := by rw [h3]
      have hmW : m ≤ W.card := hmle W hWP
      have h2R : (degTo E v W : ℝ) ≤ (degTo E v (f W) : ℝ) + ((W.card : ℝ) - (m : ℝ)) := by
        have : ((W.card - m : ℕ) : ℝ) = (W.card : ℝ) - (m : ℝ) := by
          rw [Nat.cast_sub hmW]
        have h4 : (degTo E v W : ℝ) ≤ ((degTo E v (f W) + (W.card - m) : ℕ) : ℝ) := by
          exact_mod_cast h2
        push_cast [Nat.cast_sub hmW] at h4
        linarith
      have hWupR : (W.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hWup W hWP
      have hWmR : (m : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hmW
      nlinarith only [h1, h2R, hWupR, hd1, hWmR]
    have hsum : ((P.erase W₀).card : ℝ) * ((m : ℝ) - (1 - δ - ε) * ((m : ℝ) + 1))
        ≤ ∑ W ∈ P.erase W₀, (degTo E v (f W) : ℝ) := by
      calc ((P.erase W₀).card : ℝ) * ((m : ℝ) - (1 - δ - ε) * ((m : ℝ) + 1))
          = ∑ _W ∈ P.erase W₀, ((m : ℝ) - (1 - δ - ε) * ((m : ℝ) + 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ W ∈ P.erase W₀, (degTo E v (f W) : ℝ) := Finset.sum_le_sum hterm
    have hcarderase : ((P.erase W₀).card : ℝ) = (k : ℝ) - 1 := by
      have h1 : (P.erase W₀).card = k - 1 := by
        rw [Finset.card_erase_of_mem hW₀, hEq.card_parts]
      have hk1 : (1 : ℕ) ≤ k := hk
      rw [h1, Nat.cast_sub hk1, Nat.cast_one]
    have hstepR : (∑ W ∈ P.erase W₀, (degTo E v (f W) : ℝ))
        ≤ (edeg (edgesIn C S) v : ℝ) := by
      have : ((∑ W ∈ P.erase W₀, degTo E v (f W) : ℕ) : ℝ) ≤ (edeg (edgesIn C S) v : ℝ) := by
        exact_mod_cast hstep
      push_cast at this
      exact this
    have hkey : δ * ((k : ℝ) * (m : ℝ))
        ≤ ((k : ℝ) - 1) * ((m : ℝ) - (1 - δ - ε) * ((m : ℝ) + 1)) := by
      have hid : ((k : ℝ) - 1) * ((m : ℝ) - (1 - δ - ε) * ((m : ℝ) + 1)) - δ * ((k : ℝ) * (m : ℝ))
          = (1 - δ - ε) * ((m : ℝ) + 1 - (k : ℝ)) + (m : ℝ) * ((k : ℝ) * ε - 1) := by ring
      have h1 : (0 : ℝ) ≤ (1 - δ - ε) * ((m : ℝ) + 1 - (k : ℝ)) := by
        apply mul_nonneg (by linarith) (by linarith)
      have h2 : (0 : ℝ) ≤ (m : ℝ) * ((k : ℝ) * ε - 1) := by
        apply mul_nonneg (by linarith) (by linarith)
      linarith only [hid, h1, h2]
    have hScardR : (S.card : ℝ) = (k : ℝ) * (m : ℝ) := by
      rw [hScard]; push_cast; ring
    rw [hScardR]
    rw [hcarderase] at hsum
    linarith only [hkey, hsum, hstepR]
  -- the nibble on `S`
  have hdm : k * m + n % k = n := by rw [hmdef]; exact Nat.div_add_mod n k
  have hmod : n % k < k := Nat.mod_lt _ hk
  have hSn₁ : n₁ ≤ S.card := by omega
  have hCS : edgesIn C S ⊆ cliqueEdges S := by
    intro e he
    obtain ⟨heC, hall⟩ := mem_edgesIn.1 he
    exact mem_cliqueEdgesV.2 ⟨hall, hCloop e heC⟩
  obtain ⟨T, hTfam, hTcard0⟩ := hn₁ (edgesIn C S) S hSn₁ hCS hmindeg
  have hT : TriFamilyIn C T :=
    ⟨hTfam.1, fun t ht => (hTfam.2.1 t ht).trans (edgesIn_subset C S), hTfam.2.2⟩
  set G₀ : Finset (Sym2 V) := C \ famEdges T with hG₀def
  have hG₀loop : ∀ e ∈ G₀, ¬ e.IsDiag := fun e he => hCloop e (Finset.mem_sdiff.1 he).1
  -- the leftover is small
  have hTcard : (G₀.card : ℝ) ≤ c ^ 2 * (n : ℝ) ^ 2 := by
    have hsplit : G₀ ⊆ (edgesIn C S \ famEdges T) ∪ (C \ edgesIn C S) := by
      intro e he
      obtain ⟨heC, heT⟩ := Finset.mem_sdiff.1 he
      by_cases hin : e ∈ edgesIn C S
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hin, heT⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨heC, hin⟩)
    have h1 : G₀.card ≤ (edgesIn C S \ famEdges T).card + (C \ edgesIn C S).card :=
      le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
    have h2 : (C \ edgesIn C S).card ≤ (Finset.univ \ S).card * n := card_sdiff_edgesIn_le hCloop S
    have h3 : (Finset.univ \ S).card ≤ k := by
      have h4 : (Finset.univ \ S).card = n - S.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
      omega
    have h2R : ((C \ edgesIn C S).card : ℝ) ≤ (k : ℝ) * (n : ℝ) := by
      have : (C \ edgesIn C S).card ≤ k * n := le_trans h2 (Nat.mul_le_mul_right n h3)
      exact_mod_cast this
    have hScardle : (S.card : ℝ) ≤ (n : ℝ) := by
      have : S.card ≤ n := by
        rw [hndef, ← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ S)
      exact_mod_cast this
    have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hsq : (S.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ hSnn hScardle 2
    have h7 : ((edgesIn C S \ famEdges T).card : ℝ) ≤ c ^ 2 / 2 * (n : ℝ) ^ 2 :=
      hTcard0.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    have hbig : (4 : ℝ) * (k : ℝ) / c ^ 2 ≤ (n : ℝ) := le_trans hN₃ (by exact_mod_cast hnc)
    have h8 : (k : ℝ) * (n : ℝ) ≤ c ^ 2 / 2 * (n : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hbig
      nlinarith only [mul_le_mul_of_nonneg_left hbig hnR.le, sq_nonneg (c * (n : ℝ))]
    have h1R : (G₀.card : ℝ) ≤ ((edgesIn C S \ famEdges T).card : ℝ)
        + ((C \ edgesIn C S).card : ℝ) := by exact_mod_cast h1
    linarith
  -- from here on the argument is that of `BKLO.transformStepK3At_of_approxTriDecomp`
  set B : Finset V := (Finset.univ : Finset V).filter (fun v => c * (n : ℝ) < (edeg G₀ v : ℝ))
    with hBdef
  have hBbound : (B.card : ℝ) ≤ 2 * c * (n : ℝ) := by
    have h1 := card_high_deg_mul_le (E := G₀) hG₀loop (c := c * (n : ℝ))
    have h3 : (B.card : ℝ) * (c * (n : ℝ)) ≤ 2 * (c ^ 2 * (n : ℝ) ^ 2) := by
      refine le_trans h1 ?_
      linarith
    have hcn : (0 : ℝ) < c * (n : ℝ) := by positivity
    refine le_of_mul_le_mul_right ?_ hcn
    nlinarith only [h3]
  have hBβ : (B.card : ℝ) ≤ β * (n : ℝ) := by
    have : 2 * c ≤ β := by linarith
    nlinarith only [hBbound, hnR, this]
  set T' : Finset (Finset V) := T.filter (fun t => ∀ u ∈ t, u ∉ B) with hT'def
  have hT'T : T' ⊆ T := Finset.filter_subset _ _
  have hT'fam : TriFamilyIn C T' :=
    ⟨fun t ht => hT.1 t (hT'T ht), fun t ht => hT.2.1 t (hT'T ht),
      fun t ht t' ht' hne => hT.2.2 t (hT'T ht) t' (hT'T ht') hne⟩
  have hfamsub : famEdges T' ⊆ C := famEdges_subset_of_triFamilyIn hT'fam
  set H' : Finset (Sym2 V) := C \ famEdges T' with hH'def
  refine ⟨B, H', hBβ, Finset.sdiff_subset, ?_, ?_, ?_⟩
  · have : C \ H' = famEdges T' := by
      rw [hH'def]
      exact Finset.sdiff_sdiff_eq_self hfamsub
    rw [this]
    exact hT'fam.triDecomp
  · intro e he ⟨v, hvB, hve⟩
    refine Finset.mem_sdiff.2 ⟨he, ?_⟩
    intro hc'
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hc'
    have hvt : v ∈ t := (mem_cliqueEdgesV.1 het).1 v hve
    exact (Finset.mem_filter.1 ht).2 v hvt hvB
  · intro v hvB
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
    nlinarith only [hdegR, hlow, hBbound, hnR, h5c]

end BKLO
