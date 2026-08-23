/-
# BKLO Lemma 10.10 for `r = 2` in the sparse (pseudorandom) regime

`BKLO.lemma1010K3Dense_holds` (in `BKLO/Section1010Dense.lean`) proves Lemma 10.10 when
`1/(648k²) < ρ`, where the codegree hypothesis (iii) alone bounds the number of apices at a vertex
of `V` and the deterministic greedy sweep of `BKLO.exists_triDecomp_of_budget` suffices.  This file
treats the regime the paper actually works in, `ρ ≪ α, 1/k`, and does two things.

**1.  The transcription `BKLO.Lemma1010K3` is false without the paper's hierarchy.**
`BKLO.degTo_le_edeg_of_triDecomp` (in `BKLO/Section1010Obstruction.lean`) shows that *any* `H'_V`
as in the conclusion has `Δ(H'_V) ≥ max_{y ∈ V} d_H(y, U)`, while hypothesis (iv) only says
`d_H(y,U) ≤ 2kρ|V|`.  So the conclusion `Δ(H'_V) ≤ 2α|V|` genuinely needs `kρ ≲ α`, which is part
of the paper's hierarchy `1/n ≪ ρ ≪ α, 1/k` but was dropped in the transcription
`BKLO.Lemma1010K3`.  `BKLO.Lemma1010K3Hier` below restores exactly the consequence `2kρ ≤ α` of
that hierarchy, and nothing else.

**2.  What remains is exactly the pseudorandom `K_r`-factor core, Lemma 10.7.**  For `r = 2` a
`K_r`-factor of `H[N_H(x,V)]` is a *perfect matching*, and the whole content of Lemma 10.7 /
Corollary 10.9 is that these perfect matchings can be chosen **pairwise edge-disjoint** across the
`≤ kn` apices `x ∈ U`.  This is isolated here as the single clause `BKLO.Lemma107K2`, and

  `BKLO.lemma1010K3Hier_of_lemma107K2 : Lemma107K2 → Lemma1010K3Hier`

is proved in full.  So the *only* residual on the paper's route to Lemma 10.10 is `Lemma107K2`.

Why the residual is real: the deterministic greedy sweep needs the used degree `2 d_H(v,U)` at a
vertex to fit inside the slack `18kρ^{3/2}|V|` of hypothesis (ii), i.e. `4kρ ≤ 18kρ^{3/2}`, which
fails for `ρ < 4/81`; and the dense regime `ρ > 1/(648k²)` is already covered.  In the paper the
matchings are chosen *randomly* instead, so that a previously used edge at `v` lies inside the
current neighbourhood `N_H(x,V)` only with probability `≈ |N_H(x,V) ∩ N_H(x',V)| / d ≤
2ρ²/(36kρ^{3/2}) = √ρ/(18k)`; the expected used degree is then `≈ ρ^{3/2}|V|/9`, comfortably inside
the slack.  Concentration for that sequential process is BKLO Proposition 10.8 (Jain's Bernoulli
domination).  That probabilistic core is what `Lemma107K2` packages.

Everything here is `sorry`-free.
-/
import BKLO.Section1010Dense
import BKLO.Section1010Obstruction
import BKLO.Section102K3

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### From edge-disjoint neighbourhood matchings to the triangle decomposition -/

/-- Star edges of an apex `x` that avoid `x` itself are matching edges. -/
theorem mem_famEdges_of_notMem_star {x : V} {M : Finset (Finset V)} {e : Sym2 V}
    (he : e ∈ famEdges (starTriangles x M)) (hx : x ∉ e) : e ∈ famEdges M := by
  classical
  rw [famEdges, Finset.mem_biUnion] at he
  obtain ⟨tri, htri, hetri⟩ := he
  rw [starTriangles, Finset.mem_image] at htri
  obtain ⟨f, hf, rfl⟩ := htri
  obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hetri
  refine Finset.mem_biUnion.2 ⟨f, hf, mem_cliqueEdgesV.2 ⟨?_, hnd⟩⟩
  intro v hv
  rcases Finset.mem_insert.1 (hmem v hv) with hvx | hvf
  · exact absurd (hvx ▸ hv) hx
  · exact hvf

/-- **Edge-disjoint matchings give edge-disjoint stars.**  If the neighbourhood matchings `Mx x`,
`x ∈ U`, are pairwise edge-disjoint, then so are the star-triangle edge sets: an edge of two stars
either contains an apex — impossible, since apices lie outside `W` — or is a matching edge of
both. -/
theorem starTriangles_pairwise_of_matchings {H : Finset (Sym2 V)} {U W : Finset V}
    {Mx : V → Finset (Finset V)} (hUW : Disjoint U W)
    (hsub : ∀ x ∈ U, ∀ e ∈ Mx x, e ⊆ nbhdIn H x W)
    (hpair : (U : Set V).Pairwise (fun x y => Disjoint (famEdges (Mx x)) (famEdges (Mx y)))) :
    (U : Set V).Pairwise (fun x y => Disjoint (famEdges (starTriangles x (Mx x)))
      (famEdges (starTriangles y (Mx y)))) := by
  classical
  intro x hx y hy hxy
  refine Finset.disjoint_left.2 fun e hex hey => ?_
  -- an apex cannot lie on an edge of the other apex's star
  have hnot : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → e ∈ famEdges (starTriangles b (Mx b)) → a ∉ e := by
    intro a ha b hb hab heb hae
    have hmem := mem_insert_of_mem_star (fun g hg => hsub b hb g hg) heb a hae
    rcases Finset.mem_insert.1 hmem with hab' | hcon
    · exact hab hab'
    · exact (Finset.disjoint_left.1 hUW ha) (nbhdIn_subset H b W hcon)
  have hxe : x ∉ e := hnot x hx y hy hxy hey
  have hye : y ∉ e := hnot y hy x hx (Ne.symm hxy) hex
  exact (Finset.disjoint_left.1 (hpair hx hy hxy)
    (mem_famEdges_of_notMem_star hex hxe)) (mem_famEdges_of_notMem_star hey hye)

/-- **Assembly.**  Given a perfect matching `Mx x` of each apex neighbourhood `N_H(x,W)`, with the
matchings pairwise edge-disjoint, the stars over them decompose `H[U,W] ∪ H_V` for
`H_V = ⋃_{x ∈ U} Mx x ⊆ H[W]`, and `Δ_{H_V}(v) ≤ 2 d_H(v,U)`.

This is the assembly half of `BKLO.exists_triDecomp_of_budget`, with the greedy construction of the
matchings replaced by the matchings being given. -/
theorem exists_triDecomp_of_matchings {H : Finset (Sym2 V)} {U W : Finset V}
    {Mx : V → Finset (Finset V)} (hUW : Disjoint U W)
    (hgood : ∀ x ∈ U, GoodMatching H W x (Mx x))
    (hpair : (U : Set V).Pairwise (fun x y => Disjoint (famEdges (Mx x)) (famEdges (Mx y)))) :
    ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
      TriDecomp (edgesBtw H U W ∪ HV) ∧ ∀ v : V, edeg HV v ≤ 2 * degTo H v U := by
  classical
  have hstar := starTriangles_pairwise_of_matchings hUW
    (fun x hx e he => (hgood x hx).subset e he) hpair
  -- `H_V` is the union of the matchings, an edge set inside `W`
  have hHVsub : U.biUnion (fun x => famEdges (Mx x)) ⊆ edgesIn H W := by
    intro e he
    obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
    obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
    exact edgesIn_mono (nbhdIn_subset H x W) ((hgood x hx).edges f hf hef)
  -- the star union is exactly `H[U,W] ∪ H_V`
  have hSeq : U.biUnion (fun x => famEdges (starTriangles x (Mx x)))
      = edgesBtw H U W ∪ U.biUnion (fun x => famEdges (Mx x)) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro e he
      obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
      obtain ⟨tri, htri, hetri⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (by rwa [starTriangles] at htri)
      obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hetri
      by_cases hxe : x ∈ e
      · refine Finset.mem_union_left _ ?_
        obtain ⟨qq, rfl⟩ := Sym2.mem_iff_exists.1 hxe
        have hq : qq ∈ insert x f := hmem qq (by simp)
        have hqx : qq ≠ x := by
          intro hc
          rw [Sym2.isDiag_iff_proj_eq] at hnd
          exact hnd hc.symm
        have hqf : qq ∈ f := (Finset.mem_insert.1 hq).resolve_left hqx
        have hqN : qq ∈ nbhdIn H x W := (hgood x hx).subset f hf hqf
        rw [mem_nbhdIn] at hqN
        exact Finset.mem_filter.2 ⟨hqN.2, x, hx, qq, hqN.1, rfl⟩
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
        refine Finset.mem_biUnion.2 ⟨f, hf, mem_cliqueEdgesV.2 ⟨?_, hnd⟩⟩
        intro z hz
        rcases Finset.mem_insert.1 (hmem z hz) with hzx | hzf
        · exact absurd (hzx ▸ hz) hxe
        · exact hzf
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · obtain ⟨heH, a, haU, b, hbW, rfl⟩ := Finset.mem_filter.1 he
        have hbN : b ∈ nbhdIn H a W := mem_nbhdIn.2 ⟨hbW, heH⟩
        obtain ⟨f, hf, hbf⟩ := (hgood a haU).covers b hbN
        refine Finset.mem_biUnion.2 ⟨a, haU, Finset.mem_biUnion.2
          ⟨insert a f, Finset.mem_image_of_mem _ hf, mem_cliqueEdgesV.2 ⟨?_, ?_⟩⟩⟩
        · intro z hz
          rcases Sym2.mem_iff.1 hz with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hbf
        · rw [Sym2.isDiag_iff_proj_eq]
          intro hc
          have hab : a = b := hc
          exact (Finset.disjoint_left.1 hUW haU) (by rw [hab]; exact hbW)
      · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
        obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
        exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_biUnion.2
          ⟨insert x f, Finset.mem_image_of_mem _ hf,
            cliqueEdges_mono (Finset.subset_insert x f) hef⟩⟩
  refine ⟨U.biUnion (fun x => famEdges (Mx x)), hHVsub, ?_, ?_⟩
  · rw [← hSeq]
    exact triDecomp_biUnion_starTriangles (fun x hx => (hgood x hx).matching) hstar
  · intro v
    by_cases hvW : v ∈ W
    · have hvU : ∀ x ∈ U, v ≠ x := fun x hx hc => (Finset.disjoint_left.1 hUW hx) (hc ▸ hvW)
      have h1 : edeg (U.biUnion (fun x => famEdges (Mx x))) v
          ≤ edeg (U.biUnion (fun x => famEdges (starTriangles x (Mx x)))) v :=
        edeg_mono (by rw [hSeq]; exact Finset.subset_union_right) v
      have h2 := edeg_biUnion_starTriangles_le_two_degTo (H := H) (W := W)
        (fun x hx => (hgood x hx).matching) hvU (fun x hx e he => (hgood x hx).subset e he)
      exact le_trans h1 h2
    · have hzero : edeg (U.biUnion (fun x => famEdges (Mx x))) v = 0 := by
        unfold edeg
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hve
        exact hvW ((mem_edgesIn.1 (hHVsub he)).2 v hve)
      rw [hzero]
      exact Nat.zero_le _

/-! ### The pseudorandom `K₂`-factor core (BKLO Lemma 10.7)

This was the residual clause of the previous stage.  It is now **proved**, as
`BKLO.lemma107K2_holds` in `BKLO/Section107Core.lean`; consequently
`BKLO.lemma1010K3Hier_holds` and `BKLO.cor1011K3Hier_holds` hold unconditionally. -/

/-- **BKLO Lemma 10.7 (p. 31) / Corollary 10.9, for `r = 2`, in the configuration of Lemma 10.10.**

For `r = 2` a `K_r`-factor of the apex neighbourhood `H[N_H(x,V)]` is a **perfect matching**, which
exists by Dirac's theorem (`BKLO.perfectMatchingDirac_holds`) because hypothesis (ii) says
`δ(H[N_H(x,V)]) ≥ (1/2) d_H(x,V) + 18k√ρ³|V|`.  The content of Lemma 10.7 is that one perfect
matching can be chosen **for every apex simultaneously, pairwise edge-disjointly**, across the
`≤ kn` neighbourhoods; in the paper this is done by a random greedy process whose concentration is
Proposition 10.8 (Jain's Bernoulli domination).

This is the pseudorandom `K_r`-factor core, and nothing else on the route from §10.2 to
Lemma 10.10 is missing.  It is proved in `BKLO/Section107Core.lean` (`BKLO.lemma107K2_holds`):
there the random greedy process and Proposition 10.8 are replaced by a deterministic
pessimistic-estimator sweep, whose per-apex input — a perfect matching of small weight against the
potential — comes from averaging over the `s₂ + 1` pairwise edge-disjoint perfect matchings that
the Dirac slack of hypothesis (ii) supplies (`BKLO.exists_spread_involution`). -/
def Lemma107K2 : Prop :=
  ∀ (α ρ : ℝ) (k : ℕ), 0 < α → 0 < ρ → ρ < 1 → 0 < k → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (H : Finset (Sym2 V)) (S U W : Finset V),
      n₀ ≤ S.card → (∀ e ∈ H, ¬ e.IsDiag) → H ⊆ cliqueEdges S → U ⊆ S → W ⊆ S →
      Disjoint U W → (S.card : ℝ) / (k : ℝ) - 1 ≤ (W.card : ℝ) →
      (∀ x ∈ U, 2 ∣ degTo H x W) →
      (∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ)
          ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) →
      (∀ y ∈ W, (degTo H y U : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ)) →
      (∀ y ∈ W, ((1 : ℝ) / 2 + 2 * α) * (W.card : ℝ) ≤ (degTo H y W : ℝ)) →
      ∃ Mx : V → Finset (Finset V), (∀ x ∈ U, GoodMatching H W x (Mx x)) ∧
        (U : Set V).Pairwise (fun x y => Disjoint (famEdges (Mx x)) (famEdges (Mx y)))

/-! ### Lemma 10.10 with the paper's hierarchy -/

/-- **BKLO Lemma 10.10, p. 32, for `r = 2` and `F = K₃`, with the hierarchy restored.**

This is `BKLO.Lemma1010K3` together with the single extra hypothesis `2kρ ≤ α`, which is a
consequence of the paper's hierarchy `1/n ≪ ρ ≪ α, 1/k` and is *necessary*: by
`BKLO.degTo_le_edeg_of_triDecomp`, any `H'_V` as in the conclusion satisfies
`Δ(H'_V) ≥ max_{y ∈ V} d_H(y,U)`, and hypothesis (iv) allows `d_H(y,U)` to be as large as
`2kρ|V|`, so `Δ(H'_V) ≤ 2α|V|` forces `kρ ≲ α`. -/
def Lemma1010K3Hier : Prop :=
  ∀ (α ρ : ℝ) (k : ℕ), 0 < α → 0 < ρ → ρ < 1 → 0 < k → 2 * (k : ℝ) * ρ ≤ α →
    ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (H : Finset (Sym2 V)) (S U W : Finset V),
      n₀ ≤ S.card → (∀ e ∈ H, ¬ e.IsDiag) → H ⊆ cliqueEdges S → U ⊆ S → W ⊆ S →
      Disjoint U W → (S.card : ℝ) / (k : ℝ) - 1 ≤ (W.card : ℝ) →
      (∀ x ∈ U, 2 ∣ degTo H x W) →
      (∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ)
          ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) →
      (∀ y ∈ W, (degTo H y U : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ)) →
      (∀ y ∈ W, ((1 : ℝ) / 2 + 2 * α) * (W.card : ℝ) ≤ (degTo H y W : ℝ)) →
      ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
        TriDecomp (edgesBtw H U W ∪ HV) ∧ ∀ v : V, (edeg HV v : ℝ) ≤ 2 * α * (W.card : ℝ)

/-- **Lemma 10.10 for `r = 2` follows from the pseudorandom `K₂`-factor core.**  Given the
edge-disjoint perfect matchings of Lemma 10.7, the stars over them decompose `H[U,V] ∪ H'_V` and
the resulting `H'_V` has `Δ(H'_V) ≤ 2 max_y d_H(y,U) ≤ 4kρ|V| ≤ 2α|V|` by hypothesis (iv) and the
hierarchy. -/
theorem lemma1010K3Hier_of_lemma107K2 (h107 : Lemma107K2) : Lemma1010K3Hier := by
  intro α ρ k hα hρ hρ1 hk hhier
  obtain ⟨n₀, h⟩ := h107 α ρ k hα hρ hρ1 hk
  refine ⟨n₀, ?_⟩
  intro V _ H S U W hS hloop hHS hUS hWS hUW hWcard hdvd hii hiii hiv hv
  obtain ⟨Mx, hgood, hpair⟩ :=
    h H S U W hS hloop hHS hUS hWS hUW hWcard hdvd hii hiii hiv hv
  obtain ⟨HV, hsub, hdec, hdeg⟩ := exists_triDecomp_of_matchings hUW hgood hpair
  refine ⟨HV, hsub, hdec, ?_⟩
  intro v
  have hWpos : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
  by_cases hvW : v ∈ W
  · have h1 : (edeg HV v : ℝ) ≤ 2 * (degTo H v U : ℝ) := by exact_mod_cast hdeg v
    have h2 := hiv v hvW
    nlinarith
  · have hzero : edeg HV v = 0 := by
      unfold edeg
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hve
      exact hvW ((mem_edgesIn.1 (hsub he)).2 v hve)
    rw [hzero]
    have : (0 : ℝ) ≤ 2 * α * (W.card : ℝ) := by positivity
    simpa using this

/-! ### Corollary 10.11 with the hierarchy -/

/-- **BKLO Corollary 10.11, p. 32, for `r = 2`, with the hierarchy restored.**  This is
`BKLO.Cor1011K3` with the same extra hypothesis `2kρ ≤ α` as `BKLO.Lemma1010K3Hier`. -/
def Cor1011K3Hier : Prop :=
  ∀ (α ρ : ℝ) (k : ℕ), 0 < α → 0 < ρ → ρ < 1 → 0 < k → 2 * (k : ℝ) * ρ ≤ α →
    ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (H : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V))
      (idx : Finset V → ℕ),
      n₀ ≤ S.card → (∀ e ∈ H, ¬ e.IsDiag) → H ⊆ cliqueEdges S →
      IsEquitablePartition k P S →
      (∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → idx W ≠ idx W') →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, 2 ∣ degTo H x W) →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ)
          ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ x' ∈ beforeParts P idx W, x ≠ x' →
        (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) →
      (∀ W ∈ P, ∀ y ∈ W, (degTo H y (beforeParts P idx W) : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ)) →
      (∀ W ∈ P, ∀ y ∈ W, ((1 : ℝ) / 2 + 2 * α) * (W.card : ℝ) ≤ (degTo H y W : ℝ)) →
      ∃ H₀ : Finset (Sym2 V), H₀ ⊆ insideParts H P ∧
        TriDecomp (crossParts H P ∪ H₀) ∧ ∀ v : V, (edeg H₀ v : ℝ) ≤ 2 * α * (S.card : ℝ)

/-- **Corollary 10.11 with the hierarchy, from Lemma 10.10 with the hierarchy.**  The deduction is
the one of `BKLO.cor1011K3_of_lemma1010K3`: apply the lemma once per part `W`, with `U = V_{<W}`;
the crossing edges split as `crossParts H P = ⋃_W H[V_{<W}, W]`, an edge-disjoint union, so the
triangle decompositions concatenate. -/
theorem cor1011K3Hier_of_lemma1010K3Hier (h1010 : Lemma1010K3Hier) : Cor1011K3Hier := by
  intro α ρ k hα hρ hρ1 hk hhier
  obtain ⟨n₀, hn₀⟩ := h1010 α ρ k hα hρ hρ1 hk hhier
  refine ⟨n₀, ?_⟩
  intro V _ H S P idx hcard hloop hHS heq hidx hdvd hmin hcodeg hUdeg hWdeg
  classical
  -- apply Lemma 10.10 to each part
  have hstep : ∀ W ∈ P, ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
      TriDecomp (edgesBtw H (beforeParts P idx W) W ∪ HV) ∧
      ∀ v : V, (edeg HV v : ℝ) ≤ 2 * α * (W.card : ℝ) := by
    intro W hW
    refine hn₀ H S (beforeParts P idx W) W hcard hloop hHS (beforeParts_subset heq idx W)
      (heq.subset_of_mem hW) (disjoint_beforeParts_self heq hW) ?_ (hdvd W hW) (hmin W hW)
      (hcodeg W hW) (hUdeg W hW) (hWdeg W hW)
    -- `|S|/k - 1 ≤ |W|`
    have hlow : (S.card / k : ℕ) ≤ W.card := heq.size_lower W hW
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hdiv : (S.card : ℝ) / (k : ℝ) - 1 ≤ ((S.card / k : ℕ) : ℝ) := by
      have hle : (S.card : ℝ) < ((S.card / k : ℕ) : ℝ) * (k : ℝ) + (k : ℝ) := by
        have h2 : S.card < (S.card / k) * k + k := Nat.lt_div_mul_add hk
        exact_mod_cast h2
      rw [sub_le_iff_le_add, div_le_iff₀ hkpos]
      nlinarith only [hle, hkpos]
    have hcast : ((S.card / k : ℕ) : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hlow
    linarith
  choose! HV hHVsub hHVdec hHVdeg using hstep
  refine ⟨P.biUnion HV, ?_, ?_, ?_⟩
  · -- `H₀ ⊆ insideParts H P`
    intro e he
    obtain ⟨W, hW, heW⟩ := Finset.mem_biUnion.1 he
    exact edgesIn_subset_insideParts hW (hHVsub W hW heW)
  · -- the triangle decomposition
    have hsplit : crossParts H P ∪ P.biUnion HV
        = P.biUnion (fun W => edgesBtw H (beforeParts P idx W) W ∪ HV W) := by
      rw [crossParts_eq_biUnion_edgesBtw heq hHS hloop hidx, ← Finset.biUnion_union]
    rw [hsplit]
    refine TriDecomp.biUnion (fun W hW => hHVdec W hW) ?_
    intro W₁ hW₁ W₂ hW₂ hne
    have hcross₁ : edgesBtw H (beforeParts P idx W₁) W₁ ⊆ crossParts H P :=
      edgesBtw_beforeParts_subset_crossParts heq hW₁
    have hcross₂ : edgesBtw H (beforeParts P idx W₂) W₂ ⊆ crossParts H P :=
      edgesBtw_beforeParts_subset_crossParts heq hW₂
    have hin₁ : HV W₁ ⊆ insideParts H P :=
      (hHVsub W₁ hW₁).trans (edgesIn_subset_insideParts hW₁)
    have hin₂ : HV W₂ ⊆ insideParts H P :=
      (hHVsub W₂ hW₂).trans (edgesIn_subset_insideParts hW₂)
    have hci := disjoint_crossParts_insideParts H P
    refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩ <;>
      refine Finset.disjoint_union_right.2 ⟨?_, ?_⟩
    · exact disjoint_edgesBtw_beforeParts heq hW₁ hW₂ hne
    · exact Finset.disjoint_of_subset_left hcross₁ (Finset.disjoint_of_subset_right hin₂ hci)
    · exact (Finset.disjoint_of_subset_left hcross₂
        (Finset.disjoint_of_subset_right hin₁ hci)).symm
    · exact Finset.disjoint_of_subset_left (hHVsub W₁ hW₁)
        (Finset.disjoint_of_subset_right (hHVsub W₂ hW₂)
          (disjoint_edgesIn_parts heq hW₁ hW₂ hne))
  · -- the degree bound
    intro v
    by_cases hv : ∃ W ∈ P, v ∈ W
    · obtain ⟨W₀, hW₀, hvW₀⟩ := hv
      have hzero : ∀ W ∈ P, W ≠ W₀ → edeg (HV W) v = 0 := by
        intro W hW hne
        have hvW : v ∉ W := fun hc => hne (heq.eq_of_mem hW hW₀ hc hvW₀)
        have hz := edeg_edgesIn_eq_zero (H := H) hvW
        exact Nat.le_zero.1 (hz ▸ edeg_mono (hHVsub W hW) v)
      have hsub : (P.biUnion HV).filter (fun e => v ∈ e) ⊆ (HV W₀).filter (fun e => v ∈ e) := by
        intro e he
        obtain ⟨heB, hve⟩ := Finset.mem_filter.1 he
        obtain ⟨W, hW, heW⟩ := Finset.mem_biUnion.1 heB
        by_cases hWW : W = W₀
        · exact Finset.mem_filter.2 ⟨hWW ▸ heW, hve⟩
        · exfalso
          have h0 := hzero W hW hWW
          rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
          exact h0 heW hve
      have hle : edeg (P.biUnion HV) v ≤ edeg (HV W₀) v := Finset.card_le_card hsub
      have h1 : (edeg (P.biUnion HV) v : ℝ) ≤ (edeg (HV W₀) v : ℝ) := by exact_mod_cast hle
      have h2 := hHVdeg W₀ hW₀ v
      have h3 : (W₀.card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (heq.subset_of_mem hW₀)
      nlinarith [hα.le]
    · push_neg at hv
      have hzero : edeg (P.biUnion HV) v = 0 := by
        rw [edeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hve
        obtain ⟨W, hW, heW⟩ := Finset.mem_biUnion.1 he
        exact hv W hW ((mem_edgesIn.1 (hHVsub W hW heW)).2 v hve)
      rw [hzero]
      have hnn : (0 : ℝ) ≤ 2 * α * (S.card : ℝ) := by positivity
      simpa using hnn

end BKLO
