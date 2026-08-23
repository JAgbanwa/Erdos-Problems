/-
# What flexible shell absorption asks for, and where the transformer construction stops.

`BKLO/CoverDownAbsorberConfinement.lean` isolates `BKLO.ShellAbsorption`: the **flexible**
(`∃ R, ∀ L`) reservation that, together with the dense max-degree nibble, gives the repaired
cover-down step `BKLO.CoverDownK3Div`.  This file records, `sorry`-free, the three facts that decide
what a construction of `ShellAbsorption` may and may not look like.  Nothing here asserts
`ShellAbsorption`, and nothing here weakens any statement of the development.

The intended construction is BKLO §8 absorption: reserve a bounded structure and let
`BKLO.absorber_of_transformer` turn a transformer into an absorber, with the gadgets of
`BKLO.Gadgets` placed inside `W' \ W''` by `BKLO.exists_placement`.  Two of its steps are impossible
as such, for reasons that are structural rather than numerical — they do not depend on any size, so
no re-parametrisation (fewer gadgets, shared gadgets, a linear instead of a quadratic reservation)
avoids them.

## 1.  No structure absorbs a single edge — the "with `e` / without `e`" mode does not exist

`BKLO.triDivisible_of_isAbsorber`: if `IsAbsorber A H` then `H` is triangle-divisible.  Both
`A` and `A ∪ H` are triangle-decomposable, hence have all degrees even and a multiple of three many
edges, and `A` and `H` are disjoint; so `H` inherits both.  In particular
`BKLO.not_isAbsorber_singleton`: **no** `A` satisfies `IsAbsorber A {e}`.

So an absorbing gadget that is triangle-decomposable both with a potential leftover edge `e` present
and with `e` absent cannot exist — for any `e`, at any size, and whether the gadget is dedicated to
`e` or shared between many potential edges.  Absorption is never per-edge: the object that must be
divisible is the whole remainder `R ∪ L`, which is exactly the hypothesis the interface carries.

## 2.  Inside `W'` there is no help for the *far* part of the shell

`BKLO.far_edge_cherry_of_confined_cover`: in the conclusion of `ShellAbsorption` — an edge-disjoint
triangle family `Q` with `R ∪ L ⊆ famEdges Q ⊆ (R ∪ L) ∪ (cliqueEdges W' \ cliqueEdges W'')` — every
edge of `R ∪ L` with **both** endpoints outside `W'` lies in a triangle whose other two edges are
again in `R ∪ L`.  The reason is immediate: an edge at a vertex outside `W'` is never an edge inside
`W'`, so the confinement clause leaves it no option but `R ∪ L`.

This is what stops the placement route.  `BKLO.exists_placement` places gadgets on fresh host
vertices; here the only vertices the confinement clause allows for gadget internals are those of
`W' \ W''`, and by the above a gadget placed there can carry no edge of a triangle covering a far
edge.  The far part of `R ∪ L` must be covered by triangles of `R ∪ L` itself, i.e. the reservation
has to make the far part of the remainder *self*-decomposable, at the scale of `W`.

## 3.  The confinement allowance can be empty: hollow instances

The interface requires `F ∩ cliqueEdges W'` and `F ∩ cliqueEdges W''` to be triangle-divisible, and
`F` to have min degree `≥ c|W|` with `c > 9/10`; it does **not** require `F` to have any edge inside
`W'` at all.  Both requirements are met by the empty edge set, and since `|W'| ≤ |W| / K` a graph of
min degree `c|W|` can perfectly well avoid `W'` internally.  `BKLO.hollow_instance_realizable`
exhibits, for every `c < 1`, every ratio `K` with `1/(1-c) ≤ K`, and arbitrarily large `|W|`, a
configuration satisfying **all** hypotheses of `ShellAbsorption` and with `F ∩ cliqueEdges W' = ∅`.

In such an instance `TriFamilyIn F Q` forces every edge of every triangle into `F`, so no edge
inside `W'` is usable at all, and `BKLO.triDecomp_of_confined_cover_of_hollow` gives
`famEdges Q = R ∪ L`.  Consequently — `BKLO.shellAbsorption_forces_sparse_selfdecomposition` —
`ShellAbsorption` entails:

> there is a reservation `R` of max degree `≤ ρ|W|` inside `F` such that **for every** admissible
> leftover `L` of max degree `≤ η|W|` with `R ∪ L` triangle-divisible, the graph `R ∪ L` is
> *exactly* triangle-decomposable.

By `BKLO.shellAbsorption_input_sparse` the graph `R ∪ L` has max degree `≤ (ρ + η)|W|`: it is an
arbitrarily **sparse** graph spanning `W`, and it must be decomposed with no outside help whatsoever.
That is the wall.  It is not a counting failure — the reservation is allowed `ρ|W|²/2` edges against
a leftover of `η|W|²/2`, and `η` is ours to choose — and it is not the (correctly rejected) demand
for one dedicated gadget per potential leftover edge.  It is that the object to be produced is a
robustly decomposable *sparse* structure: neither BKLO §8 (whose absorbers are built on **fresh**
vertices, after the divisible set `H` is known — `BKLO.sparseAbsorberExistence_nine` is `∀ H, ∃ A`)
nor the dense-graph inputs of §4 supply one, and the project contains no component that does.
BKLO's own cover-down does not meet this wall because there the vortex levels are *dense*
(`G[W_i]` has min degree `≥ c|W_i|`), so the level `W'` supplies the covering edges; the interface
as stated in `BKLO/CoverDownAbsorberConfinement.lean` omits that hypothesis, and §3 above shows the
omission is not harmless.

None of this refutes `ShellAbsorption`: no statement here is a counterexample to it, and the
counting is comfortable in every direction (the reservation is allowed a degree `ρ|W|` against a
leftover of degree `η|W|` with `η` chosen afterwards, so `R` may be quadratic in size and still
legal).  What the three facts do is locate, exactly, the step at which a reserved-transformer
construction stops: the object that would have to be produced is a *sparse* structure that stays
triangle-decomposable after **any** admissible sparse divisible leftover is added to it, and it must
be produced before the leftover is seen.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownAbsorberConfinement

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### 1.  Absorption is never per-edge -/

/-- **An absorber forces divisibility.**  If `A` absorbs `H` then `H` is triangle-divisible: `A` and
`A ∪ H` are both decomposable, hence have even degrees and `3 ∣` many edges, and `A` and `H` are
disjoint. -/
theorem triDivisible_of_isAbsorber {A H : Finset (Sym2 V)} (h : IsAbsorber A H) :
    TriDivisible H := by
  obtain ⟨hd, hA, hAH⟩ := h
  obtain ⟨hAe, hAc⟩ := hA.triDivisible
  obtain ⟨hUe, hUc⟩ := hAH.triDivisible
  refine ⟨fun v => ?_, ?_⟩
  · show Even (edeg H v)
    have h1 : edeg (A ∪ H) v = edeg A v + edeg H v := edeg_union_of_disjoint hd v
    have h2 : edeg (A ∪ H) v % 2 = 0 := Nat.even_iff.1 (hUe v)
    have h3 : edeg A v % 2 = 0 := Nat.even_iff.1 (hAe v)
    rw [h1] at h2
    exact Nat.even_iff.2 (by omega)
  · have hcard : (A ∪ H).card = A.card + H.card := Finset.card_union_of_disjoint hd
    rw [hcard] at hUc
    omega

/-- **No gadget absorbs a single edge.**  There is no edge set that is triangle-decomposable both
with `e` present and with `e` absent, at any size, dedicated or shared.  So the "with `e` / without
`e`" mode of a placed gadget template does not exist; only a *divisible* remainder can be absorbed,
which is why `BKLO.ShellAbsorption` carries `TriDivisible (R ∪ L)`. -/
theorem not_isAbsorber_singleton {A : Finset (Sym2 V)} {e : Sym2 V} : ¬ IsAbsorber A {e} := by
  intro h
  have := (triDivisible_of_isAbsorber h).2
  simp at this

/-! ### 2.  The confinement clause gives the far part of the shell no help -/

/-- **Far edges are covered from inside the remainder.**  If an edge-disjoint triangle family `Q`
covers `S` and uses, besides `S`, only edges inside `W'` (and none inside `W''`), then every edge of
`S` with both endpoints outside `W'` lies in a triangle whose other two edges are again in `S`.

Applied to `S = R ∪ L` in the conclusion of `BKLO.ShellAbsorption`, this says that gadget internals
placed inside `W' \ W''` are useless for the far part of the shell: the reservation must make the
far part of the remainder self-decomposable. -/
theorem far_edge_cherry_of_confined_cover
    {W' W'' : Finset V} {F S : Finset (Sym2 V)} {Q : Finset (Finset V)}
    (hQ : TriFamilyIn F Q) (hcov : S ⊆ famEdges Q)
    (hconf : famEdges Q ⊆ S ∪ (cliqueEdges W' \ cliqueEdges W''))
    {u v : V} (hu : u ∉ W') (hv : v ∉ W') (he : s(u, v) ∈ S) :
    ∃ w : V, u ≠ w ∧ v ≠ w ∧ s(u, w) ∈ S ∧ s(v, w) ∈ S := by
  classical
  obtain ⟨t, htQ, het⟩ := Finset.mem_biUnion.1 (hcov he)
  obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 het
  have hut : u ∈ t := hmem u (by simp)
  have hvt : v ∈ t := hmem v (by simp)
  have huv : u ≠ v := by
    intro h; exact hnd (by simp [Sym2.isDiag_iff_proj_eq, h])
  have h3 : t.card = 3 := hQ.1 t htQ
  have hsub : ({u, v} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [hut, hvt]
  have hcard2 : ({u, v} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using huv), Finset.card_singleton]
  have hone : (t \ ({u, v} : Finset V)).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, h3, hcard2]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.1 hone
  have hwmem : w ∈ t \ ({u, v} : Finset V) := by rw [hw]; exact Finset.mem_singleton_self w
  obtain ⟨hwt, hwuv⟩ := Finset.mem_sdiff.1 hwmem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwuv
  have hedge : ∀ x : V, x ∈ t → x ≠ w → x ∉ W' → s(x, w) ∈ S := by
    intro x hxt hxw hxW'
    have h1 : s(x, w) ∈ cliqueEdges t := by
      refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
      · intro y hy
        rcases Sym2.mem_iff.1 hy with rfl | rfl
        exacts [hxt, hwt]
      · simp [Sym2.isDiag_iff_proj_eq, hxw]
    have h2 : s(x, w) ∈ famEdges Q := Finset.subset_biUnion_of_mem cliqueEdges htQ h1
    rcases Finset.mem_union.1 (hconf h2) with h | h
    · exact h
    · exact absurd ((mem_cliqueEdgesV.1 (Finset.mem_sdiff.1 h).1).1 x (by simp)) hxW'
  exact ⟨w, fun h => hwuv.1 h.symm, fun h => hwuv.2 h.symm,
    hedge u hut (fun h => hwuv.1 h.symm) hu, hedge v hvt (fun h => hwuv.2 h.symm) hv⟩

/-! ### 3.  Hollow instances: the confinement allowance is empty -/

/-- **In a hollow instance the cover is exact.**  If `F` has no edge inside `W'`, a confined cover of
`S` uses nothing but `S`, so `S` is triangle-decomposable outright. -/
theorem triDecomp_of_confined_cover_of_hollow
    {W' W'' : Finset V} {F S : Finset (Sym2 V)} {Q : Finset (Finset V)}
    (hhollow : F ∩ cliqueEdges W' = ∅) (hQ : TriFamilyIn F Q) (hcov : S ⊆ famEdges Q)
    (hconf : famEdges Q ⊆ S ∪ (cliqueEdges W' \ cliqueEdges W'')) :
    famEdges Q = S ∧ TriDecomp S := by
  classical
  have hQF : famEdges Q ⊆ F := famEdges_subset_of_triFamilyIn hQ
  have hsub : famEdges Q ⊆ S := by
    intro e he
    rcases Finset.mem_union.1 (hconf he) with h | h
    · exact h
    · have : e ∈ F ∩ cliqueEdges W' := Finset.mem_inter.2 ⟨hQF he, (Finset.mem_sdiff.1 h).1⟩
      rw [hhollow] at this
      exact absurd this (Finset.notMem_empty e)
  have heq : famEdges Q = S := Finset.Subset.antisymm hsub hcov
  exact ⟨heq, heq ▸ hQ.triDecomp⟩

/-! ### The hollow configuration -/

/-- `3 ∣ binom(n,2)` when `n ≡ 3 (mod 6)`. -/
theorem three_dvd_choose_two {n q : ℕ} (h : n = 6 * q + 3) : 3 ∣ n.choose 2 := by
  subst h
  have h2 : 2 * (6 * q + 3).choose 2 = (6 * q + 3) * ((6 * q + 3) - 1) := two_mul_choose_two _
  have h3 : (6 * q + 3) - 1 = 6 * q + 2 := by omega
  rw [h3] at h2
  have h4 : (6 * q + 3) * (6 * q + 2) = 36 * (q * q) + 30 * q + 6 := by ring
  rw [h4] at h2
  omega

/-- Off its own vertex set the clique edge set has no degree. -/
theorem edeg_cliqueEdges_of_notMem {S : Finset V} {v : V} (hv : v ∉ S) :
    edeg (cliqueEdges S) v = 0 := by
  classical
  have h : (cliqueEdges S).filter (fun e => v ∈ e) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun e he hve => hv ((mem_cliqueEdgesV.1 he).1 v hve)
  unfold edeg
  rw [h, Finset.card_empty]

/-- The empty edge set is triangle-divisible. -/
theorem triDivisible_empty_edges : TriDivisible (∅ : Finset (Sym2 V)) :=
  ⟨fun v => by simp [edeg], by simp⟩

/-- **The hollow configuration, at prescribed sizes.**  On `N ≡ 3 (mod 6)` vertices, with a level
`W'` of `M ≡ 3 (mod 6)` vertices, the complete graph *with the edges inside `W'` deleted* satisfies
every hypothesis of `BKLO.ShellAbsorption` and has no edge inside `W'`.

Its minimum degree is `N - M ≥ (1 - 1/K)N ≥ cN`, which is why the ratio has to satisfy
`1/(1-c) ≤ K`; the divisibility of the two levels is the divisibility of the empty edge set. -/
theorem hollow_instance_of_sizes {c : ℝ} (hc : c < 1) {K N M a b : ℕ} (hK : 2 ≤ K)
    (hKc : 1 / (1 - c) ≤ (K : ℝ)) (hN : N = 6 * b + 3) (hM : M = 6 * a + 3)
    (hKM : K * M ≤ N) (hKKM : N ≤ K * K * M) (hMK : 3 * K ≤ M) :
    ∃ (W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
      (univ : Finset (Fin N)).card = N ∧ W'' ⊆ W' ∧
      K * W'.card ≤ N ∧ N ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
      F ⊆ cliqueEdges (univ : Finset (Fin N)) ∧ TriDivisible F ∧
      TriDivisible (F ∩ cliqueEdges W') ∧ TriDivisible (F ∩ cliqueEdges W'') ∧
      (∀ v ∈ (univ : Finset (Fin N)), c * (N : ℝ) ≤ (edeg F v : ℝ)) ∧
      F ∩ cliqueEdges W' = ∅ ∧ (F \ cliqueEdges W').Nonempty := by
  classical
  have hc1 : (0 : ℝ) < 1 - c := by linarith
  have hMle : M ≤ K * M := Nat.le_mul_of_pos_left M (by omega)
  have hM2 : 2 * M ≤ K * M := Nat.mul_le_mul_right _ hK
  have hMN : M ≤ N := le_trans hMle hKM
  have hcardU : (univ : Finset (Fin N)).card = N := by simp
  obtain ⟨W', hW'sub, hW'card⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset (Fin N))) (n := M)
      (by rw [hcardU]; exact hMN)
  obtain ⟨W'', hW''sub, hW''card⟩ :=
    Finset.exists_subset_card_eq (s := W') (n := 3) (by rw [hW'card]; omega)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Sym2 (Fin N)),
      F = cliqueEdges (univ : Finset (Fin N)) \ cliqueEdges W' := ⟨_, rfl⟩
  -- degrees
  have hdeg : ∀ v : Fin N, edeg (cliqueEdges W') v + edeg F v = N - 1 := by
    intro v
    have h := edeg_sdiff_add (cliqueEdges_mono (Finset.subset_univ W')) v
    rw [← hF] at h
    have h2 : edeg (cliqueEdges (univ : Finset (Fin N))) v = N - 1 := by
      rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcardU]
    rw [h2] at h
    exact h
  have hdegW' : ∀ v ∈ W', edeg F v = N - M := by
    intro v hv
    have h := hdeg v
    rw [edeg_cliqueEdges_of_mem hv, hW'card] at h
    omega
  have hdegOut : ∀ v : Fin N, v ∉ W' → edeg F v = N - 1 := by
    intro v hv
    have h := hdeg v
    rw [edeg_cliqueEdges_of_notMem hv] at h
    omega
  have hdegge : ∀ v : Fin N, N - M ≤ edeg F v := by
    intro v
    by_cases hv : v ∈ W'
    · rw [hdegW' v hv]
    · rw [hdegOut v hv]; omega
  -- no edge inside `W'`
  have hhollow : F ∩ cliqueEdges W' = ∅ := by
    rw [hF]
    ext e
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and]
    tauto
  have hnotin : ∀ e ∈ F, e ∉ cliqueEdges W' := by
    intro e he hmem
    have h : e ∈ F ∩ cliqueEdges W' := Finset.mem_inter.2 ⟨he, hmem⟩
    rw [hhollow] at h
    exact absurd h (Finset.notMem_empty e)
  have hhollow'' : F ∩ cliqueEdges W'' = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨heF, heW''⟩ := Finset.mem_inter.1 he
    exact hnotin e heF (cliqueEdges_mono hW''sub heW'')
  -- divisibility of `F`
  have hcardF : F.card = N.choose 2 - M.choose 2 := by
    rw [hF, Finset.card_sdiff_of_subset (cliqueEdges_mono (Finset.subset_univ W')),
      card_cliqueEdges, card_cliqueEdges, hcardU, hW'card]
  have hchN : 3 ∣ N.choose 2 := three_dvd_choose_two (q := b) hN
  have hchM : 3 ∣ M.choose 2 := three_dvd_choose_two (q := a) hM
  have hchle : M.choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 hMN
  have hdivF : TriDivisible F := by
    refine ⟨fun v => ?_, ?_⟩
    · show Even (edeg F v)
      by_cases hv : v ∈ W'
      · rw [hdegW' v hv]
        refine Nat.even_iff.2 ?_
        omega
      · rw [hdegOut v hv]
        exact Nat.even_iff.2 (by omega)
    · show 3 ∣ F.card
      rw [hcardF]
      omega
  -- minimum degree
  have hmindeg : ∀ v ∈ (univ : Finset (Fin N)), c * (N : ℝ) ≤ (edeg F v : ℝ) := by
    intro v _
    have hMbound : (M : ℝ) ≤ (1 - c) * (N : ℝ) := by
      have h1 : (K : ℝ) * (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKM
      have hKpos : (0 : ℝ) < (K : ℝ) := by
        have hK0 : 0 < K := by omega
        exact_mod_cast hK0
      have h2 : (1 : ℝ) ≤ (1 - c) * (K : ℝ) := by
        rw [div_le_iff₀ hc1] at hKc
        linarith
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith
    have hcast : ((N - M : ℕ) : ℝ) = (N : ℝ) - (M : ℝ) := Nat.cast_sub hMN
    have h3 : ((N - M : ℕ) : ℝ) ≤ (edeg F v : ℝ) := by exact_mod_cast hdegge v
    rw [hcast] at h3
    linarith
  -- the shell is nonempty
  have hout : 2 ≤ ((univ : Finset (Fin N)) \ W').card := by
    rw [Finset.card_sdiff_of_subset hW'sub, hcardU, hW'card]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < ((univ : Finset (Fin N)) \ W').card)
  have hxW' : x ∉ W' := (Finset.mem_sdiff.1 hx).2
  have hyW' : y ∉ W' := (Finset.mem_sdiff.1 hy).2
  have hedge : s(x, y) ∈ F := by
    rw [hF]
    refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
    · exact mem_cliqueEdgesV.2 ⟨fun z _ => Finset.mem_univ z, by
        simp [Sym2.isDiag_iff_proj_eq, hxy]⟩
    · intro hmem
      exact hxW' ((mem_cliqueEdgesV.1 hmem).1 x (by simp))
  refine ⟨W', W'', F, hcardU, hW''sub, ?_, ?_, ?_, ?_, hdivF, ?_, ?_, hmindeg, hhollow, ?_⟩
  · rw [hW'card]; exact hKM
  · rw [hW'card]; exact hKKM
  · rw [hW'card, hW''card]; omega
  · rw [hF]; exact Finset.sdiff_subset
  · rw [hhollow]; exact triDivisible_empty_edges
  · rw [hhollow'']; exact triDivisible_empty_edges
  · exact ⟨s(x, y), Finset.mem_sdiff.2 ⟨hedge, hnotin _ hedge⟩⟩

/-- **Hollow instances are legitimate, at every size.**  For every density `c < 1`, every ratio `K`
with `1/(1-c) ≤ K` and every size threshold, there is a configuration satisfying *all* hypotheses of
`BKLO.ShellAbsorption` in which `F` has **no** edge inside `W'`.  So the confinement allowance
`cliqueEdges W' \ cliqueEdges W''` of the conclusion can be entirely unusable: with
`TriFamilyIn F Q` demanding every triangle edge in `F`, a hollow instance leaves the covering family
nothing but `R ∪ L` itself. -/
theorem hollow_instance_realizable {c : ℝ} (hc : c < 1) {K : ℕ} (hK : 2 ≤ K)
    (hKc : 1 / (1 - c) ≤ (K : ℝ)) (n₀ : ℕ) :
    ∃ (N : ℕ) (W W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
      n₀ ≤ W.card ∧ W' ⊆ W ∧ W'' ⊆ W' ∧
      K * W'.card ≤ W.card ∧ W.card ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
      F ⊆ cliqueEdges W ∧ TriDivisible F ∧
      TriDivisible (F ∩ cliqueEdges W') ∧ TriDivisible (F ∩ cliqueEdges W'') ∧
      (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) ∧
      F ∩ cliqueEdges W' = ∅ ∧ (F \ cliqueEdges W').Nonempty := by
  classical
  obtain ⟨a, M, hM, hMK, hMn⟩ : ∃ a M : ℕ, M = 6 * a + 3 ∧ 3 * K ≤ M ∧ n₀ ≤ M :=
    ⟨n₀ + K, 6 * (n₀ + K) + 3, rfl, by omega, by omega⟩
  obtain ⟨b, N, hN, hKM, hKKM⟩ : ∃ b N : ℕ, N = 6 * b + 3 ∧ K * M ≤ N ∧ N ≤ K * K * M := by
    refine ⟨(K * M) / 6 + 1, 6 * ((K * M) / 6 + 1) + 3, rfl, by omega, ?_⟩
    have h1 : 2 * (K * M) ≤ K * (K * M) := Nat.mul_le_mul_right _ hK
    have h2 : 2 * M ≤ K * M := Nat.mul_le_mul_right _ hK
    have h3 : K * K * M = K * (K * M) := by ring
    omega
  obtain ⟨W', W'', F, hcardU, hW''sub, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    hollow_instance_of_sizes (c := c) hc (K := K) (N := N) (M := M) (a := a) (b := b)
      hK hKc hN hM hKM hKKM hMK
  have hMle : M ≤ K * M := Nat.le_mul_of_pos_left M (by omega)
  refine ⟨N, univ, W', W'', F, ?_, Finset.subset_univ _, hW''sub, ?_, ?_, h3, h4, h5, h6, h7,
    ?_, h9, h10⟩
  · rw [hcardU]; omega
  · rw [hcardU]; exact h1
  · rw [hcardU]; exact h2
  · intro v hv
    rw [hcardU]
    exact h8 v hv

/-! ### What `ShellAbsorption` therefore asks for -/

/-- **The wall.**  `BKLO.ShellAbsorption` entails, at arbitrarily large sizes, a *reserved*
(`∃ R, ∀ L`) triangle decomposition of an arbitrarily **sparse** graph spanning `W`, with no outside
help at all:

there is `R ⊆ F` of max degree `≤ ρ|W|` such that for **every** `L ⊆ F \ R` of max degree `≤ η|W|`
with `R ∪ L` triangle-divisible, the graph `R ∪ L` is exactly triangle-decomposable.

The instance is the hollow one of `BKLO.hollow_instance_realizable`, where `F` has no edge inside
`W'`, so `TriFamilyIn F Q` makes the confinement allowance `cliqueEdges W' \ cliqueEdges W''`
unusable and the covering family can consist only of edges of `R ∪ L`.  By
`BKLO.shellAbsorption_input_sparse` the graph `R ∪ L` has max degree `≤ (ρ + η)|W|`.

Neither BKLO §8 — whose absorbers use **fresh** vertices and are produced *after* the divisible set
is known (`∀ H, ∃ A`) — nor the dense-graph inputs of §4 produce such an object; this is the exact
step at which the reserved-transformer construction stops. -/
theorem shellAbsorption_forces_sparse_selfdecomposition (hAbs : ShellAbsorption)
    {c γ ρ : ℝ} {K : ℕ} (hc : 9 / 10 < c) (hc1 : c < 1) (hγ : 0 < γ) (hρ : 0 < ρ) (hK : 2 ≤ K)
    (hKc : 1 / (1 - c) ≤ (K : ℝ)) (n₀ : ℕ) :
    ∃ η : ℝ, 0 < η ∧
      ∃ (N : ℕ) (W W' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
        n₀ ≤ W.card ∧ W' ⊆ W ∧ F ⊆ cliqueEdges W ∧ (F \ cliqueEdges W').Nonempty ∧
        F ∩ cliqueEdges W' = ∅ ∧
        ∃ R : Finset (Sym2 (Fin N)), R ⊆ F ∧ (∀ v : Fin N, (edeg R v : ℝ) ≤ ρ * (W.card : ℝ)) ∧
          ∀ L : Finset (Sym2 (Fin N)), L ⊆ F \ R →
            (∀ v : Fin N, (edeg L v : ℝ) ≤ η * (W.card : ℝ)) →
            TriDivisible (R ∪ L) → TriDecomp (R ∪ L) := by
  classical
  obtain ⟨η, n₁, hη, habs⟩ := hAbs c γ ρ K hc hγ hρ hK
  obtain ⟨N, W, W', W'', F, hcard, hW', hW'', hKW, hKKW, hKW'', hFW, hdivF, hdivF', hdivF'',
    hdense, hhollow, hne⟩ :=
    hollow_instance_realizable (c := c) hc1 hK hKc (max n₀ n₁)
  obtain ⟨R, hRsub, hRdeg, habs2⟩ :=
    habs W W' W'' F (le_trans (le_max_right n₀ n₁) hcard) hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF'
      hdivF'' hdense
  have hshell : F \ cliqueEdges W' = F := by
    ext e
    simp only [Finset.mem_sdiff, and_iff_left_iff_imp]
    intro he hmem
    have : e ∈ F ∩ cliqueEdges W' := Finset.mem_inter.2 ⟨he, hmem⟩
    rw [hhollow] at this
    exact absurd this (Finset.notMem_empty e)
  refine ⟨η, hη, N, W, W', F, le_trans (le_max_left n₀ n₁) hcard, hW', hFW, hne, hhollow,
    R, by rw [hshell] at hRsub; exact hRsub, hRdeg, ?_⟩
  intro L hL hLdeg hdiv
  obtain ⟨Q, hQ, hQcov, hQconf, -⟩ := habs2 L (by rw [hshell]; exact hL) hLdeg hdiv
  exact (triDecomp_of_confined_cover_of_hollow hhollow hQ hQcov hQconf).2

/-- **The far part must absorb itself, in every instance.**  Whatever reservation `R` a proof of
`BKLO.ShellAbsorption` produces, and whatever admissible leftover `L` it is handed, every edge of
`R ∪ L` with both endpoints outside `W'` lies in a triangle of `R ∪ L`.

This is `BKLO.far_edge_cherry_of_confined_cover` read at the interface.  It is the exact sense in
which gadget internals placed inside `W' \ W''` — the only place the confinement clause allows them
— are of no use for the far part of the shell: the covering triangle of a far edge has *all three*
of its edges in the remainder, so that part of the remainder has to be decomposable on its own. -/
theorem shellAbsorption_forces_far_cherries (hAbs : ShellAbsorption) (c γ ρ : ℝ) (K : ℕ)
    (hc : 9 / 10 < c) (hγ : 0 < γ) (hρ : 0 < ρ) (hK : 2 ≤ K) :
    ∃ (η : ℝ) (n₀ : ℕ), 0 < η ∧
      ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
        n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
        K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
        F ⊆ cliqueEdges W → TriDivisible F →
        TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
        (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
        ∃ R : Finset (Sym2 V), R ⊆ F \ cliqueEdges W' ∧
          (∀ v : V, (edeg R v : ℝ) ≤ ρ * (W.card : ℝ)) ∧
          ∀ L : Finset (Sym2 V), L ⊆ (F \ cliqueEdges W') \ R →
            (∀ v : V, (edeg L v : ℝ) ≤ η * (W.card : ℝ)) →
            TriDivisible (R ∪ L) →
            ∀ u v : V, u ∉ W' → v ∉ W' → s(u, v) ∈ R ∪ L →
              ∃ w : V, u ≠ w ∧ v ≠ w ∧ s(u, w) ∈ R ∪ L ∧ s(v, w) ∈ R ∪ L := by
  obtain ⟨η, n₀, hη, habs⟩ := hAbs c γ ρ K hc hγ hρ hK
  refine ⟨η, n₀, hη, ?_⟩
  intro V inst W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense
  obtain ⟨R, hRsub, hRdeg, habs2⟩ :=
    habs W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense
  refine ⟨R, hRsub, hRdeg, ?_⟩
  intro L hL hLdeg hdiv u v hu hv he
  obtain ⟨Q, hQ, hQcov, hQconf, -⟩ := habs2 L hL hLdeg hdiv
  exact far_edge_cherry_of_confined_cover hQ hQcov hQconf hu hv he

end BKLO
