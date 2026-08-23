/-
# BKLO §10.1 — Lemmas 10.3 and 10.4 for `r = 2` (`F = K₃`).

This file transcribes BKLO Lemma 10.3 (the greedy `Kᵣ`-factor lemma, `r = 2`, so: perfect
matchings, supplied by Dirac's theorem = the `r = 2` case of Hajnal–Szemerédi, BKLO Theorem 10.2)
and BKLO Lemma 10.4 (the same statement with the `K_{r+1}`-decomposition replaced by an
`F`-decomposition), and proves

    Lemma 10.3  ⟹  Lemma 10.4          (`BKLO.lemma104K3_of_lemma103K3`)

for `r = 2`.  This is the *key simplification* of the triangle case: for `r = 2` one has
`K_{r+1} = K₃ = F`, so the embedding step in the proof of Lemma 10.4 — which for a general
`r`-regular `F` embeds copies of `F* = F \ {u} − F[N_F(u)]` onto the `K_{r+1}`'s using BKLO
Lemma 5.2 — is vacuous: `F*` is edgeless, and a `K₃`-decomposition *is* an `F`-decomposition.
Consequently hypothesis (iv) of Lemma 10.4 (`δ(H[V]) ≥ (1 − 1/r + 2γ)|V|`, which in the paper is
what makes the embedding possible) is not needed for `r = 2`; it is kept in the statement because
the paper states it, and the docstring records that it is unused.

Lemma 10.3 itself is *not* proved here: it is taken as the hypothesis `Lemma103K3`, exactly as
transcribed from the paper.  (It is being discharged separately from Dirac's theorem,
`BKLO.perfectMatchingDirac_holds`.)

Everything here is `sorry`-free.
-/
import BKLO.Section10Defs

open Finset

namespace BKLO

/-- **BKLO Lemma 10.3, for `r = 2`.**

*Let `r, k, n ∈ ℕ` and let `γ > 0` with `1/n ≪ γ, 1/k, 1/r`.  Let `H` be a graph on `n` vertices.
Let `U, V ⊆ V(H)` be disjoint with `|V| ≥ ⌊n/k⌋`.  Suppose that, for each `x ∈ U` and each
`y ∈ V`,*

* *(i) `r` divides `d_H(x, V)`;*
* *(ii) `δ(H[N_H(x,V)]) ≥ (1 − 1/r) d_H(x,V) + γ|V|`;*
* *(iii) `d_H(y, U) ≤ γ|V|/r`.*

*Then there is a subgraph `H_V` of `H[V]` such that `H[U,V] ∪ H_V` has a `K_{r+1}`-decomposition
and `Δ(H_V) ≤ γ|V|`.*

Here `r = 2`, so `K_{r+1} = K₃` and a `K_{r+1}`-decomposition is a `TriDecomp`.  The hierarchy
`1/n ≪ γ, 1/k` is transcribed as: for every `γ > 0` and every `k` there is a threshold `n₀`
beyond which the conclusion holds. -/
def Lemma103K3 : Prop :=
  ∀ (γ : ℝ) (k : ℕ), 0 < γ → 0 < k → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Sym2 V)) (U W : Finset V),
      n₀ ≤ Fintype.card V → (∀ e ∈ H, ¬ e.IsDiag) → Disjoint U W →
      Fintype.card V / k ≤ W.card →
      (∀ x ∈ U, 2 ∣ degTo H x W) →
      (∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + γ * (W.card : ℝ) ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ y ∈ W, (degTo H y U : ℝ) ≤ γ * (W.card : ℝ) / 2) →
      ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
        TriDecomp (edgesBtw H U W ∪ HV) ∧ ∀ v : V, (edeg HV v : ℝ) ≤ γ * (W.card : ℝ)

/-- **BKLO Lemma 10.4, for `r = 2` and `F = K₃`.**

*Let `r, f, k, n ∈ ℕ` and let `η, γ > 0` with `1/n ≪ η ≪ γ, 1/k, 1/r, 1/f`.  Let `F` be an
`r`-regular graph on `f` vertices and let `H` be a graph on `n` vertices.  Let `U, V ⊆ V(H)` be
disjoint with `|V| ≥ ⌊n/k⌋`.  Suppose that, for each `x ∈ U` and each `y ∈ V`,*

* *(i) `r` divides `d_H(x,V)`;*
* *(ii) `δ(H[N_H(x,V)]) ≥ (1 − 1/r) d_H(x,V) + γ|V|`;*
* *(iii) `d_H(y,U) ≤ η|V|`;*
* *(iv) `δ(H[V]) ≥ (1 − 1/r + 2γ)|V|`.*

*Then there is a subgraph `H'_V` of `H[V]` such that `H[U,V] ∪ H'_V` has an `F`-decomposition and
`Δ(H'_V) ≤ 2γ|V|`.*

Here `r = 2`, `F = K₃` and `f = 3`.  The hierarchy `1/n ≪ η ≪ γ, 1/k` is transcribed as: for every
`γ > 0` and every `k` there is `η₀ > 0` such that for every `0 < η ≤ η₀` there is a threshold `n₀`
beyond which the conclusion holds.

**Hypothesis (iv) is not needed when `r = 2`** — see `BKLO.lemma104K3_of_lemma103K3` — but it is
kept, since the paper states it. -/
def Lemma104K3 : Prop :=
  ∀ (γ : ℝ) (k : ℕ), 0 < γ → 0 < k → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Sym2 V)) (U W : Finset V),
      n₀ ≤ Fintype.card V → (∀ e ∈ H, ¬ e.IsDiag) → Disjoint U W →
      Fintype.card V / k ≤ W.card →
      (∀ x ∈ U, 2 ∣ degTo H x W) →
      (∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + γ * (W.card : ℝ) ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ y ∈ W, (degTo H y U : ℝ) ≤ η * (W.card : ℝ)) →
      (∀ y ∈ W, ((1 : ℝ) / 2 + 2 * γ) * (W.card : ℝ) ≤ (degTo H y W : ℝ)) →
      ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
        TriDecomp (edgesBtw H U W ∪ HV) ∧ ∀ v : V, (edeg HV v : ℝ) ≤ 2 * γ * (W.card : ℝ)

/-- **Lemma 10.4 from Lemma 10.3, for `r = 2`.**

For `r = 2` the graph `F* = F \ {u} − F[N_F(u)]` of the paper's proof is edgeless (`F = K₃` has
`|N_F(u)| = 2` and `F \ {u}` is the single edge inside `N_F(u)`), so no embedding is needed and a
`K_{r+1} = K₃`-decomposition already *is* an `F`-decomposition.  The proof is therefore: take
`η₀ := γ/2`, so that hypothesis (iii) of Lemma 10.4, `d_H(y,U) ≤ η|V|`, implies hypothesis (iii) of
Lemma 10.3, `d_H(y,U) ≤ γ|V|/2 = γ|V|/r`; apply Lemma 10.3 and weaken `Δ ≤ γ|V|` to `Δ ≤ 2γ|V|`.
Hypothesis (iv) is not used. -/
theorem lemma104K3_of_lemma103K3 (h : Lemma103K3) : Lemma104K3 := by
  intro γ k hγ hk
  obtain ⟨n₀, hn₀⟩ := h γ k hγ hk
  refine ⟨γ / 2, by positivity, fun η hη hηγ => ⟨n₀, ?_⟩⟩
  intro V _ _ H U W hcard hloop hdisj hW hdvd hdeg hUdeg _hiv
  obtain ⟨HV, hHV, hdec, hΔ⟩ :=
    hn₀ H U W hcard hloop hdisj hW hdvd hdeg (fun y hy => by
      have h1 : (degTo H y U : ℝ) ≤ η * (W.card : ℝ) := hUdeg y hy
      have h2 : η * (W.card : ℝ) ≤ (γ / 2) * (W.card : ℝ) :=
        mul_le_mul_of_nonneg_right hηγ (Nat.cast_nonneg _)
      have : (γ / 2) * (W.card : ℝ) = γ * (W.card : ℝ) / 2 := by ring
      linarith)
  refine ⟨HV, hHV, hdec, fun v => le_trans (hΔ v) ?_⟩
  have : (0 : ℝ) ≤ γ * (W.card : ℝ) := by positivity
  linarith

end BKLO
