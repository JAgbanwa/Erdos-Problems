/-
# BKLO §7, §9 and §10.2 — the vocabulary needed by Lemma 10.12, for `r = 2` (`F = K₃`).

This file transcribes, for `r = 2` and `F = K₃`, the statements that the proof of BKLO Lemma 10.12
(pp. 33–34) uses:

| paper                                     | here                    |
| ----------------------------------------- | ----------------------- |
| Lemma 7.2 (p. 13, random subgraph `R`)     | `BKLO.Lemma72K3`        |
| `F`-parity graph (§9, Prop. 9.2, p. 24–25) | `BKLO.IsParityGraphK3`  |
| Lemma 9.3 (p. 25)                          | `BKLO.Lemma93K3`        |
| Lemma 10.10 (p. 32)                        | `BKLO.Lemma1010K3`      |
| Corollary 10.11 (p. 32)                    | `BKLO.Cor1011K3`        |
| Lemma 10.6 (p. 28), on a vertex *set*      | `BKLO.Lemma106K3Set`    |

Of these, `Cor1011K3` is *proved* from `Lemma1010K3` in `BKLO/Section102K3.lean`.  `Lemma72K3`,
`Lemma93K3`, `Lemma1010K3` and `Lemma106K3Set` are carried as hypotheses; each docstring names the
paper page and the ingredient that is out of scope.

The paper indexes the parts of a partition `P = {V₁, …, V_k}` and uses `V_{<i} = V₁ ∪ … ∪ V_{i-1}`.
Here a partition is an (unordered) `Finset (Finset V)`, so the indexing is supplied by an auxiliary
`idx : Finset V → ℕ`, injective on `P`, and `V_{<i}` becomes `beforeParts P idx W`.

Everything here is `sorry`-free.
-/
import BKLO.Section10Iteration

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Codegrees -/

/-- `d_E({x,y}, W) = |N_E(x,W) ∩ N_E(y,W)|`, the codegree of the pair `x, y` inside `W`. -/
def codegTo (E : Finset (Sym2 V)) (x y : V) (W : Finset V) : ℕ :=
  (nbhdIn E x W ∩ nbhdIn E y W).card

theorem codegTo_mono_left {E E' : Finset (Sym2 V)} (h : E ⊆ E') (x y : V) (W : Finset V) :
    codegTo E x y W ≤ codegTo E' x y W :=
  Finset.card_le_card
    (Finset.inter_subset_inter (nbhdIn_mono_left h x W) (nbhdIn_mono_left h y W))

/-! ### The ordering of the parts -/

/-- `V_{<i}`: the union of the parts of `P` preceding `W` in the ordering given by `idx`. -/
def beforeParts (P : Finset (Finset V)) (idx : Finset V → ℕ) (W : Finset V) : Finset V :=
  (P.filter (fun W' => idx W' < idx W)).biUnion id

theorem mem_beforeParts {P : Finset (Finset V)} {idx : Finset V → ℕ} {W : Finset V} {x : V} :
    x ∈ beforeParts P idx W ↔ ∃ W' ∈ P, idx W' < idx W ∧ x ∈ W' := by
  simp only [beforeParts, Finset.mem_biUnion, Finset.mem_filter, id]
  tauto

/-! ### §7: Lemma 7.2 -/

/-- **BKLO Lemma 7.2, p. 13** (specialised to `s = 2`, i.e. to degrees and codegrees), transcribed
as a hypothesis.

*Let `k, s ∈ ℕ` and let `0 < γ, ρ < 1`.  There is `n₀ = n₀(k, s, γ)` such that the following holds.
Let `G` be a graph on `n ≥ n₀` vertices and let `V₁, …, V_k` be an equitable partition of its
vertex set.  Let `H` be a graph on `V(G)`.  Then there is a subgraph `R` of `G` such that, for each
`1 ≤ i ≤ k` and each `S ⊆ V(G)` with `|S| ≤ s`, `d_R(S, Vᵢ) = ρ^{|S|} d_G(S, Vᵢ) ± γ|Vᵢ|`, and for
each `x, y ∈ V(G)`, `d_H(y, N_R(x, Vᵢ)) = ρ d_H(y, N_G(x, Vᵢ)) ± γn`.*

The paper's proof is probabilistic: `R` is a `ρ`-random subgraph of `G` and the estimates hold with
high probability by Hoeffding's inequality (Lemma 7.1, p. 13) and a union bound over the
`k(n+1)^s + kn²` events.  That concentration argument is the ingredient which is out of scope here.

Only the three directions of the `±`-estimates that the proof of Lemma 10.12 actually uses are
required, which makes this hypothesis *weaker* than the paper's Lemma 7.2:
the upper bound in (10.5), the upper bound in (10.6), and the lower bound in (10.7).

**Warning.**  This transcription is *false*: see `BKLO.not_lemma72K3` in `BKLO/Section72K3.lean`.
It drops two hypotheses of the paper — that the codegree estimate is about a *set* `{x, y}` of two
*distinct* vertices, and that `G` and `H` are graphs on the `n` vertices of `V(G)`.  The corrected
statement `BKLO.Lemma72K3'` below restores both and is proved in `BKLO/Section72K3.lean`; it is
what the assembly of Lemma 10.12 now uses. -/
def Lemma72K3 : Prop :=
  ∀ (k : ℕ) (γ ρ : ℝ), 0 < k → 0 < γ → 0 < ρ → ρ < 1 → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (G Hg : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V)),
      n₀ ≤ S.card → IsEquitablePartition k P S →
      ∃ R : Finset (Sym2 V), R ⊆ G ∧
        (∀ (x : V) (W : Finset V), W ∈ P →
          (degTo R x W : ℝ) ≤ ρ * (degTo G x W : ℝ) + γ * (W.card : ℝ)) ∧
        (∀ (x y : V) (W : Finset V), W ∈ P →
          (codegTo R x y W : ℝ) ≤ ρ ^ 2 * (codegTo G x y W : ℝ) + γ * (W.card : ℝ)) ∧
        (∀ (x y : V) (W : Finset V), W ∈ P →
          ρ * (degTo Hg y (nbhdIn G x W) : ℝ) - γ * (S.card : ℝ)
            ≤ (degTo Hg y (nbhdIn R x W) : ℝ))

/-- **BKLO Lemma 7.2, p. 13, corrected** (specialised to `s = 2`, i.e. to degrees and codegrees).

`BKLO.Lemma72K3` above transcribes the three `±`-estimates the proof of Lemma 10.12 uses, but it
is *false as stated*: see `BKLO.not_lemma72K3` in `BKLO/Section72K3.lean`.  Two hypotheses of the
paper were lost in that transcription, and both are restored here.

* The paper's estimate `d_R(S, Vᵢ) = ρ^{|S|} d_G(S, Vᵢ) ± γ|Vᵢ|` is about a *set* `S` of at most
  `s = 2` vertices, so the codegree estimate, with its factor `ρ²`, only concerns `x ≠ y`; for
  `x = y` the relevant estimate is the degree one, with its factor `ρ`.  Taking `x = y` in the
  codegree clause of `Lemma72K3` demands `d_R(x, Vᵢ) ≤ ρ² d_G(x, Vᵢ) + γ|Vᵢ|`, which together with
  the third clause is contradictory; this is exactly what `BKLO.not_lemma72K3` exploits.  Here the
  codegree clause is restricted to `x ≠ y`, as in the paper.
* In the paper `G` and `H` are graphs on the `n` vertices of `V(G) = V₁ ∪ … ∪ V_k`, and the
  probabilistic proof takes a union bound over `O(kn²)` events, one for each pair of vertices of
  `V(G)` and each part.  Here that is the hypothesis `G ⊆ cliqueEdges S`, `Hg ⊆ cliqueEdges S`.
  Without it a vertex `y ∉ S` may have an arbitrary neighbourhood in a part `W`, and the third
  clause applied to the `2^{|W|}` possible neighbourhoods forces `N_R(x, W)` to meet every subset
  of `N_G(x, W)` in a `ρ`-proportion, which contradicts the first clause.

Both restored hypotheses hold at the point where the proof of Lemma 10.12 applies Lemma 7.2.  This
statement is *proved* in `BKLO/Section72K3.lean` (`BKLO.lemma72K3'_holds`). -/
def Lemma72K3' : Prop :=
  ∀ (k : ℕ) (γ ρ : ℝ), 0 < k → 0 < γ → 0 < ρ → ρ < 1 → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (G Hg : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V)),
      n₀ ≤ S.card → G ⊆ cliqueEdges S → Hg ⊆ cliqueEdges S → IsEquitablePartition k P S →
      ∃ R : Finset (Sym2 V), R ⊆ G ∧
        (∀ (x : V) (W : Finset V), W ∈ P →
          (degTo R x W : ℝ) ≤ ρ * (degTo G x W : ℝ) + γ * (W.card : ℝ)) ∧
        (∀ (x y : V) (W : Finset V), x ≠ y → W ∈ P →
          (codegTo R x y W : ℝ) ≤ ρ ^ 2 * (codegTo G x y W : ℝ) + γ * (W.card : ℝ)) ∧
        (∀ (x y : V) (W : Finset V), W ∈ P →
          ρ * (degTo Hg y (nbhdIn G x W) : ℝ) - γ * (S.card : ℝ)
            ≤ (degTo Hg y (nbhdIn R x W) : ℝ))

/-! ### §9: parity graphs -/

/-- **`F`-parity graph with respect to `P`** (BKLO §9, Proposition 9.2, pp. 24–25), for `r = 2`
and `F = K₃`, in the form in which the proof of Lemma 10.12 uses it (p. 33):

`Ppar` has an `F`-decomposition, and for every `r`-divisible graph `G*` edge-disjoint from `Ppar`
there is a subgraph `P'` of `Ppar` such that

* (P1) `r` divides `d_{G* ∪ P'}(x, Vᵢ)` for each `i` and each `x ∈ V_{<i}`;
* (P2) `Ppar − P'` has an `F`-decomposition.

For `r = 2`, "`r` divides" is `Even` and an `F`-decomposition is a `TriDecomp`. -/
def IsParityGraphK3 (P : Finset (Finset V)) (idx : Finset V → ℕ) (Ppar : Finset (Sym2 V)) :
    Prop :=
  TriDecomp Ppar ∧
    ∀ Gstar : Finset (Sym2 V), Disjoint Gstar Ppar → EvenDegrees Gstar →
      ∃ P' : Finset (Sym2 V), P' ⊆ Ppar ∧ TriDecomp (Ppar \ P') ∧
        ∀ W ∈ P, ∀ x ∈ beforeParts P idx W, Even (degTo (Gstar ∪ P') x W)

/-- **BKLO Lemma 9.3, p. 25**, for `r = 2` and `F = K₃`, transcribed as a hypothesis.

*Let `r, f ∈ ℕ`, let `F` be an `r`-regular graph on `f` vertices and let `γ > 0`.  Then there is
`n₀ = n₀(k, γ, F)` such that: if `G` is a graph on `n ≥ n₀` vertices and `P = {V₁, …, V_k}` is a
`(k, δ)`-partition for `G` with `δ ≥ 1 − 1/r + γ`, then `G` contains an `F`-parity graph `P` with
respect to `P` with `Δ(P) ≤ γn`.*

The paper's proof embeds the abstract parity graph of Proposition 9.2 into `G` using **Lemma 5.2**
(the rooted embedding lemma, p. 10), which is not available in this development; Lemma 9.3 is
therefore carried as a hypothesis.  For `r = 2`: `1 − 1/r = 1/2`. -/
def Lemma93K3 : Prop :=
  ∀ (k : ℕ) (γ : ℝ), 0 < k → 0 < γ → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (G : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V))
      (idx : Finset V → ℕ) (d : ℝ),
      n₀ ≤ S.card → (∀ e ∈ G, ¬ e.IsDiag) → G ⊆ cliqueEdges S →
      1 / 2 + γ ≤ d → IsKDeltaPartition k d P G S →
      ∃ Ppar : Finset (Sym2 V), Ppar ⊆ G ∧ IsParityGraphK3 P idx Ppar ∧
        ∀ v : V, (edeg Ppar v : ℝ) ≤ γ * (S.card : ℝ)

/-! ### §10.2: Lemma 10.10 and Corollary 10.11 -/

/-- **BKLO Lemma 10.10, p. 32**, for `r = 2` and `F = K₃`, transcribed as a hypothesis.

*Let `r, k, n, f ∈ ℕ` and let `α, ρ > 0` with `1/n ≪ ρ ≪ α, 1/k, 1/r, 1/f ≤ 1`.  Let `F` be an
`r`-regular graph on `f` vertices and let `H` be a graph on `n` vertices.  Let `U, V ⊆ V(H)` be
disjoint with `|V| ≥ ⌊n/k⌋`.  Suppose that, for all distinct `x, x' ∈ U` and each `y ∈ V`,*

* *(i) `r` divides `d_H(x, V)`;*
* *(ii) `δ(H[N_H(x,V)]) ≥ (1 − 1/r) d_H(x,V) + 9rkρ^{3/2}|V|`;*
* *(iii) `|N_H(x,V) ∩ N_H(x',V)| ≤ 2ρ²|V|`;*
* *(iv) `d_H(y, U) ≤ 2kρ|V|`;*
* *(v) `δ(H[V]) ≥ (1 − 1/r + 2α)|V|`.*

*Then there is a subgraph `H'_V` of `H[V]` such that `H[U,V] ∪ H'_V` has an `F`-decomposition and
`Δ(H'_V) ≤ 2α|V|`.*

For `r = 2`: `1 − 1/r = 1/2`, `9rk = 18k`, and an `F`-decomposition is a `TriDecomp`.  The paper
deduces Lemma 10.10 from Corollary 10.9 "in the same way that Lemma 10.4 follows from Lemma 10.3",
i.e. through **Lemma 5.2**, the rooted embedding lemma (p. 10); Corollary 10.9 in turn rests on
Lemma 10.7 (p. 31).  Both are out of scope here, so Lemma 10.10 is carried as a hypothesis.

**Warning.**  This transcription is *false*: see `BKLO.Cex.not_lemma1010K3` in
`BKLO/Section1010Refutation.lean`.  It drops the paper's hierarchy `1/n ≪ ρ ≪ α, 1/k`, quantifying
instead over all `α, ρ ∈ (0,1)`, and in the regime `α ≪ kρ` hypotheses (i)–(v) are compatible with
a vertex `y ∈ V` of apex degree `d_H(y,U) ≫ 2α|V|`, which `BKLO.degTo_le_edeg_of_triDecomp` shows
is a lower bound for `Δ(H'_V)`.  The statement `BKLO.Lemma1010K3Hier` in
`BKLO/Section1010Sparse.lean` restores exactly the needed consequence `2kρ ≤ α` of the hierarchy;
it is proved there from the single residual clause `BKLO.Lemma107K2`, the pseudorandom
`K_r`-factor core (Lemma 10.7 / Corollary 10.9 for `r = 2`), and
`BKLO.Cex.hyps_nonvacuous` shows that its hypotheses are satisfiable. -/
def Lemma1010K3 : Prop :=
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
      ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
        TriDecomp (edgesBtw H U W ∪ HV) ∧ ∀ v : V, (edeg HV v : ℝ) ≤ 2 * α * (W.card : ℝ)

/-- **BKLO Corollary 10.11, p. 32**, for `r = 2` and `F = K₃`.

*Let `P = {V₁, …, V_k}` be an equitable partition of `V(H)`.  Suppose that, for each `2 ≤ i ≤ k`,
all distinct `x, x' ∈ V_{<i}` and each `y ∈ Vᵢ`, conditions (i)–(v) of Lemma 10.10 hold.  Then
there is a subgraph `H₀` of `H − H[P]` such that `H[P] ∪ H₀` has an `F`-decomposition and
`Δ(H₀) ≤ 2αn`.*

This is *proved* from `Lemma1010K3` in `BKLO/Section102K3.lean`. -/
def Cor1011K3 : Prop :=
  ∀ (α ρ : ℝ) (k : ℕ), 0 < α → 0 < ρ → ρ < 1 → 0 < k → ∃ n₀ : ℕ,
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

/-! ### Lemma 10.6 on a vertex set -/

/-- **BKLO Lemma 10.6, p. 28**, for `r = 2`, stated for a graph living on a vertex *set*
`S : Finset V` rather than on the whole (finite) vertex type.

This is the form in which the proof of Lemma 10.12 uses Lemma 10.6.  Compared with
`BKLO.Lemma106K3` (which lives on a `Fintype`) it carries, besides the change of ambient vertex
set, the extra hypothesis `1/k ≤ ε`: part of the paper's hierarchy `1/k ≪ ε` for Lemma 10.6.  That
hypothesis is what the counterexample `BKLO.not_transformStepK3` (with `k = 2`) violates, and it
is available at the point where the proof of Lemma 10.12 below applies Lemma 10.6.  It is *weaker*
than the paper's `1/k ≪ ε`, and weaker than the `1/k ≤ ε/8` of `BKLO.Lemma106K3Res`. -/
def Lemma106K3Set (δ : ℝ) : Prop :=
  ∀ (γ ε : ℝ) (k : ℕ), 0 < γ → γ ≤ ε / 4 → 0 < ε → ε ≤ 1 / 3 → 0 < k → 1 / (k : ℝ) ≤ ε →
    ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V)),
      n₀ ≤ S.card → (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S →
      IsKDeltaPartition k (δ + ε) P E S →
      ∃ H : Finset (Sym2 V), H ⊆ E ∧
        TriDecomp (E \ H) ∧
        (∀ v : V, (edeg (crossParts H P) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        (∀ W ∈ P, ∀ v : V, (edeg (edgesIn E W \ edgesIn H W) v : ℝ) ≤ 2 * γ * (W.card : ℝ))

end BKLO
