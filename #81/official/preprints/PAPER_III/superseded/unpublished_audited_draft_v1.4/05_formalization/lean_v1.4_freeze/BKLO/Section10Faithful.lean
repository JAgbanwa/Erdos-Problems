/-
# BKLO §10 for `r = 2` (`F = K₃`) — the faithful transcription, assembled.

This file collects the faithful transcription of Barber–Kühn–Lo–Osthus, *Edge-decompositions of
graphs with high minimum degree*, §10 ("Near optimal decompositions"), specialised to `r = 2`,
`F = K₃`, `f = 3`.  The paper text is in `PAPER_SECTION_10.txt`.

## What is transcribed, and where

| paper                     | here                                                        |
| ------------------------- | ----------------------------------------------------------- |
| notation of §10           | `BKLO/Section10Defs.lean`                                    |
| Proposition 10.5          | `BKLO.prop_10_5`            (**proved**, general `r ≥ 1`)     |
| Lemma 10.3                | `BKLO.Lemma103K3`           (hypothesis)                      |
| Lemma 10.4                | `BKLO.Lemma104K3`, `BKLO.lemma104K3_of_lemma103K3` (**proved** from 10.3) |
| Lemma 10.6                | `BKLO.Lemma106K3`, `BKLO.lemma106K3_of_transformStep` (**proved** from the transformation step and 10.4) |
| Lemma 10.12               | `BKLO.Lemma1012K3`          (hypothesis)                      |
| Lemma 10.13 (= Lemma 10.1)| `BKLO.lemma_10_13_K3`       (**proved** from 10.12)           |

The key simplification for `r = 2` is that `K_{r+1} = K₃ = F`, so the embedding step of Lemma 10.4
is vacuous and a `K_{r+1}`-decomposition *is* an `F`-decomposition
(`BKLO.lemma104K3_of_lemma103K3`).

## The chain

`Lemma 10.3` ⟹ `Lemma 10.4` ⟹ (with `TransformStepK3`) `Lemma 10.6`;
`Lemma 10.12` ⟹ `Lemma 10.13` = `Lemma 10.1`.

Both halves are assembled below.  Everything in this development is `sorry`-free, and no `axiom`
is introduced: the paper ingredients that are *not* formalised appear as explicit `Prop`-valued
hypotheses, each transcribed verbatim from the paper text and named in its docstring.

## The inputs that are *not* discharged here, with their paper references

1. **`BKLO.Lemma103K3`** — BKLO Lemma 10.3, p. 27 (the greedy `Kᵣ`-factor lemma; for `r = 2` it is
   fed by Dirac's theorem, i.e. the `r = 2` case of Hajnal–Szemerédi = BKLO Theorem 10.2).  This is
   the hypothesis the task explicitly takes for granted; it is discharged separately.

2. **`BKLO.TransformStepK3`** — the first half of the proof of BKLO Lemma 10.6, pp. 28–29.  It
   packages exactly three paper ingredients that are unavailable in this development:
   * the existence of a subgraph `G'` of `G[P]` with (G1) `Δ(G') ≤ 2qn` and (G2)
     `d_{G'}(S, V(G)) ≥ q^r εn/2` for all `|S| ≤ r` — the probabilistic step of the proof;
   * the approximate-decomposition threshold `δ_F^η` (the definition of `δ_F^η` applied to
     `G[P] − G'`);
   * **BKLO Lemma 5.2, p. 10** — the rooted embedding lemma producing `m` *edge-disjoint*
     embeddings of `H₁, …, H_m` with `Δ(⋃ φ(Hᵢ)) ≤ ηn`.  The embedding lemma available in this
     project, `BKLO.exists_embedding`, embeds a *single* gadget while avoiding a given vertex set;
     it is strictly weaker than Lemma 5.2 and cannot be used here.

3. **`BKLO.Lemma1012K3`** — BKLO Lemma 10.12, p. 33.  Its proof (pp. 33–34) derives it from
   Lemma 10.6 together with **Lemma 7.2** (the sparse random subgraph `R` with the degree and
   codegree estimates (10.5)–(10.7)), **Lemma 9.3** (the existence of an `F`-parity graph) and
   **Corollary 10.11** (§10.2, the pseudorandom-remainder version of Lemma 10.3, itself a corollary
   of Lemma 10.10).  Sections 7, 9 and 10.2 are outside the scope of this task, so Lemma 10.12 is
   taken as a hypothesis; the missing link in the chain is therefore exactly
   `Lemma 10.6 ⟹ Lemma 10.12`, i.e. BKLO Corollary 10.11 plus Lemmas 7.2 and 9.3.

## On `BKLO.NearOptimalConclusion`

`BKLO.NearOptimalConclusion` (in `BKLO/NearOptimal.lean`) is *not* the conclusion of §10.  It asks
for a **single** bounded vertex set `U`, fixed before the bounded reserved edge set `A`, such that
the uncovered remainder lies inside `cliqueEdges U`.  The output of §10 (Lemma 10.1 = Lemma 10.13,
transcribed here as `BKLO.lemma_10_13_K3`) instead leaves a remainder spread over *all* parts of
the last partition `P_ℓ` — roughly `n/m` parts of size `≤ m` each, not one bounded set.  Passing
from the §10 output to a vortex-shaped statement such as `NearOptimalConclusion` is the business of
BKLO §11 (absorption), which is not part of §10 and is not formalised here.  Accordingly this file
does *not* claim `NearOptimalConclusion`; claiming it from §10 alone would be unfaithful.

## Update: the transformation step is false as transcribed, and its repair

`BKLO.TransformStepK3` as transcribed below quantifies over **all** `k > 0`, thereby dropping the
part `1/k ≪ ε` of the paper's hierarchy for Lemma 10.6.  That makes it false:
`BKLO.not_transformStepK3` (in `BKLO/Section10TransformStepRefutation.lean`) refutes it for every
`δ < 1`, using `k = 2`, where the crossing graph is bipartite and hence triangle-free.

The repaired statement `BKLO.TransformStepK3Res` (`1/k ≤ ε/8` restored) is **proved** in
`BKLO/Section10TransformStepProof.lean` from the single paper input
`BKLO.ApproxTriDecompMinDeg δ`, i.e. from `δ ≥ δ_F^η` — which is how BKLO defines `δ`.  Neither
the probabilistic subgraph `G'` nor Lemma 5.2 is needed for this conclusion: deleting the copies
of `F` that meet `B` costs each vertex outside `B` at most `2|B|` in degree, because the copies
are edge-disjoint.  The repaired chain ends in `BKLO.Lemma106K3Res` and
`BKLO.section10_K3_repaired` below.
-/
import BKLO.Section10DegreeReduction
import BKLO.Section10TransformStepProof

namespace BKLO

/-- **BKLO Lemma 10.6 for `r = 2`, from Lemma 10.3.**

Combines `lemma104K3_of_lemma103K3` (Lemma 10.3 ⟹ Lemma 10.4, using `K_{r+1} = K₃ = F`) with
`lemma106K3_of_transformStep` (the second half of the proof of Lemma 10.6).  The remaining
hypothesis `TransformStepK3` is the first half of that proof; see the file header for the three
paper ingredients it packages. -/
theorem lemma106K3_of_lemma103K3 {δ : ℝ} (hδ : (2 : ℝ) / 3 ≤ δ)
    (htr : TransformStepK3 δ) (h103 : Lemma103K3) : Lemma106K3 δ :=
  lemma106K3_of_transformStep hδ htr (lemma104K3_of_lemma103K3 h103)

/-- **The two halves of BKLO §10 for `r = 2`, assembled.**

Given
* Lemma 10.3 (`h103`, the hypothesis supplied by Dirac's theorem),
* the transformation step of the proof of Lemma 10.6 (`htr`), and
* Lemma 10.12 (`h12`),

one obtains Lemma 10.6 and Lemma 10.13 (which is the formal version of Lemma 10.1). -/
theorem section10_K3 {δ ε : ℝ} {k : ℕ} (hδ : (2 : ℝ) / 3 ≤ δ)
    (hk : 0 < k) (hε : 0 < ε) (hkε : 1 / (k : ℝ) ≤ ε / 8)
    (h103 : Lemma103K3) (htr : TransformStepK3 δ) (h12 : Lemma1012K3 δ) :
    Lemma106K3 δ ∧
      ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        ∀ {V : Type} [DecidableEq V] (L : List (Finset (Finset V))) (Pl : Finset (Finset V))
          (E : Finset (Sym2 V)) (S : Finset V),
          (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
          PartSeq k (δ + ε) δ ε m L Pl E S →
          ∃ Hstar : Finset (Sym2 V), Hstar ⊆ insideParts E (restrictParts Pl S) ∧
            TriDecomp (E \ Hstar) :=
  ⟨lemma106K3_of_lemma103K3 hδ htr h103, lemma_10_13_K3 hk hε hkε h12⟩

/-- **The two halves of BKLO §10 for `r = 2`, assembled — repaired version.**

Same as `BKLO.section10_K3`, except that the false hypothesis `TransformStepK3 δ` (see
`BKLO.not_transformStepK3`) has been *removed*: the transformation step is now proved, from the
approximate decomposition threshold `BKLO.ApproxTriDecompMinDeg δ` (the paper's `δ ≥ δ_F^η`).
The conclusion is the repaired Lemma 10.6, `BKLO.Lemma106K3Res`, which carries the paper's
hierarchy condition `1/k ≤ ε/8` — the same condition `hkε` that the second half of §10 already
requires. -/
theorem section10_K3_repaired {δ ε : ℝ} {k : ℕ} (hδ : (2 : ℝ) / 3 ≤ δ) (hδ1 : δ ≤ 1)
    (hk : 0 < k) (hε : 0 < ε) (hkε : 1 / (k : ℝ) ≤ ε / 8)
    (h103 : Lemma103K3) (happ : ApproxTriDecompMinDeg δ) (h12 : Lemma1012K3 δ) :
    Lemma106K3Res δ ∧
      ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        ∀ {V : Type} [DecidableEq V] (L : List (Finset (Finset V))) (Pl : Finset (Finset V))
          (E : Finset (Sym2 V)) (S : Finset V),
          (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S → EvenDegrees E →
          PartSeq k (δ + ε) δ ε m L Pl E S →
          ∃ Hstar : Finset (Sym2 V), Hstar ⊆ insideParts E (restrictParts Pl S) ∧
            TriDecomp (E \ Hstar) :=
  ⟨lemma106K3Res_of_inputs hδ hδ1 happ h103, lemma_10_13_K3 hk hε hkε h12⟩

end BKLO
