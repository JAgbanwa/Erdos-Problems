/-
# Paper III — Addenda (v0.9.1 corollaries)

These are the *optional, post-core* additions of `LEDGER_INCREMENTAL_v0.9.1.md`.  They only
**consume** already-formalized core results (E-3.1, Theorem 1.1 / Corollary 1.2,
Proposition 10.1) and add **no** new axioms; nothing in the frozen core (§2–§9, App. A–D)
depends on them.  Dependency graph is one-directional, exactly as the incremental ledger
certifies.

* **A1 — Corollary 10.4** (§10.4): the exact closed fractional value `ν₃*(H(p,q,d)) = F`.
  This is Theorem 3.1 / node E-3.1 re-packaged as a stand-alone named result.
* **A3 — Corollary 10.4b** (§10.4): threshold ⊆ split, so the linear-error bound holds for
  threshold graphs; the complete-split family `K_p ∨ K̄_{2p}` is the concrete witness.
* **A2 — Corollary 12.2** (§12.3), formalizable part: the *bound* `cp(G) ≤ n²/6 + 2n` in the
  effective low corridor (the poly-time *algorithm* claim is prose, not formalized).
-/
import PaperIII.E_4_agg
import PaperIII.Main
import PaperIII.Prop_10_1

namespace PaperIII

open SplitGraph Finset

/-- **Corollary 10.4 (A1)** — exact common-neighborhood fractional triangle packing.
For `p ≥ 3`, `q ≥ 1`, `d ≤ p`, the common-profile graph `H(p,q,d)` has
`ν₃*(H(p,q,d)) = F(p,q,d)` (a closed form for the whole one-parameter family).
This is exactly node E-3.1, restated as a stand-alone result. -/
theorem Corollary_10_4 (p q d : ℕ) (hp : 3 ≤ p) (hq : 1 ≤ q) (hd : d ≤ p) :
    tau3Star (commonProfile p q d).graph = ((F p q d : ℚ) : ℝ) :=
  E_3_1 p q d hp hq hd

/-- The complete-split graph `K_p ∨ K̄_{2p}` (the extremal family): a clique of order `p`
and `2p` independent vertices each adjacent to all of `K`.  It is a threshold graph. -/
def completeSplit (p : ℕ) : SplitGraph := ⟨p, 2 * p, fun _ => Finset.univ⟩

/-- **Corollary 10.4b (A3)** — threshold graphs.  Every threshold graph is split, so the
linear-error clique-partition bound of Theorem 1.1 applies to them with the same constant;
in particular to the extremal complete-split family.  Formalized as: the universal bound of
`Corollary_1_2` covers `completeSplit p` (a threshold graph) for every `p`. -/
theorem Corollary_10_4b :
    ∃ C : ℝ, ∀ p : ℕ,
      ((completeSplit p).cp : ℝ)
        ≤ ((completeSplit p).n : ℝ) ^ 2 / 6 + C * ((completeSplit p).n : ℝ) := by
  obtain ⟨C, hC⟩ := Corollary_1_2
  exact ⟨C, fun p => hC (completeSplit p)⟩

/-- **Corollary 12.2 (A2), formalizable part** — the effective-corridor *bound*.
For a split graph in the low corridor (`p ≥ 36`, `0 ≤ s`, `s² ≤ 36p`), the clique-partition
number satisfies `cp(G) ≤ n²/6 + 2n` with the explicit constant of Proposition 10.1.
(The polynomial-time *algorithm* of Corollary 12.2 is expository and not formalized here.) -/
theorem Corollary_12_2_bound (G : SplitGraph) (hp : 37 ≤ G.p)
    (hs0 : 0 ≤ G.s) (hs : (G.s : ℝ) ^ 2 ≤ 36 * (G.p : ℝ)) :
    (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (3 / 2) * (G.n : ℝ) := by
  have h1 : (G.cp : ℝ) ≤ ((G.Phi : ℤ) : ℝ) := by exact_mod_cast cp_le_Phi G
  exact le_trans h1 (Prop_10_1_low G hp hs0 hs)

end PaperIII
