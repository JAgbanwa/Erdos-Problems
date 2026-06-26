This [document](https://github.com/JAgbanwa/Erdos-Problems/blob/main/%23130/an_erdos_problem_130-2.pdf) was an earlier partial result by Claude Sonnet 4.6 (High) with this as a 
[formalization](https://github.com/JAgbanwa/Erdos-Problems/blob/main/%23130/Lean%20formalization).

GPT 5.5 Pro claims [this](https://github.com/JAgbanwa/Erdos-Problems/blob/main/%23130/_130_proper.pdf) ([.tex version](https://github.com/JAgbanwa/Erdos-Problems/blob/main/%23130/(Potential)%20full%20solution.tex)) as a solution to Erdös problem #130 which is [formalised](https://github.com/JAgbanwa/Erdos-Problems/tree/main/%23130/RequestProject) in Lean thanks to Aristotle. 

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

I formalized the paper *Integer-distance graphs in planar general position: rigorous bounds and the finite-block reduction* in Lean 4 / Mathlib. The whole project builds successfully.

Structure (all files under `RequestProject/`):

- `Defs.lean` — the Euclidean plane `Plane = EuclideanSpace ℝ (Fin 2)`, the integer-distance predicate `IsIntDist`, the general-position assumptions `NoThreeCollinear` / `NoFourConcyclic`, and the integer-distance graph `IntDistGraph A` (= Γ(A)).
- `Countable.lean` — **Theorem 1.2**: Lemma 2.1 (countable degree, `neighborSet_countable`), Lemma 2.2 (every connected component is countable, `component_countable`), and ℵ₀-colourability `colorable_aleph0` (a proper colouring into ℕ, i.e. χ(Γ(A)) ≤ ℵ₀).
- `NoInfiniteClique.lean` — **Theorem 1.3**: the geometric core Lemma 3.1 (`two_dist_diff_finite`, the Erdős–Anning finiteness lemma) and `no_infinite_clique` / `isClique_finite` (Γ(A) has no infinite clique; every clique is finite).
- `Example.lean` — **Example 5.1**: the explicit five points with s = √195, with all ten pairwise distances proved to be integers and full general position verified (no three collinear, no four concyclic), giving `exists_general_position_int_K5` (a finite general-position set whose integer-distance graph contains a K₅). Includes reusable 2D criteria `not_collinear_2d` and `not_cospherical_2d`.
- `FiniteBlock.lean` — **Theorem 1.4** (the finite-block criterion `finite_block_criterion`, stated faithfully as an iff). The forward direction `finite_block_forward` is fully proved using the De Bruijn–Erdős compactness theorem from Mathlib (`exists_finite_subset_not_colorable`).
- `Main.lean` — a top-level summary hub re-exporting Theorems 1.2, 1.3, 1.4 and Example 5.1.

Soundness: every fully-proved theorem depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound` (verified via `#print axioms`); no `sorry`/`sorryAx` and no added axioms or `@[implemented_by]`.

Two `sorry`s remain, both confined to the deep analytic part of Section 4: Lemma 4.2 (`generic_separation`, the Baire-category generic placement of a finite block) and the converse direction `finite_block_converse` that it powers. These are stated faithfully and documented; they correspond exactly to the additional finite-realisation/Baire-category input that the paper deliberately separates from the unconditional results. Consequently the full equivalence `finite_block_criterion` depends on `sorryAx` (only through the converse), while everything else is complete and axiom-clean.
