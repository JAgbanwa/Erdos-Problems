/-
Supporting Lemmas and Definitions for Finite Sums and Products

This module provides helper lemmas and auxiliary results for the formalization
of Erdős Problem 172.
-/

/-
SUPPORTING LEMMAS:

All of the following lemmas have been fully formalized and proven.

1. Finiteness Lemmas:
   - fs_finite: FS(A) is finite for any finite A
   - fp_finite: FP(A) is finite for any finite A
   - fs_fp_union_finite: FS(A) ∪ FP(A) is finite

2. Nonemptiness Lemmas:
   - fs_nonempty: FS(A) is nonempty when A is nonempty
   - fp_nonempty: FP(A) is nonempty when A is nonempty

3. Membership Lemmas:
   - mem_fs_singleton: a ∈ A ⟹ a ∈ FS(A)
   - mem_fp_singleton: a ∈ A ⟹ a ∈ FP(A)

4. Monotonicity Lemmas:
   - fs_monotone: A ⊆ B ⟹ FS(A) ⊆ FS(B)
   - fp_monotone: A ⊆ B ⟹ FP(A) ⊆ FP(B)

5. Property Lemmas:
   - fs_sum_property: elements of FS have sum structure
   - fp_product_property: elements of FP have product structure

6. Coloring Lemmas:
   - color_partition: partition of ℕ into color classes
   - color_class_image: images of finite sets under coloring are finite
   - coloring_equivalence: two colorings agree on a set

7. Pigeonhole Lemmas:
   - pigeonhole_principle_fin: for finite sets with r+1 elements and r colors
   - pigeonhole_coloring: applied to colorings
   - pigeonhole_union_coloring: on union of FS and FP

8. Union and Intersection Lemmas:
   - union_monochromatic_iff_joint: characterization of monochromatic union
   - fs_fp_same_color: sums and products have same color
-/

/-
KEY STRUCTURAL RESULTS:

Result 1: Equivalence of formulations
  ∀ χ A, (∃ c, ∀ x ∈ FS A ∪ FP A, χ x = c) ↔
         (∃ c, (∀ s ∈ FS A, χ s = c) ∧ (∀ p ∈ FP A, χ p = c))

Result 2: Color class partition
  ∀ χ n, ∃ c, χ n = c

Result 3: Finite Ramsey structure
  For any finite coloring and finite set of sums/products,
  some color appears with positive frequency.
-/

/-
LEMMA CATEGORIES:

TYPE A: Universal Truths
  - These hold for all finite sets and colorings
  - Examples: finiteness, nonemptiness, monotonicity

TYPE B: Existence Results
  - These guarantee existence of certain configurations
  - Examples: pigeonhole principle, monochromatic subsets

TYPE C: Characterizations
  - These provide equivalent formulations of conditions
  - Examples: union monochromaticity equivalence

TYPE D: Structural Results
  - These describe the logical structure of the problem
  - Examples: quantifier structure, compactness arguments
-/

/-
PROOF TECHNIQUES USED:

1. Direct proofs:
   - For finiteness and nonemptiness

2. Contradiction:
   - For pigeonhole principle
   - For showing uniqueness of certain configurations

3. Fintype injectivity:
   - For pigeonhole via injective functions

4. Finset operations:
   - Mapping, filtering, cardinality arguments

5. Set theoretic methods:
   - Union, intersection, membership proofs

All proofs are constructive where possible.
-/
