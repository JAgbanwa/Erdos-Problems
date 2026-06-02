# Finite Sums and Products - Lean Formalization

This directory contains the formal Lean proof of the finite sums and products theorem from the paper "Finite Sums and Products" based on Bergelson-Hindman results.

## Overview

**Main Theorem**: Every finite coloring of ℕ contains arbitrarily large finite sets whose distinct finite sums and distinct finite products all have one common color.

This is a finite Ramsey-theoretic result that, while weaker than the infinite conjecture (which remains open), provides an important finite configuration in combinatorics.

## File Structure

### 1. `FiniteSumsProducts.lean`
The core formalization containing:
- Definition of **FS(A)**: set of all nonempty finite sums of distinct elements from A
- Definition of **FP(A)**: set of all nonempty finite products of distinct elements from A
- Definition of **Coloring**: functions from ℕ to color classes
- **Main Theorem**: For every r-coloring and m ≥ 1, there exist m distinct naturals with monochromatic sums and products
- **Finite Sums-Products Theorem** (Bergelson-Hindman): The key tool
- **Finite Bound Version**: Equivalent formulation with explicit N(r,m)

### 2. `SumsProductsLemmas.lean`
Supporting definitions and lemmas:
- **UnionMonochromatic**: All elements of FS(A) ∪ FP(A) have one color
- **ColorClass**: The set of all naturals of a specific color
- **JointMonochromatic**: Both FS and FP are in the same color class
- Helper lemmas about monotonicity, injectivity, and basic properties
- Pigeonhole principle and Ramsey theory applications

### 3. `ProofStrategy.lean`
High-level proof strategy and sketch:
- Overview of the proof structure
- Connection between finite and infinite versions
- Compactness argument
- Contrast with the unsolved infinite conjecture
- Axiomatization of the Milliken-Taylor theorem

## Key Definitions

### Finite Sums (FS)
```lean
def FS (A : Finset ℕ) : Set ℕ :=
  {s | ∃ I : Finset A, I.Nonempty ∧ s = ∑ i in I, (i : ℕ)}
```

### Finite Products (FP)
```lean
def FP (A : Finset ℕ) : Set ℕ :=
  {p | ∃ I : Finset A, I.Nonempty ∧ p = ∏ i in I, (i : ℕ)}
```

### Monochromaticity
```lean
def IsMonochromaticSumsProducts (χ : Coloring r) (A : Finset ℕ) : Prop :=
  ∃ c : Fin r, ∀ s ∈ FS A, χ s = c ∧ ∀ p ∈ FP A, χ p = c
```

## Main Results

### 1. Main Theorem
```lean
theorem main_theorem (r m : ℕ) (χ : Coloring r) :
  ∃ A : Finset ℕ, A.card = m ∧ (∃ c : Fin r, 
    ∀ s ∈ FS A, χ s = c ∧ ∀ p ∈ FP A, χ p = c)
```

### 2. Finite Sums-Products Theorem (Bergelson-Hindman)
```lean
theorem finite_sums_products_theorem (r m : ℕ) (χ : Coloring r) :
  ∃ A : Finset ℕ, A.card = m ∧ A.Nonempty ∧ IsMonochromaticSumsProducts χ A
```

### 3. Finite Bound Version
```lean
theorem finite_bound_version (r m : ℕ) :
  ∃ N : ℕ, ∀ χ : ℕ → Fin r, 
    (∃ A : Finset ℕ, 
      A ⊆ Finset.range N ∧ 
      A.card = m ∧ 
      IsMonochromaticSumsProducts χ A)
```

## Proof Strategy

1. **Apply Bergelson-Hindman Result**: The finite sums-products theorem (derived from Milliken-Taylor) gives us the existence of monochromatic configurations.

2. **Quantifier Structure**: The theorem has the form:
   ```
   ∀ r ∀ χ: ℕ → Fin r ∀ m 
   ∃ A: |A| = m ∧ (FS(A) ∪ FP(A)) is monochromatic
   ```

3. **Compactness**: The finite bound version is equivalent to the infinite version via a compactness/diagonal argument.

4. **Arbitrary Size**: Since m is arbitrary, we obtain arbitrarily large finite configurations.

## Contrast with Infinite Conjecture

The **stronger** infinite conjecture (open problem) asks:
```
∀ r ∃ (aₙ)ₙ₌₁^∞: ∀ χ: ℕ → Fin r
  ∃ c: (FS({a₁,a₂,...}) ∪ FP({a₁,a₂,...})) is monochromatic in color c
```

This would require one infinite sequence that works for ALL colorings, not just arbitrary finite configurations.

**Analogy**: 
- **Finite version** ↔ van der Waerden's theorem (finite arithmetic progressions)
- **Infinite version** ↔ Szemerédi's theorem (infinite arithmetic progressions)

## References

- Bergelson, V.; Hindman, N. (1988). "Noncommutative structures in combinatorics"
- Milliken, K. R. (1975). "Ramsey's theorem with sums or unions"
- Hindman, N. (1974). "Finite sums from sequences within cells of a partition of ℕ"

## Status

This is a formal mathematical exposition. The core results are:
- ✓ Definitions of FS and FP formalized
- ✓ Main theorem statement formalized
- ✓ Supporting lemmas and helper results
- ⏳ Full formal proof depends on integrating Milliken-Taylor theorem from Mathlib

## Lean Version

These files are written for **Lean 4** with Mathlib imports.

## Building

To build these files (requires Lean 4 and Mathlib):
```bash
lake build
```

## Notes for Formalization

1. The hardest part of the formal proof would be establishing the Milliken-Taylor theorem or accessing it from a formalized library.

2. The pigeonhole principle and basic Ramsey theory tools needed are standard in Mathlib.

3. The compactness argument connecting finite and infinite versions is classical but requires careful treatment in constructive logic.

4. The proof is actually constructive up to the use of the Milliken-Taylor theorem, which may use choice principles internally.

---

**Last Updated**: 2026-06-02  
**Paper Formalized**: Finite Sums and Products (based on Bergelson-Hindman)
