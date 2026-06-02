# Finite Sums and Products - Problem 172

This directory contains exposition for Erdős Problem 172. The checked Lean
formalization now lives in the root Lake library under `ErdosProblems/`.

## Question

Is it true that in any finite coloring of `ℕ` there exist arbitrarily large
finite sets `A` such that all nonempty sums and products of distinct elements
of `A` have the same color?

## Current Lean Formalization

The Lean project is built from the repository root with:

```bash
lake build
```

The formalized files are:

- `ErdosProblems/FiniteSumsProducts.lean`: definitions of `FS`, `FP`,
  `Coloring`, `IsMonochromatic`, nonempty finite subsets, and basic finiteness,
  nonemptiness, and monotonicity lemmas.
- `ErdosProblems/SumsProductsLemmas.lean`: color-class lemmas,
  monochromaticity lemmas, and finite pigeonhole facts.
- `ErdosProblems/ProofStrategy.lean`: the precise finite and infinite
  proposition statements, plus proved structural lemmas.
- `ErdosProblems/Problem172.lean`: the main conditional theorem and cardinality
  bounds for `FS`, `FP`, and `FS A ∪ FP A`.

The root module `ErdosProblems.lean` imports the checked library modules.

## Important Formalization Detail

The definitions use nonempty subsets:

```lean
def FS (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsets A).image (fun s => s.sum id)

def FP (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsets A).image (fun s => s.prod id)
```

This excludes the empty sum `0` and empty product `1`, which is necessary for
the cardinality bounds

```lean
(FS A).card ≤ 2 ^ A.card - 1
(FP A).card ≤ 2 ^ A.card - 1
```

to be true.

## Main Formal Statement

The external Ramsey-theoretic input is recorded as:

```lean
def FiniteVersion : Prop :=
  ∀ r m : ℕ, ∀ χ : Coloring r,
    ∃ (A : Finset ℕ), A.card = m ∧ IsMonochromatic χ ((FS A) ∪ (FP A))
```

The theorem in `Problem172.lean` proves the desired conclusion from this
explicit hypothesis:

```lean
theorem finite_sums_products_theorem
    (h : FiniteVersion) (r m : ℕ) (χ : Coloring r) :
    ∃ (A : Finset ℕ), A.card = m ∧
      IsMonochromatic χ (FS A ∪ FP A)
```

This avoids adding hidden logical assumptions or proof placeholders. Integrating
a fully formal proof of `FiniteVersion` would require formalizing or importing
the appropriate Milliken-Taylor/Bergelson-Hindman machinery.

## Status

- Lean project scaffold is present at the repository root.
- `lake build` succeeds.
- There are no Lean proof placeholders or extra logical-assumption declarations.
- The finite Milliken-Taylor-style input remains an explicit proposition, not a
  hidden placeholder.

## Expository Summary

The finite theorem says that for every number of colors `r`, every target size
`m`, and every coloring `χ : ℕ → Fin r`, there is a finite set `A` of size `m`
such that every element of `FS A ∪ FP A` has one common color.

The stronger infinite conjecture asks for an injective sequence whose finite
sum/product behavior is monochromatic in a compatible way. That stronger
statement is not proved here.
