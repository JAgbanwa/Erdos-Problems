# PR-ready drafts (Zulip announcements + PR descriptions)

Everything below is pre-written so the only remaining steps are the **human/external** ones
(sign the CLA, post to Zulip, create the branch, click "open PR"). Two independent
contributions — submit them as **two separate PRs**.

---

## Contribution 1 — Dirac's theorem (`Submission/Dirac.lean`)

**Target file:** `Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean` (add the theorem there).
**Main declaration:** `SimpleGraph.IsHamiltonian_of_minDegree`.

### Zulip announcement (post in `#mathlib4`, thread "Dirac's theorem")
> Hi all — I'd like to contribute **Dirac's theorem** (a finite simple graph on `n ≥ 3`
> vertices with minimum degree `≥ n/2` has a Hamiltonian cycle) to
> `Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean`. Mathlib has `IsHamiltonian` /
> `IsHamiltonianCycle` but not this existence theorem. I have a complete, self-contained proof
> (classical rotation–extension argument), sorry-free and axiom-clean
> (`[propext, Classical.choice, Quot.sound]`), developed as a by-product of a formalization
> project (with AI assistance, human-reviewed). Is this wanted, and is anyone already working
> on it? Happy to adapt the statement/API to reviewers' preferences.

### PR title
`feat(Combinatorics/SimpleGraph): Dirac's theorem (Hamiltonicity from minimum degree)`

### PR description
> Adds **Dirac's theorem**: `SimpleGraph.IsHamiltonian_of_minDegree` — a finite simple graph
> `G` on `V` with `3 ≤ Fintype.card V` and `Fintype.card V ≤ 2 * G.minDegree` is Hamiltonian
> (proved via `Walk.IsHamiltonianCycle`).
>
> Proof: the classical longest-path rotation–extension argument. Self-contained; uses only
> existing Mathlib API (`Walk`, `IsHamiltonianCycle`, `minDegree`, `List.IsChain`).
> Sorry-free; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
>
> Developed with AI assistance (theorem prover) and human-reviewed as a by-product of a
> combinatorics formalization; the submitter takes responsibility for the code.
>
> Label: `t-combinatorics`.

---

## Contribution 2 — matching from minimum degree (`Submission/Matching.lean`)

**Target file:** `Mathlib/Combinatorics/SimpleGraph/Matching.lean` (add the theorems there).
**Main declarations:** `SimpleGraph.exists_isPerfectMatching_of_minDegree` (even case) and the
near-perfect odd-case variant.

### Zulip announcement (post in `#mathlib4`, thread "matching from min degree")
> Hi all — I'd like to contribute the result that a finite simple graph with
> `minDegree ≥ n/2` has a perfect matching (even `n`) resp. a near-perfect matching (odd `n`),
> to `Mathlib/Combinatorics/SimpleGraph/Matching.lean`. It's a short consequence of Mathlib's
> Tutte theorem (a high-min-degree graph has no Tutte violator). Self-contained, sorry-free,
> axiom-clean. Developed with AI assistance, human-reviewed. Wanted? Anyone already on it?

### PR title
`feat(Combinatorics/SimpleGraph): (near-)perfect matching from minimum degree ≥ n/2`

### PR description
> Adds `SimpleGraph.exists_isPerfectMatching_of_minDegree` (for `Even (card V)` and
> `card V ≤ 2 * G.minDegree`, `∃ M : G.Subgraph, M.IsPerfectMatching`) and the odd-case
> near-perfect variant (matching covering all but one vertex, `M.verts = {w}ᶜ`).
>
> Proof: via Mathlib's Tutte theorem — a minimum degree `≥ n/2` rules out any Tutte violator;
> the odd case uses an apex-vertex reduction. Uses the `Subgraph.IsMatching` /
> `IsPerfectMatching` API. Sorry-free; `#print axioms` = `[propext, Classical.choice,
> Quot.sound]`.
>
> Developed with AI assistance (theorem prover), human-reviewed. Label: `t-combinatorics`.

---

## Remaining PR-time steps (human/external — NOT done here)
1. Sign the Mathlib CLA (first PR only).
2. Post the Zulip announcements above; get a maintainer's go-ahead.
3. Fork `mathlib4`, branch per contribution.
4. Move each declaration into its target file above. **Import minimization is done here, in
   the Mathlib tree**: once the declarations sit in the target file, run `lake exe shake` to
   compute/trim to the minimal `Mathlib.*` imports (the standalone draft intentionally uses
   `import Mathlib`, which cannot be minimized outside the Mathlib module graph). Keep the
   copyright header + docstrings.
5. `lake exe cache get && lake build`; `lake exe runLinter` + `lake exe shake`; ensure CI green.
6. Open the two PRs against `master`, label `t-combinatorics`, paste the descriptions above,
   disclose AI assistance, request review.
