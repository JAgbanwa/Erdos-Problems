# Summary of changes for run 5111cd0a-fccb-4ba6-8637-e6a5ef6a47ec
All formalisations are now consolidated into a single Lean file: `RequestProject/Paper.lean`.
What I did:
- Merged the entire development (previously spread across 16 files under `RequestProject/`) into one file, `RequestProject/Paper.lean`, concatenating the sources in dependency order (Defs → Basic → Recurrence → Chromatic → Cover → Centralizer → UpperBound → MainBounds → Neumann → Dihedral → HThree → SmallValues → Results → Extraspecial group construction → Extraspecial bounds), with a single `import Mathlib` at the top and clear section-header comments marking each original source.
- Removed the now-redundant per-topic files (and the old `Main.lean` aggregator) so the project consists of exactly one Lean file, as requested.
Verification:
- The project builds successfully (`lean_build` on the whole library) with the single file.
- The merge is faithful: no proofs were altered and no new `sorry`s were introduced. The only remaining `sorry`s are the same four pre-existing ones — the two deep Section 6 symplectic computations for the extraspecial group (`ωnc(E r) = 2r+1` and `ac(E r) = 2^r+1`) — exactly as documented previously.
- Spot-checked that a fully-proved main result (`h_upper_bound`, i.e. `h(n) ≤ Uₙ`) uses only the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
All changes are committed and pushed.
# Summary of changes for run e6a25505-ba39-4516-b6e7-59ae5ddfcec9
I formalized the paper *Abelian Subgroup Covers Under a Bound on Pairwise Noncommuting Sets* in Lean 4 + Mathlib. The full library builds; the only remaining `sorry`s are the two deep symplectic computations of Section 6 (see below). A detailed writeup is in `SUMMARY.md`.
## Core definitions (`RequestProject/Defs.lean`)
- `wnc G : ℕ∞` — the noncommuting number `ωnc(G)` (sup of sizes of pairwise-noncommuting finite sets);
- `ac G : ℕ∞` — the abelian covering number (least size of a cover by abelian subgroups);
- `U : ℕ → ℕ` — the recurrence `U₁=U₂=1`, `Uₙ = n·Uₙ₋₂`;
- `h : ℕ → ℕ∞` — `h(n) = sup { ac(G) : ωnc(G) ≤ n }`.
## Proved in full (standard axioms only)
- **Prop 2.2 (≤):** `ωnc(G) ≤ ac(G)` (`Chromatic.lean`).
- **Section 3:** centralizer lemmas incl. the "centralizer drop by two" (`Centralizer.lean`).
- **Theorem 4.2 (elementary upper bound):** `ωnc(G) ≤ m ⟹ ac(G) ≤ Uₘ`, hence `h(n) ≤ Uₙ` — so `h(n)` is finite (`UpperBound.lean`, `MainBounds.lean`).
- **Lemma 4.1:** closed forms `U₂ᵣ = 2^{r-1}·r!`, `U₂ᵣ₊₁ = (2r+1)!!`, and monotonicity of `U` (`Recurrence.lean`).
- **Prop 7.1 / Cor 7.2 (dihedral):** for odd `q ≥ 3`, `ωnc(D₂q) = ac(D₂q) = q+1`, giving `h(n) ≥ n` for even `n ≥ 4` (`Dihedral.lean`).
- **Theorem 8.1 (small values):** `h(1)=h(2)=1`, `h(3)=3`, `h(4)=4` (`SmallValues.lean`, `HThree.lean`, `Results.lean`).
- **Section 9:** Lemma 9.7 (`ac(G) ≤ [G:Z(G)]` for finite-index centre) fully proved; Theorem 9.8 (`h(n) ≤ Cⁿ`) proved conditionally on the quantitative centre theorem (Cor 9.6), taken as an explicit hypothesis since the paper itself cites Neumann and Pyber as external inputs (`Neumann.lean`).
## Stated faithfully but with `sorry` (Section 6)
The extraspecial group `E r` is fully constructed, including its group law and the commutation criterion via the symplectic form (`Extraspecial/Group.lean`). Its two exact computations — `ωnc(E r) = 2r+1` (Thm 6.2) and `ac(E r) = 2^r+1` (Thm 6.5) — are stated in `Extraspecial/Bounds.lean` but not yet proved: their proofs require the symplectic linear algebra of Section 5 (symplectic bases, isotropic-subspace dimension, rank of the off-diagonal all-ones matrix). From these statements the exponential lower bounds `h(2r+1) ≥ 2^r+1` and `h(n) ≥ 2^⌊(n-1)/2⌋+1` (Cor 6.6) are derived.
## Assessment of "how true is this?"
Everything checked is faithful to the paper. Verified with no extra assumptions: the superexponential upper bound `h(n) ≤ Uₙ`, the closed forms, the dihedral lower bound, and the exact values `h(1..4)`. The sharp upper bound `h(n) ≤ Cⁿ` is verified modulo the two cited external theorems, exactly as in the paper. I also found a typo: the paper's abstract prints `ac(E_r) = 2r+1`, but its own proof (and Prop 6.4's spread of `2^r+1` subspaces) gives `ac(E_r) = 2^r+1` — the exponential value needed for the lower bound, which is what I recorded. The one substantive gap is the exponential lower bound's two `E_r` computations, left as documented `sorry`s.
