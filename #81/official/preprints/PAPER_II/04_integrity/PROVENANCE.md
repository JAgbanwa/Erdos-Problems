# Provenance -- Paper II, preprint v1.0

- **Manuscript.** Authored by Juan Pablo Traverso Gianini with AI-assisted
  exploratory, computational, adversarial, editorial, and translation support
  (systems from Anthropic, Google, OpenAI). The author reviewed the mathematics,
  selected the final arguments, and is solely responsible for the content. The
  English and Spanish versions were checked for cross-format and cross-language
  consistency (identical mathematics; only prose translated).
- **Formalization.** Lean 4 / Mathlib v4.28.0. The released `05_formalization/lean`
  tree is the exact source of repository commit `5f2d448`; each file matches the
  committed object by SHA-256. The theorem `PaperII.theorem_1_2` builds
  `sorry`-free with axiom report `[propext, Classical.choice, Quot.sound]`.
- **Validation.** Internal AI adversarial audits (sections A-F) plus object-level
  audit of the committed Lean artifact. No external peer review; no independent
  third-party build reproduction yet.
- **Integrity.** `SHA256SUMS.txt` was regenerated over the final release tree.

Release d