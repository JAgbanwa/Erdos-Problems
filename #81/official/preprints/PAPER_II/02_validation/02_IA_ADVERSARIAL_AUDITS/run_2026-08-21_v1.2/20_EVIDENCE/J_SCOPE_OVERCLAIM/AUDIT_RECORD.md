# Gate J - Scope and overclaim (PAPER_II, preprint_draft_v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS`

## Method

Regex sweep for the status vocabulary protocol Section 5.6 names, then each occurrence
read in context. A targeted search was made for constructions asserting resolution of the
Erdos problem.

## Results

- **No resolution claim.** Searching for "settles / resolves / solves" plus a
  problem-or-conjecture object returned only false positives: L44 "**Solv**ing its two
  branches" (about the two-variable LP), L196 a section-contents sentence, and L1077
  about `level_set_iff`. **Paper II makes no claim to resolve Erdos Problem #81.**
- **Status.** L9 "Preprint draft: version 1.2"; L11 `EDITORIAL_DRAFT_WITH_OPEN_GATES`,
  `unpublished`, and names "Independent clean-room reproduction, external adversarial
  audit, external peer review" as open release gates. Accurate.
- **Novelty framing.** L13 states the internal literature audit found no earlier result
  determining the same exact finite extremum, then labels it explicitly an internal
  editorial assessment and not a substitute for independent prior-art review. Correct
  posture.
- **Formalization language.** L1185 states the report "contains no `sorryAx` and no
  project-specific axiom" and prints the delivered archive name and SHA-256 - both
  verified correct at Gate G0. L1187, Table 4, is captioned "Frozen formalization
  perimeter (**Lean v1.2**)" and states "independent reproduction remains pending". The
  v1.1-era mislabeling of this table is corrected.
- **Author-side evidence not dressed as independent.** No author-side record is described
  as independent reproduction; the pending status is stated in two places.
- **Scope fences.** The abstract states the paper "proves only the fractional
  cover-functional theorem" and "does not prove an integral clique-partition theorem", and
  that its proof "does not use strong LP duality or an asymptotic packing theorem". It also
  bounds the uniqueness claim to the clique size within the complete-split family. Each of
  these is a self-limitation, and each is accurate on the evidence gathered.
- **`sharp` / `optimal`.** "Sharp" occurs once, and "optimal" occurrences refer to LP
  optima (optimal covers, optimal solutions), not to claimed optimality of a constant. No
  instance of a sharp quadratic coefficient being allowed to imply an optimal linear one -
  the situation that produced a finding in Paper I - arises here, because Paper II proves
  an **exact** maximum rather than a bound with an unoptimized additive term.

## Findings

None at this gate.
