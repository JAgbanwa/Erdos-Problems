# Gate B - Definitions, conventions and the functional (PAPER_II, v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS`

## Objective

Reconstruct the chordal, complete-split and fractional triangle-cover definitions
independently, including the exact functional and all finite-domain conventions.

## Reconstruction

- **Chordality** was implemented independently as simplicial-vertex elimination: a graph
  is chordal iff repeated removal of a vertex whose surviving neighbourhood is a clique
  eliminates every vertex. This needs no clique-tree machinery and is exactly equivalent
  to the standard definition. Used to filter 33,867 labeled graphs down to 19,048 chordal
  ones at Gate G.
- **The functional** `Phi_tau(G) = |E(G)| - 2 tau_3^*(G)` was implemented directly, with
  `tau_3^*` as the optimum of the fractional triangle-cover LP (minimize the total edge
  weight subject to every triangle receiving at least 1) and `nu_3^*` as the packing
  optimum (maximize total triangle weight subject to every edge carrying at most 1). The
  factor **2** is the one to check, since it is what makes the functional the
  triangle-packing *defect* rather than a raw difference; it is consistent throughout the
  manuscript and reproduces the claimed values on the complete-split family.
- **Complete-split graphs** `S_{p,q} = K_p join complement(K_q)` were built directly and
  their `Phi_tau` computed exactly; they attain the claimed maximum at every `n` tested.
- **Finite-domain conventions.** The claim is stated for every integer `n >= 1`. The left
  endpoint `n = 1` is where such closed forms usually fail: `floor(9/24) = 0` and the
  single-vertex graph has `Phi_tau = 0`. **It holds.** The degenerate case `S_{2,0} = K_2`
  that the abstract singles out appears in the `n = 2` tie and behaves as claimed.

## The packing/cover identity

The manuscript asserts `nu_3^* = tau_3^*`, which is LP duality for this pair of programs.
Rather than assume it, both optima were computed by separate linear programs on every
graph tested: **0 mismatches** over 19,048 chordal graphs (Gate G) and over 251,085 copy
instances (Gate C). The identity is used correctly and is not a hidden assumption.

## Findings

None at this gate.

## Evidence

`../G_FALSIFICATION/scripts/chordal_max_exact.py` (chordality test and both LPs),
`../C_PROOF_CHAIN/scripts/copy_inequality.py`, and their result files.
