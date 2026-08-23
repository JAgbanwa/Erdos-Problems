# Gate A - Definitions and claims (PAPER_II, preprint_draft_v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS`

## Claim map

**`P2-MAIN-V1_2`** - the exact chordal maximum. Abstract and Theorem 1.1: for every
integer `n >= 1`,

    max { Phi_tau(G) : G chordal, |V(G)| = n } = floor((2n+1)^2/24)

with `Phi_tau(G) = |E(G)| - 2 tau_3^*(G)`, together with attainment by a complete-split
graph. Formal: `PaperII.theorem_1_2`. Role: **final theorem**.
Falsified against: exhaustive enumeration of all chordal graphs on up to 6 vertices with
both `nu_3^*` and `tau_3^*` computed exactly. **Survived** (Gate G).

**`P2-EXTREMIZER`** - maximizers, level sets and copy defects. Formal:
`Fsat_argmax_unique`, `Fsat_argmax_tie`, `level_set_iff`, `copyDefect_nonneg`,
`copyGamma_ge_half_copyDefect`. Role: **structural bridges**.
Falsified against: the copy inequality on 251,085 exhaustive instances, and the observed
argmax and tie pattern in the enumeration. **Survived** (Gates C, G).

**`P2-ASYM-COR`** - asymptotic, modular and Paper-I comparison corollaries. Formal:
`phiTau_max_sandwich`, `odd_sq_emod_24`, `phiTau_max_closed`,
`phiTau_max_le_paperI_bound`. Role: **byproducts** of the closed value.
Falsified against: exact integer arithmetic over `n` in `[-20000, 20000]`. **Survived**
(Gate F), including the negative-`n` range the sandwich is stated for.

**`P2-FORMAL-CONFORMANCE`** - the full v1.2 surface and reusable components. Formal:
`PaperII`, `Contrib.Submission.Chordal`, `Contrib.Submission.GeodesicChordless`.
Role: **byproduct / reusable lane**. Assessed at Gate H.

## Definitions checked for coherence

| Object | Definition | Coherent |
|---|---|---|
| `tau_3^*` | fractional triangle-cover number | yes |
| `nu_3^*` | fractional triangle-packing number | yes |
| `Phi_tau(G)` | `\|E(G)\| - 2 tau_3^*(G)` | yes |
| the identity `nu_3^* = tau_3^*` | asserted in the abstract | **independently confirmed**: 0 mismatches over 19,048 chordal graphs and again over 251,085 copy instances, with the two optima computed by separate linear programs |
| `S_{p,q}` | complete-split graph `K_p join complement(K_q)` | yes |
| `G_{v->u}` | copy operation, `v` becomes a clone of `u` | yes |

## Scoping that the audit specifically checked, and found correct

The abstract limits the uniqueness claim: "The uniqueness/tie statement concerns the
maximizing clique size within the complete-split family. The paper does **not** claim that
every chordal extremizer is uniquely determined up to isomorphism." The Gate G enumeration
confirms that the weaker claim is the right one - ties in the maximizing clique size do
occur (at `n=2` and `n=4`) - and this audit did **not** test the stronger statement, which
the paper does not make.

The abstract also states what the paper does not prove: "It does not prove an integral
clique-partition theorem; its cover-first proof does not use strong LP duality or an
asymptotic packing theorem." The reference list contains no asymptotic packing result,
consistent with that claim.

## Protocol Section 5.2 distinctions

| Distinction | Status |
|---|---|
| source present | yes, 42 project `.lean` files per the freeze metadata |
| target compiled | assessed at Gate H |
| aggregate root imports target | assessed at Gate H - the protocol explicitly warns that the aggregate `PaperII` target does not by itself prove `Extremizer` and `CopyDefect` are imported |
| public API re-exports declaration | not applicable |
| headline theorem has the claimed axiom footprint | assessed at Gate H |

## Findings

None at this gate.
