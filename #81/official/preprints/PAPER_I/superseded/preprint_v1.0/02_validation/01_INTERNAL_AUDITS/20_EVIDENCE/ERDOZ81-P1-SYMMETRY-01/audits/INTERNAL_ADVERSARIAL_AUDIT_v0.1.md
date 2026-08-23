# Audit Record

Audit ID: ERDOZ81-P1-SYMMETRY-01-AUD-001  
Gate ID: ERDOZ81-P1-SYMMETRY-01  
Statement version: 0.1  
Audit type: SELF_AUDIT / internal adversarial audit  
Independence level: producer and auditor are the same agent, with separated records  
Auditor: Researcher, auditor role  
Date: 2026-07-05  
Protocol version: 1.0

## Scope

Attempt to reject the stabilizer-averaging reduction.

## Checks performed

1. **Correct group.** The full symmetric group on \(K\) is not used; only permutations preserving \(S\) setwise are allowed.
2. **Action convention.** Checked the inverse in \((gz)_e=z_{g^{-1}e}\).
3. **Feasibility.** Triangle inequalities are permuted, not altered.
4. **Convexity.** Averaging is valid because \(\mathcal P_p\) is convex.
5. **Objective invariance.** Coefficients are constant on the stabilizer edge orbits.
6. **Negative coefficient.** The proof uses equality under permutation, so no nonnegativity assumption is needed.
7. **Empty orbits.** For \(s=2\), \(o=0\), or \(o=1\), nonexistent edge classes are omitted rather than assigned fictitious variables.
8. **Small \(p\).** When \(p=2\), the polytope has no triangle constraints but averaging remains valid.
9. **Nonunique optimizers.** The argument requires only one optimizer and produces another.
10. **No premature LP solution.** No claim is made about the exact feasible inequalities or optimum value.

## Falsification attempts

- \(S=K\), where only the \(SS\) orbit exists.
- \(o=1\), where \(\bar S\bar S\) is empty.
- \(s=2\), where \(SS\) consists of one edge.
- \(q>s-1\), making the \(SS\) objective coefficient negative.
- \(p=2\), where no triangle constraint exists.

The averaging statement remains valid in all cases.

## Findings

No mathematical defect found.

## Material objections

The downstream three-orbit gate must enumerate triangle orbits conditionally on their existence. Writing all four inequalities unconditionally would be incorrect in boundary cases.

## Verdict

`CONFIRM_PROVISIONAL_PASS`.

## Required actions before PASS

- Evidence admission.
- Upstream definition/profile gates promoted as required.
- Downstream boundary-aware orbit enumeration.
