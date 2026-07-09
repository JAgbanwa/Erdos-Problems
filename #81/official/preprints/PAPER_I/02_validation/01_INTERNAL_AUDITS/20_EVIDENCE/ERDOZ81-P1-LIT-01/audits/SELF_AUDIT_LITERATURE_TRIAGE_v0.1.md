# Self-Audit — Literature Triage v0.1

Audit ID: ERDOZ81-P1-LIT-01-AUD-001
Gate ID: ERDOZ81-P1-LIT-01
Statement version: 0.1
Audit type: SELF_AUDIT
Independence level: producer self-audit
Date: 2026-07-05
Protocol version: 1.0

## Checks performed

1. Separated correctness from provenance and novelty.
2. Verified that Gates 1–3 and 5–9 contain internal arguments rather than hidden
   applications of the historical clique-partition bounds.
3. Confirmed that the strong-LP-duality dependency was replaced by an internal proof.
4. Located Theorem 1 in Chen--Erdős--Ordman for the \(3/16\) bound.
5. Located Haxell--Rödl's fixed-graph transfer as Theorem 1.1 in Yuster's exposition,
   and Yuster's family extension as Theorem 1.2.
6. Checked that the \(1/6\) statement is a lower/example benchmark in the 1993 paper,
   not the desired universal upper bound.
7. Treated unsuccessful formula searches as inconclusive, not as novelty evidence.

## Findings

- No prior gate requires reopening for mathematical error.
- The provenance gate cannot be `PASS` because \(R(p,q)\) has not yet been derived
  and the external transfer certificate is not complete.
- The orbit-solution gate may proceed after this classification, provided it treats
  \(U,D,H\) as internal candidates and proves every claimed inequality.
- A full novelty review remains deferred until publication preparation.

## Verdict

`PROVISIONAL_PASS / SELF_AUDITED / UNVERIFIED`.

## Required actions

- Derive \(R(p,q)\) rather than importing it.
- Complete one transfer certificate only after the exact final corollary is fixed.
- Re-run a deeper prior-art review before paper release.
