# Paper III v1.0.4 — Proof Dependency Ledger

## Internal spine

| Result | Used to prove | Internal inputs |
|---|---|---|
| Theorem 3.1 | exact common-profile packing | four-orbit LP and duality |
| Lemma 4.1 | Theorem 4.2 | replication of a fractional cover |
| Theorem 4.2 | bulk branch | Theorem 3.1, Lemma 4.1, square completion |
| Lemma 5.1 | short corridor | complete-graph factorization and averaging |
| Lemma 5.2 | high-dispersion branch | double-factor averaging |
| Lemma 6.1 | high-dispersion gain | exact set-difference count |
| Lemma 7.1 | low-dispersion branch | factorization, list edge coloring, gain completion |
| Section 8.3 | sparse-independent branch | path parity correction and modulo-three correction |
| Section 9 | Theorem 1.1 | exhaustion of bulk, sparse, and near-extremal regimes |

## External mathematical inputs

| Input | Exact use | Location |
|---|---|---|
| Haxell--Rödl/Yuster | \(\nu_3^*-\nu_3=o(n^2)\) for fixed triangles | Theorem 2.1, Section 9.1 |
| Borodin--Kostochka--Woodall | proper list edge coloring of the bipartite gain graph | Theorem 2.2, Section 7.2 |
| Dense triangle decomposition | exact decomposition of a sufficiently dense triangle-divisible residual | Theorem 2.3, Section 8.3 |
| Dirac | Hamilton cycles/paths and large matchings | Sections 8.2--8.3 |
| Turán | existence of a \(K_5\) in the corrected dense residual | Section 8.3 |

## Non-dependencies

- computational scripts;
- finite LP or ILP enumeration;
- randomized testing;
- the explicit numerical regression audit;
- Paper I.

Paper II supplies contextual fractional extremal information but is not a logical input to the proof of Theorem 1.1.
