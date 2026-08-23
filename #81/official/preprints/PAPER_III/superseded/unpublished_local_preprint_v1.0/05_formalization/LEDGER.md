# Proof Ledger — Paper III (Linear-Error Clique Partitions of Split Graphs)

**Purpose.** This is the formalization base for the machine-checked (Lean/mathlib,
Aristotle) verification of Theorem 1.1. It lists every statement in dependency order,
with exact hypotheses, so that each node maps to one Lean declaration. It matches
`PAPER_III_split_lineal_v0.9.0.md` section by section.

**Two layers (see §11.6 of the paper).**
- **Layer X** — two external asymptotic theorems, stated here as *axioms* with exact
  hypotheses. Not to be proved.
- **Layer E** — everything else: finite linear programs, counting, averaging, completed
  squares. This is the sorry-free target.

**Audit status.** Every algebraic identity below was checked symbolically
(`verify_ledger_algebra.py`) and every quantitative lemma against exact ILP / exact
rational arithmetic (`audit_c_fast.py`, `audit_c_ilp.py`): 46,390 + 91 checks, no
discrepancy. Symbols verified: T(G) identity = 0; (9.12) `s²` coefficient = −5/288;
(9.19) identity = 0; (9.20) = `s²/64`; δ ≥ 7/8 at s = p/8 in both parities of p;
corridor threshold `6√p = p/8 ⟺ p = 2304`.

---

## 0. Notation (Lean: a `structure` for the split graph and its profile)

- `G = (K ⊔ I, E)` split: `K` clique, `|K| = p`; `I` independent, `|I| = q`; `n = p+q`.
- For `vᵢ ∈ I`: `Nᵢ = N(vᵢ) ∩ K`, `dᵢ = |Nᵢ|`, `Sᵢ = K ∖ Nᵢ`, `mᵢ = |Sᵢ|`.
- `M = Σ mᵢ`, `S₂ = Σ mᵢ²`, `m = maxᵢ mᵢ`.
- Near `q = 2p`: `s = 2p − q`.
- `α = q/p`.
- `ν₃(G)` = max edge-disjoint triangles; `ν₃*(G)` = fractional optimum.
- `Φ(G) = |E(G)| − 2 ν₃(G)`.
- `χ'(K_t) = t−1` (t even), `t` (t odd); `χ'(K₀)=χ'(K₁)=0`. `r_p = χ'(K_p)`.
- `T(G) = ½ ( |E(G)| − (p+q)²/6 )`.

**Goal (Theorem 1.1).** `∃ C, ∀` split `G`: `Φ(G) ≤ n²/6 + C·n`.
Corollary 1.2: `cp(G) ≤ n²/6 + C·n`, from `cp(G) ≤ |E| − 2ν₃(G)` (Lemma D.2 of Paper D
/ trivial: each packed triangle replaces 3 edge-cliques by 1).

---

## Layer X — external axioms (DO NOT PROVE)

**AX1 (Haxell–Rödl / Yuster).** For the fixed graph `K₃`, uniformly over graphs `G`:
`ν₃*(G) − ν₃(G) = o(|V(G)|²)`. Used only in §4.3/§9.1 (bulk).
Formal form: `∀ ε>0, ∃ n₀, ∀ G, |V(G)|≥n₀ → ν₃*(G) − ν₃(G) ≤ ε·|V(G)|²`.

**AX2 (Dross + Barber–Kühn–Lo–Osthus).** `∀ ε>0, ∃ n₀, ∀` triangle-divisible `H`
(`|E(H)| ≡ 0 mod 3`, all degrees even) with `|V(H)|≥n₀` and `δ(H) ≥ (0.9+ε)|V(H)|`:
`H` has an exact triangle decomposition. Used only in §8 (sparse, α→0).

*Everything below is Layer E.*

---

## 1. Common-profile linear program (§3)

**E-3.1 (Common-profile formula).** Let `H(p,q,d)` be the split graph with clique `K`
(`|K|=p`), independent set `I` (`|I|=q`), every `vᵢ` with the same neighborhood `N`,
`|N|=d`; put `r = p−d`. Then for `p ≥ 3`:
```
ν₃*(H(p,q,d)) = F(p,q,d)
             := min{ (C(p,2)+q·d)/3 ,  C(d,2)+C(r,2) ,  C(d,2)+(d·r+C(r,2))/3 }.
```
- **Depends on:** finite LP duality (Farkas, in mathlib).
- **Proof:** symmetrize the triangle-cover LP over `Sym(N)×Sym(R)×Sym(I)` → 4 weights
  `(a,b,c,e)`, 5 constraints (3.1)–(3.2), objective (3.3); the objective is affine on the
  reduced triangle `1/3 ≤ e ≤ a ≤ 1`, so the min is at a vertex `(1/3,1/3),(1,1),(1,1/3)`;
  the three values are the three terms of `F`. Duality gives `=`.
- **Audit:** 245/245 exact vs direct triangle LP (`audit_c_fast.py`, part A).
- **Formal note:** the LP is fixed-size (4 vars, 5 constraints); `F` can be *defined* by
  the min and the ≤ direction proved by exhibiting the dual, the ≥ by the primal vertex.

## 2. Replication and the fractional margin (§4)

**E-4.1 (Replication).** For split `G` with `q ≥ 1`:
`ν₃*(G) ≥ (1/q) Σᵢ F(p,q,dᵢ)`.
- **Depends on:** E-3.1.
- **Proof:** from an optimal cover `y` of `G`, clone `vᵢ` into `q` twins with `Nᵢ` and its
  incident weights → a cover of `H(p,q,dᵢ)` of value `A + q·Bᵢ ≥ F(p,q,dᵢ)`; sum over `i`,
  minimize over covers.

**E-4.2 (Unified fractional margin).** With `α=q/p`,
```
μ(α) = α²/12            if 0 ≤ α ≤ 2/3,
       (2−α)²/48        if 2/3 ≤ α ≤ 2,
```
then for `0 < q ≤ 2p`:  `ν₃*(G) ≥ T(G) + μ(α)·p² − p/4`.
- **Depends on:** E-4.1 + algebra.
- **Key identity (verified = 0):** `T(G) = ½ Σ dᵢ + C_α p² − p/4` with
  `C_α = (2−2α−α²)/12`. Each branch of `F` completes to `≥ qd/2 + (C_α+μ(α))p² − p/2`;
  the third residual branch is dominated by the min of the first two (Appendix A).
- **Audit:** 45,904/45,904 exact rational (`audit_c_fast.py`, part B); dominance 241/241.

**E-4.3 (Bulk consequence).** If `ε ≤ α ≤ 2−ε` then `μ(α) ≥ c_ε > 0`; with **AX1**,
`ν₃(G) ≥ T(G)` for `n` large, i.e. `Φ(G) ≤ n²/6`.

## 3. Factorization rounding (§5)

**E-5.1 (One-factor averaging).** If `q ≥ r_p`: `ν₃(G) ≥ (1/q) Σᵢ C(dᵢ,2)`.
- **Depends on:** existence of a proper `r_p`-edge-coloring of `K_p` (1-factorization,
  classical; Lean: `χ'(K_t)` value). **Proof:** factor `K_p` into `r_p` matchings, assign
  injectively/uniformly to `I`; `vᵢ` keeps factor-edges inside `Nᵢ`; expectation
  `(1/q)Σ C(dᵢ,2)`; some assignment meets it.
- **Corollary (5.3), q=2p−s:** `Φ(G) ≤ n²/6 + p/2 + (s²−6s+3)/12`. Closes `s = O(√p)`.
- **Audit:** 16/16 exact ILP.

**E-5.2 (Double-factor inequality).** With `bₑ = |{i : e ⊄ Nᵢ}|`,
`V = Σ_{e∈E(K)} bₑ(q−bₑ)`, `h = min{r_p, q−r_p}`, `δ = h/r_p`, if `q ≥ r_p`:
```
Φ(G) ≤ n²/6 + p/2 − s²/6 + ((s−1)M − S₂)/q − 2δV/(q(q−1)).
```
- **Depends on:** E-5.1 machinery + a second-moment loss bound.
- **Proof:** a factor given two independent vertices loses `e` only if *both* are bad:
  prob `bₑ(bₑ−1)/(q(q−1))` vs `bₑ/q`. Average over the random choice of the `h` doubled
  factors and the injective assignment.
- **Audit:** 27/27 exact ILP (with `V` computed exactly).

## 4. Polarization (§6)

**E-6.1 (Polarization inequality).** With `m = maxᵢ mᵢ`, if `2p − 3m − 1 ≥ 0`:
`V ≥ ((2p − 3m − 1)/4) · Σ_{i,j} |Sᵢ △ Sⱼ|`.
- **Depends on:** counting `|Bᵢ ∖ Bⱼ| = aᵢⱼ(2(p−|Sⱼ|) − aᵢⱼ − 1)/2`, `aᵢⱼ=|Sᵢ∖Sⱼ|`,
  then `|Sⱼ|≤m`, `aᵢⱼ≤m`, sum over ordered pairs.

## 5. Shifted-center gain completion (§7)

**E-7.1 (Reserved-gain shifted-center inequality).** Fix `R ⊆ K`, `ρ=|R|`, `Q=K∖R`,
`b=|Q|`; `Tᵢ=Sᵢ∖R` (`tᵢ=|Tᵢ|`), `Gᵢ=R∖Sᵢ` (`gᵢ=|Gᵢ|`); `A_R=Σtᵢ`, `A₂,R=Σtᵢ²`,
`B_R=Σgᵢ`; `r_b=χ'(K_b)`, `u=q−r_b`; `θ_R=max{ρ−1,0}/b`; `κ_R=1−2(1−θ_R)u/q`.
Under hypotheses (7.1)–(7.2):
```
Φ(G) ≤ n²/6 + p/2 − s²/6 + s·ρ − 2ρ² + κ_R·B_R + ((s−2ρ−1)A_R − A₂,R)/q.
```
Hypotheses (7.1): `b≥2`, `q≥r_b`, `b≥χ'(K_ρ)`. Hypothesis (7.2): `b − tᵢ ≥ max{ρ,u}` ∀i.
- **Depends on:** three edge-disjoint triangle families QQI (factorization), IRQ
  (**E-D.3**, list edge coloring), RRQ (factorization with forbidden-color deletion).
- **List-coloring hypothesis check (fixes former external dependency):** in the gain
  graph `deg(vᵢ)=gᵢ≤ρ` and `deg(r)≤u`, so `Δ ≤ max{ρ,u}`; every list has size
  `b−tᵢ ≥ max{ρ,u} ≥ Δ`. Hence **E-D.3** (max-degree case) applies. *(This is the step
  that removes the Borodin–Kostochka–Woodall citation.)*
- **Audit:** 48/48 exact ILP on instances satisfying (7.1)–(7.2).

## 6. Sparse-independent regime (§8, α→0)

**E-8 (Sparse bound).** If `q = o(p)` and every `v∈I` has `d(v) > (2n−1)/6 + k` (the
minimal-counterexample degree bound), then `Φ(G) ≤ n²/6 + O(n)`.
- **Depends on:** Dirac (Hamilton cycle at `δ > n/2`, classical), Turán (`K₅` at
  `δ > 3p/4`, in mathlib), **AX2**, and the parity/divisibility correction **E-B**.

**E-B (Divisibility correction, Appendix B).** For a path `P=x₁…x_p` and `O⊆V(P)` with
`|O|` even, `J = {xⱼxⱼ₊₁ : |O ∩ {x₁..xⱼ}| odd}` satisfies `Odd(J)=O`, `|E(J)|≤p−1`,
`Δ(J)≤2`. Then a `C₄`/`C₅` inside a Turán-`K₅` fixes `|E| mod 3` keeping degrees even.
- Pure finite combinatorics; fully Layer E.

## 7. List edge coloring, self-contained (Appendix D)

**E-D.1 (Kernel coloring lemma).** `D` kernel-perfect digraph, `|L(v)| ≥ d⁺_D(v)+1` ∀v ⟹
underlying graph is `L`-colorable.
- **Proof:** pick color `c`, `S={v:c∈L(v)}`, kernel `K` of `D[S]`; color `K` with `c`;
  delete `K`, delete `c` from `S∖K`; invariant preserved (each such `v` loses one color
  and ≥1 out-neighbor); recurse.

**E-D.2 (Gale–Shapley).** Every preference system on a bipartite graph has a stable
matching. **Proof:** deferred acceptance; termination (each edge proposed ≤ once) +
stability case analysis.

**E-D.3 (Galvin, max-degree case).** `B` simple bipartite, `Δ=Δ(B)`, `|L(e)| ≥ Δ` ∀e ⟹
`B` has a proper list edge coloring.
- **Depends on:** E-D.1, E-D.2, König edge coloring (proved inline in Step 1 via
  alternating-path recoloring; the parity fact used: in bipartite `B`, any path between
  adjacent `u,r` has odd length).
- **Proof:** König `Δ`-coloring `φ`; preferences (U prefers higher `φ`, R lower `φ`);
  digraph on `E(B)` with arc `e→f` iff `f >_z e` at shared `z`; `d⁺(e) ≤ Δ−1`; kernels of
  induced subdigraphs = stable matchings (E-D.2) ⟹ kernel-perfect; apply E-D.1.

## 8. Main assembly (§9) — the contradiction

**E-9 (Theorem 1.1).** Assume no absolute `C`. Take minimal counterexamples `G_k` with
`Φ(G_k) > n_k²/6 + k·n_k`. Then:
- **(9.2) degree bound:** `∀ v∈I: d(v) > (2n_k−1)/6 + k` (from `Φ(G)≤Φ(G−v)+d(v)`).
- **`q ≥ 2p−1`:** killed by E-5.1 (gives `Φ ≤ n²/6 + p/2`).
- **Bulk `ε≤α≤2−ε`:** killed by E-4.3 (+AX1).
- **`α→0`:** killed by E-8 (+AX2).
- **`α→2`, `q=2p−s`, `s=o(p)`:**
  - `s = O(√p)`: killed by E-5.1 corollary (5.3).
  - `√p ≪ s = o(p)` (`6√p ≤ s ≤ p/8`, `p ≥ 2304`): from (9.2), `3m ≤ s−3` (9.5).
    Dispersion dichotomy on `D = Σ_x a_x(q−a_x)`:
    - **High `D ≥ qs²/12`:** E-6.1 (coeff `≥ (q+2)/4` by (9.5)) + E-5.2 (δ ≥ 7/8 by
      s≤p/8) ⟹ `Φ − n²/6 ≤ p/2 − 5s²/288 − 2s/3 < 0` since `s² ≥ 36p`.
    - **Low `D < qs²/12`:** some `Sⱼ` is a center `R` with `A_R+B_R < s²/6`; verify
      (7.1)–(7.2) (holds with slack 2 by (9.5)); E-7.1 with
      `s²/6 − sρ + 2ρ² = 2(ρ−s/4)² + s²/24 ≥ s²/24` and deviations `≤ 5s/4p·(A_R+B_R)`
      ⟹ `Φ − n²/6 ≤ p/2 − s²/64 < 0`.
- All branches contradict; done.

**Prop-10.1 (effective corridor, Layer E, no axioms).** For `p≥36, 0≤s≤6√p`:
`Φ ≤ n²/6 + 2n`. For `p≥2304, 6√p≤s≤p/8` and `d(v) > (2n−1)/6 + 1` ∀v: `Φ ≤ n²/6`.
This is the machine-verifiable-unconditionally sub-result (only E-5,6,7 + algebra).

---

## Dependency DAG (topological order for Lean)

```
AX1, AX2                                  [axioms]
E-3.1  → E-4.1 → E-4.2 → E-4.3(+AX1)
E-5.1 → E-5.2
E-6.1
E-D.1, E-D.2 → E-D.3 → E-7.1 (+E-5.1 factorization)
E-B → E-8 (+AX2, Dirac, Turán)
E-4.3, E-5.1, E-5.2, E-6.1, E-7.1, E-8  → E-9 (Theorem 1.1)
E-5.1, E-5.2, E-6.1, E-7.1              → Prop-10.1  (no axioms)
E-9 → Corollary 1.2 (cp bound)
```

## What can be verified unconditionally vs axiom-relative

- **Unconditional (no axioms):** E-3.1, E-4.1, E-4.2, E-5.1, E-5.2, E-6.1, E-7.1, E-B,
  E-D.1/2/3, **Prop-10.1**, and all algebraic identities.
- **Axiom-relative (needs AX1 and/or AX2):** E-4.3, E-8, and therefore E-9 (Theorem 1.1).

**Recommended milestone order for the formalization agent:**
1. Algebraic core: E-3.1, E-4.2 (the two audited theorems) + identities.
2. Appendix D chain (E-D.1→E-D.3): fully self-contained, no packing.
3. Corridor lemmas E-5.1, E-5.2, E-6.1, E-7.1 → **Prop-10.1 sorry-free**.
4. Bulk/sparse relative to AX1/AX2 → E-9.
