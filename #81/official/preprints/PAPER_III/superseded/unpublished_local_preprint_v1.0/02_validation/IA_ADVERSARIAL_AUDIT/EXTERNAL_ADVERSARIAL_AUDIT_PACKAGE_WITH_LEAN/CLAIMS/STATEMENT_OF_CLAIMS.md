# Statement of Claims — what to audit (adversarially)

Notation (paper §0): split graph `G = (K ⊔ I, E)`, clique `|K|=p`, independent `|I|=q`,
`n=p+q`; for `vᵢ∈I`: `Nᵢ=N(vᵢ)∩K`, `dᵢ=|Nᵢ|`, `Sᵢ=K∖Nᵢ`, `mᵢ=|Sᵢ|`; `M=Σmᵢ`,
`S₂=Σmᵢ²`, `m=maxᵢmᵢ`; near `q=2p`: `s=2p−q`; `α=q/p`; `ν₃` = max edge-disjoint triangles,
`ν₃*` = fractional optimum; `Φ(G)=|E|−2ν₃(G)`; `r_p=χ'(K_p)`;
`T(G)=½(|E|−(p+q)²/6)`.

The authoritative, exact statements are in `LEDGER.md`. This file is the enumerated
attack list. **Only AX1 and AX2 are external inputs; everything else must be
self-contained.**

## External inputs (verify faithfulness to literature; do NOT prove)
- **AX1 (Thm 2.1, Haxell–Rödl / Yuster).** Uniformly over graphs, `ν₃*(G)−ν₃(G)=o(|V|²)`.
  Used only in the bulk regime (§4.3/§9.1).
- **AX2 (Thm 2.3, Dross + Barber–Kühn–Lo–Osthus).** Triangle-divisible graphs with
  `δ(H) ≥ (0.9+ε)|V(H)|` and `|V|` large have an exact triangle decomposition. Used only
  in the sparse regime (§8).

## Main claims (relative to AX1, AX2 where noted)
- **C-1 · Theorem 1.1 (E-9).** `∃ C, ∀` split `G`: `Φ(G) ≤ n²/6 + C·n`. (Uses AX1, AX2.)
- **C-2 · Corollary 1.2.** `∃ C, ∀` split `G`: `cp(G) ≤ n²/6 + C·n`, from `cp(G) ≤ Φ(G)`.
- **C-3 · Proposition 10.1 (unconditional).**
  (i) `p≥36, 0≤s≤6√p` ⟹ `Φ ≤ n²/6 + 2n`;
  (ii) `p≥2304, 6√p≤s≤p/8` and `d(v)>(2n−1)/6+1 ∀v` ⟹ `Φ ≤ n²/6`. (No external input.)

## Finite / closed-form claims (unconditional; directly falsifiable)
- **C-4 · Theorem 3.1 (E-3.1).** For `p≥3`, common-profile `H(p,q,d)`, `r=p−d`:
  `ν₃*(H(p,q,d)) = F(p,q,d) = min{ (C(p,2)+qd)/3 , C(d,2)+C(r,2) , C(d,2)+(dr+C(r,2))/3 }`.
- **C-5 · Lemma 4.1 (E-4.1).** `q≥1` ⟹ `ν₃*(G) ≥ (1/q) Σᵢ F(p,q,dᵢ)`.
- **C-6 · Theorem 4.2 (E-4.2).** `0<q≤2p` ⟹ `ν₃*(G) ≥ T(G)+μ(α)p²−p/4`, where
  `μ(α)=α²/12` on `[0,2/3]`, `(2−α)²/48` on `[2/3,2]`. Core step (4.5):
  `F(p,q,d) ≥ qd/2 + (C_α+μ(α))p² − p/2`, `C_α=(2−2α−α²)/12`.
- **C-7 · Lemma 5.1 (E-5.1).** `q≥r_p` ⟹ `ν₃(G) ≥ (1/q) Σᵢ C(dᵢ,2)`.
  Corollary 5.3: `Φ(G) ≤ n²/6 + p/2 + (s²−6s+3)/12`.
- **C-8 · Lemma 5.2 (E-5.2).** `q≥r_p` ⟹
  `Φ(G) ≤ n²/6 + p/2 − s²/6 + ((s−1)M−S₂)/q − 2δV/(q(q−1))`, `V=Σ_e b_e(q−b_e)`,
  `δ=min{r_p,q−r_p}/r_p`.
- **C-9 · Lemma 6.1 (E-6.1).** `2p−3m−1≥0` ⟹ `V ≥ ((2p−3m−1)/4) Σ_{i,j}|Sᵢ△Sⱼ|`.
- **C-10 · Lemma 7.1 (E-7.1).** Reserved-gain shifted-center inequality (see LEDGER for
  the full statement and hypotheses (7.1)–(7.2)); the list-coloring input is proved in
  Appendix D (no external citation).
- **C-11 · Appendix B (E-B).** Path parity correction: `Odd(J)=O`, `|E(J)|≤p−1`, `Δ(J)≤2`.
- **C-12 · Appendix D (E-D.1/2/3).** Self-contained list edge coloring (kernel lemma;
  Gale–Shapley; König; Galvin max-degree case). **This removes the only remaining
  external coloring citation** — verify that claim.
- **C-13 · Sharpness (§10.2).** `K_p ∨ K̄_{2p}` has `|E|−2ν₃ = n²/6 + n/6`; the leading
  `1/6` is optimal.

## Addenda (v0.9.1, downstream corollaries — no core dependency)
- **C-14 · Corollary 10.4** = C-4 restated (exact `ν₃*` closed form).
- **C-15 · Corollary 10.4b** = C-1 specialized to threshold graphs (`threshold ⊆ split`).
- **C-16 · Corollary 12.2** = effective-corridor algorithmic packaging of C-3.

## What a refutation looks like
Any of: a split graph violating C-1/C-3/C-7/C-8/etc.; a `(p,q,d)` with `ν₃*≠F` (C-4) or
breaking the margin (C-6); AX1/AX2 stated more strongly than the cited literature; a
load-bearing dependency on an uncited/uncredited external theorem; a proof step that does
not follow; or the extremal family not attaining the claimed value (C-13).
