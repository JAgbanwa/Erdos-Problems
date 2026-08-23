# Block 04 — Corridor integral packing (Lemma 5.1 / E-5.1 & Corollary 5.3)

## What is audited
On systematically generated split graphs `G` (clique `K` of order `p`; `q` independent
vertices with arbitrary neighbourhoods `Nᵢ ⊆ K`) we verify, using the **exact** maximum
edge-disjoint triangle packing number `ν₃(G)`:

- **E-5.1**: if `q ≥ r_p = χ'(K_p)` then `ν₃(G) ≥ (1/q)·Σᵢ C(dᵢ,2)`.
- **Corollary 5.3**: if `q ≥ r_p` then `Φ(G) ≤ n²/6 + p/2 + (s²−6s+3)/12` with `s=2p−q`.
- **Basic invariants**: `0 ≤ Φ(G) = |E| − 2ν₃(G)` and `3ν₃(G) ≤ |E|`.

## Method
`ν₃(G)` is computed **exactly** by a 0/1 integer linear program (PuLP + CBC):

```
maximize  Σ_t x_t   s.t.   Σ_{t ∋ e} x_t ≤ 1  ∀ edge e,   x_t ∈ {0,1}.
```

All bound comparisons then use exact rational arithmetic on the closed forms. The
neighbourhood profiles enumerated per `(p,q)` are: (a) every common profile `N` of each
size, (b) a staircase profile, (c) an alternating full/empty/half profile — a
reproducible, deterministic family (no randomness). This reproduces the paper's
exact-ILP corridor audits.

## Files
- `verify_corridor_ILP.py` — the audit script.
- `results/corridor_ILP_results.txt` — full log.
- `certificate_block04.pdf` — audit certificate (English).

## How to reproduce
```
python verify_corridor_ILP.py     # requires PuLP + CBC
```

## Result
**372/372 instances** pass the basic invariants; **E-5.1 180/180** and
**Corollary 5.3 180/180** on the applicable instances (`q ≥ r_p`).
