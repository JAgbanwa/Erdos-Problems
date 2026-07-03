The [Lean formalization](https://github.com/JAgbanwa/Erdos-Problems/blob/main/%2381/Lean%20formalisation%20of%20theorems) of this [paper](https://zenodo.org/records/20736085) was formalized by Wouter van Doorn.

## Announced resolution milestone

In June 2026, Juan Pablo Traverso Gianini announced an asymptotic resolution of the Erdős--Ordman--Zalcstein chordal clique partition problem:

```text
max{cp(G): G chordal, |V(G)| = n} = (1/6 + o(1)) n^2.
```

The announced lower-bound construction is the complete split graph

```text
K_p join overline{K}_{2p}, where n = 3p.
```

The announced proof proceeds through a fractional triangle-packing theorem for chordal graphs,

```text
|E(G)| - 2 nu_3^*(G) <= (1/6 + o(1)) n^2,
```

followed by fractional-to-integral rounding for the fixed family `{K_3}`.

The current public release package is available in [`announced_resolution/`](announced_resolution/). It mirrors the public release repository and includes:

- the final research announcement in Markdown, LaTeX, and PDF;
- the three-paper public release package under `public_release/`;
- manuscript sources, PDFs, public audit records, reproducibility scripts, and outputs;
- SHA-256 hashes and citation/license metadata;
- the encrypted complete author package as a timestamped integrity record.

Status: announced resolved; pending peer review and independent verification.
