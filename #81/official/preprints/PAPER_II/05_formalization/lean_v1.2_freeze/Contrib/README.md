# Contrib — Mathlib contribution candidates (from Paper II)

Extract, rewrite idiomatically, and prepare for upstreaming the *general* graph-theory results
proven in Paper II that Mathlib currently lacks. **These files import ONLY Mathlib** (no `PaperII.*`)
— an upstream PR cannot depend on the paper. The proven Paper II versions are the *reference*; the
work here is the idiomatic Lean/Mathlib rewrite + generalization.

## Modules

Working lane (this folder). The PR-ready copies live in `Contrib/Submission/` (see its README).

### `Contrib/Chordal.lean` → eventual `Mathlib/Combinatorics/SimpleGraph/Chordal.lean`
All in `namespace SimpleGraph`; **proven, sorry-free, imports only Mathlib**.

| Decl | Statement | Axioms |
|---|---|---|
| `IsChordal` (def) | every cycle of length ≥ 4 has a chord | — |
| `IsSimplicial`, `Separates`, `IsMinimalSeparator` (defs) | — | — |
| `IsChordal.comap` | embedding as induced subgraph into chordal ⇒ chordal (heredity) | `[propext, Quot.sound]` |
| `IsChordal.minimalSeparator_isClique` ⭐ | minimal vertex separator ⇒ clique | clean |
| `IsChordal.exists_isSimplicial` ⭐ | **Dirac 1961:** nonempty finite chordal ⇒ simplicial vertex | clean |
| `IsChordal.exists_two_nonadj_isSimplicial` | connected non-complete finite chordal ⇒ two non-adjacent simplicial vertices | clean |

### `Contrib/GeodesicChordless.lean` → separate PR (general, not chordal-specific)
| Decl | Statement | Axioms |
|---|---|---|
| `geodesic_adj_imp_edge` | on a shortest walk, adjacent support vertices are joined by a walk edge | clean |
| `exists_induced_path_of_walk` | a walk inside a set yields an induced (chordless) path inside it | clean |
| `reachable_induce_of_walk` | (helper) a walk staying in `K` lifts to reachability in `G.induce K` | clean |

("clean" = `[propext, Classical.choice, Quot.sound]`.) Reference originals: `PaperII/IsChordal.lean`,
`PaperII/Dirac.lean`, `PaperII/Dirac1.lean`.

## Workflow (per decl)

1. Port the *statement* in Mathlib style (namespace, `variable`, docstring, naming conventions).
2. Rewrite the proof idiomatically — the Paper II proofs are Aristotle-generated (`grind`/`aesop`/
   `simp +decide`); acceptable/correct but NOT PR-style. Golf + use existing Mathlib API.
3. Generalize: drop `[Fintype V] [DecidableEq V]` where the result holds without them (heredity: yes;
   Dirac: needs finiteness). State the most general true form.
4. `lake build Contrib` must pass, sorry-free, axioms `[propext, Classical.choice, Quot.sound]`.

## Before opening a PR (step 0)

- Check the Mathlib Zulip / open PRs for existing chordal-graph work (avoid duplication; align
  naming). There has been community interest — confirm nothing is already in flight.
- Follow the Mathlib contribution guide (naming, `theorem`/`lemma` conventions, docstrings, `#align`
  not needed in Lean4-only, module docstring, copyright header).

## Status

Working lane **complete and proven** (`lake build Contrib.Chordal Contrib.GeodesicChordless` green,
sorry-free, axiom-clean). The proofs are Aristotle-ported (`grind`/`aesop`/`simp` — valid Mathlib
tactics; some linter warnings remain). The PR-ready polish (linter-clean, docstrings, generalization)
happens in `Contrib/Submission/`, not here.
