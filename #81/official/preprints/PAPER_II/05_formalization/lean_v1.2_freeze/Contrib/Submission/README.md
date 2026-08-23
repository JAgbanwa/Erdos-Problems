# Contrib/Submission — Mathlib submission lane

**Purpose.** PR-ready versions of the graph-theory results extracted from Paper II (Erdős #81) for
upstreaming to Mathlib. Everything here imports **only Mathlib** (no `PaperII.*`) and is meant to drop
into the Mathlib source tree. The working lane (`Contrib/*.lean`, one level up) is where things are
made to compile first; this lane is the polished copy. **Nothing here edits the working lane.**

> This README describes the current contents of the folder and is kept up to date as files change.

## Contents

| File | Maps to (in Mathlib) | Description |
|---|---|---|
| `Chordal.lean` | `Mathlib/Combinatorics/SimpleGraph/Chordal.lean` | Chordal graphs: definition + Dirac-family results. |
| `GeodesicChordless.lean` | `Mathlib/Combinatorics/SimpleGraph/…` (separate PR) | General "shortest walks are chordless" lemmas (not chordal-specific). |
| `README.md` | — | This file. |

## `Chordal.lean` — public API (`namespace SimpleGraph`)

Definitions:
- `IsChordal G` — every cycle of length `≥ 4` has a chord (standard definition).
- `IsSimplicial G v` — the neighbourhood of `v` induces a clique.
- `Separates G S a b`, `IsMinimalSeparator G S a b` — vertex separators and minimality.

Results:
- `IsChordal.comap` — a graph embedding as an induced subgraph into a chordal graph is chordal
  (heredity). No finiteness assumptions.
- `IsChordal.minimalSeparator_isClique` — in a chordal graph, every minimal vertex separator is a
  clique. `[Fintype V] [DecidableEq V]`.
- `IsChordal.exists_isSimplicial` — **Dirac (1961):** a nonempty finite chordal graph has a
  simplicial vertex. `[Fintype V] [DecidableEq V] [Nonempty V]`.
- `IsChordal.exists_two_nonadj_isSimplicial` — a connected non-complete finite chordal graph has two
  non-adjacent simplicial vertices. `[Fintype V] [DecidableEq V]`.

All other declarations in the file are `private` helper lemmas.

## `GeodesicChordless.lean` — public API (`namespace SimpleGraph`)

- `geodesic_adj_imp_edge` — on a shortest walk, two adjacent support vertices are joined by an edge
  of the walk.
- `exists_induced_path_of_walk` — a walk staying inside a set `K` yields an induced (chordless) path
  inside `K`.
- `reachable_induce_of_walk` — a walk staying in `K` lifts to reachability in `G.induce K`.

General graph-theory lemmas (no chordality); intended as a **separate** Mathlib PR.

## Status

| Check | State |
|---|---|
| Builds (`lake build Contrib.Submission.Chordal`) | ✅ green |
| Sorry-free | ✅ |
| Self-contained (imports only Mathlib) | ✅ |
| `#print axioms` | ✅ `[propext, Classical.choice, Quot.sound]` |
| Apache header + author + docstrings | ✅ |
| Linter warnings | ✅ **0** (both modules) |

**Status: PR-READY.** `lake build Contrib.Submission.Chordal Contrib.Submission.GeodesicChordless`
→ green, 0 warnings, 0 errors, sorry-free, axiom-clean. Only the human steps below remain.

## Pre-PR checklist (remaining — human steps only)

1. **Human steps (cannot be automated here):**
   - Open a topic in the Mathlib Zulip (graph-theory area) to coordinate placement/naming and check
     for in-flight work.
   - Fork Mathlib, drop the file(s) at the mapped paths, open the PR.

## Notes

- `aesop` / `grind` / `simp` are standard Mathlib tactics and are fine; the linter items above are the
  only cleanliness gap.
- Author (copyright/`Authors:` header): **Juan Pablo Traverso** (confirmed).
