/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PaperIV.CliqueTree.Basic
import PaperIV.CliqueTree.PEO
import PaperIV.CliqueTree.Maximal
import PaperIV.CliqueTree.Helly
import PaperIV.CliqueTree.MaximalBridge
import PaperIV.CliqueTree.Characterization
import PaperIV.CliqueTree.Separator
import PaperIV.CliqueTree.Counting

/-!
# Clique trees of finite chordal graphs

This library extends the chordal-graph development of `Chordal.lean` (chordality, simplicial
vertices, minimal separators and Dirac's theorem) with a reusable, Mathlib-style theory of
**clique trees**.

* `CliqueTree/Basic.lean` — the structure `SimpleGraph.CliqueTree` (a rooted clique forest: clique
  bags, a parent map with strictly decreasing rank, a top node per vertex, edge covering and the
  local running-intersection condition) together with its API: ancestor calculus, the intersection
  property, branch separation, leaf elimination, simpliciality of private vertices, the unique bag
  assigned to each edge and the resulting edge accounting.
* `CliqueTree/PEO.lean` — perfect elimination orders, their existence for finite chordal graphs,
  and the clique-bag decomposition `{v} ∪ N⁺(v)` they induce: a clique tree whose bags are *not*
  required to be maximal, with the exact edge count `e(G) = ∑ v, |N⁺(v)|`.
* `CliqueTree/Maximal.lean` — removal of the redundant bags: a clique tree whose bags are exactly
  the maximal cliques of the graph, each occurring once, built by simplicial elimination; and the
  fact that every maximal clique already occurs as a PEO bag.
* `CliqueTree/Helly.lean` — the Helly property of the bags (every clique lies in one bag) and its
  consequence: the clique number is the size of the largest bag, and some bag is a maximum clique.
* `CliqueTree/MaximalBridge.lean` — the bridge between the relative notion `IsMaximalCliqueOn` and
  Mathlib's `Maximal G.IsClique`, and the classical bound of `Fintype.card V` on the number of
  maximal cliques of a chordal graph.
* `CliqueTree/Characterization.lean` — the converse constructions: a graph carrying a clique tree,
  or a perfect elimination order, is chordal; hence both are characterisations of chordality.
* `CliqueTree/Separator.lean` — the minimal separators of the graph are exactly the intersections
  `bag i ∩ bag j` along the tree edges of a clique tree of maximal cliques, together with the two
  counterexamples showing that the hypotheses are needed.
* `CliqueTree/Counting.lean` — the bag-counting identity
  `∑ i, |bag i| − ∑ (tree edges), |bag i ∩ bag j| = |V|`.
-/
