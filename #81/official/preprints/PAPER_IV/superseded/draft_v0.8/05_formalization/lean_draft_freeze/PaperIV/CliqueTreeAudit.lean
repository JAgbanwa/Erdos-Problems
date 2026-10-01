/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PaperIV.CliqueTree

/-!
# Axiom audit for the clique-tree library

Compiling this module prints the transitive axiom dependencies of every public result of the
`CliqueTree` library.  Each of them must use only the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms SimpleGraph.IsChordal.exists_isPEO
#print axioms SimpleGraph.IsChordal.nonempty_cliqueTree
#print axioms SimpleGraph.IsPEO.cliqueTree
#print axioms SimpleGraph.IsPEO.peoBag_isClique
#print axioms SimpleGraph.IsPEO.exists_peoBag_of_adj
#print axioms SimpleGraph.IsPEO.card_edgeFinset_eq_sum_card_laterNbrs
#print axioms SimpleGraph.IsPEO.card_edgeFinset_add_card_eq_sum_card_peoBag
#print axioms SimpleGraph.CliqueTree.isAncestor_top_of_mem_bag
#print axioms SimpleGraph.CliqueTree.mem_bag_of_isAncestor
#print axioms SimpleGraph.CliqueTree.branch_separator
#print axioms SimpleGraph.CliqueTree.not_adj_of_branch_separator
#print axioms SimpleGraph.CliqueTree.exists_isLeaf
#print axioms SimpleGraph.CliqueTree.isSimplicial_of_mem_privateVerts
#print axioms SimpleGraph.CliqueTree.exists_bag_ne_of_isLeaf
#print axioms SimpleGraph.CliqueTree.existsUnique_edgeBag
#print axioms SimpleGraph.CliqueTree.mem_bag_edgeBag
#print axioms SimpleGraph.CliqueTree.card_edgeFinset_eq_sum_fiber
#print axioms SimpleGraph.CliqueTree.subset_bag_of_mem_fiber
#print axioms SimpleGraph.exists_isMaximalCliqueOn
#print axioms SimpleGraph.exists_maxCliqueForest
#print axioms SimpleGraph.IsChordal.exists_maximalCliqueTree
#print axioms SimpleGraph.IsPEO.exists_eq_peoBag_of_isMaximalCliqueOn

/-! ### Helly property and the clique number -/

#print axioms SimpleGraph.CliqueTree.top_comparable_of_mem_bag
#print axioms SimpleGraph.CliqueTree.isAncestor_top_of_rank_le
#print axioms SimpleGraph.CliqueTree.mem_bag_top_of_rank_le
#print axioms SimpleGraph.CliqueTree.exists_subset_bag
#print axioms SimpleGraph.CliqueTree.exists_subset_bag'
#print axioms SimpleGraph.CliqueTree.exists_subset_bag_set
#print axioms SimpleGraph.CliqueTree.cliqueNum_eq_sup_card_bag
#print axioms SimpleGraph.CliqueTree.exists_isMaximumClique_bag
#print axioms SimpleGraph.IsPEO.cliqueNum_eq_sup_card_peoBag

/-! ### Maximal cliques: bridge to Mathlib and counting -/

#print axioms SimpleGraph.isMaximalCliqueOn_univ_iff
#print axioms SimpleGraph.MaxCliqueForest.exists_top_eq
#print axioms SimpleGraph.MaxCliqueForest.bag_nonempty
#print axioms SimpleGraph.MaxCliqueForest.size_le_card
#print axioms SimpleGraph.MaxCliqueForest.size_le
#print axioms SimpleGraph.CliqueTree.exists_top_eq
#print axioms SimpleGraph.CliqueTree.card_le_card_of_isMaximalCliqueOn
#print axioms SimpleGraph.IsChordal.exists_maximalCliqueTree_card_le
#print axioms SimpleGraph.IsChordal.card_maximalCliques_le

/-! ### Characterisations of chordality -/

#print axioms SimpleGraph.IsChordal.of_nonempty_cliqueTree
#print axioms SimpleGraph.isChordal_iff_nonempty_cliqueTree
#print axioms SimpleGraph.IsPEO.isChordal
#print axioms SimpleGraph.isChordal_iff_exists_isPEO

/-! ### Minimal separators -/

#print axioms SimpleGraph.CliqueTree.separates_bag_inter
#print axioms SimpleGraph.CliqueTree.isMinimalSeparator_bag_inter
#print axioms SimpleGraph.CliqueTree.exists_parent_eq_of_isMinimalSeparator
#print axioms SimpleGraph.CliqueTree.not_exists_isMinimalSeparator_dupBagTree
#print axioms SimpleGraph.CliqueTree.not_exists_parent_eq_isolatedTree

/-! ### The bag-counting identity -/

#print axioms SimpleGraph.CliqueTree.mem_parentSep_iff
#print axioms SimpleGraph.CliqueTree.card_parentSep
#print axioms SimpleGraph.CliqueTree.card_eq_sum_card_bag_sub_sum_card_inter
#print axioms SimpleGraph.CliqueTree.card_add_sum_card_parentSep
