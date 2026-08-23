/-
# Nibble — axiom gate for the per-triple half of the AX1 regularity core

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapUniformCodegree
import Nibble.CoreGapTripleDegrees
import Nibble.CoreGapPrune
import Nibble.CoreGapDensePairs
import Nibble.CoreGapSubblock
import Nibble.CoreGapPackingSplit

namespace Nibble.AX1

-- ingredient 1: per-edge counting in a uniform triple
#check @card_filter_lt_le
#check @card_filter_gt_le
#check @codegreeIn
#check @uniform_triple_codegree

-- triangle degrees inside a cluster triple
#check @edgeTriangleDegree_pair
#check @tripleGraph
#check @edgeTriangleDegree_tripleGraph
#check @tripleGraph_near_regular_pair
#check @tripleGraph_near_regular

-- deleting the exceptional edges
#check @prune
#check @deletedDegree
#check @edgeTriangleDegree_prune_ge
#check @sum_deletedDegree_le
#check @card_edges_heavy_deleted_le
#check @prune_near_regular
#check @uniform_triple_member

-- the ν₃* bookkeeping: LP weight per edge set, and the split along cluster triples
#check @sum_fracPacking_over_edges_le
#check @nu3star_le_of_edgeCover
#check @partClass
#check @partClass_card_three_of_isNClique
#check @sum_split_partClass
#check @sum_pair_classes_le

-- uniformity passes to vertex sub-blocks
#check @edgeDensity_sub_lt_of_isUniform
#check @isUniform_subblock

-- decoupling the regularity scale from the density threshold
#check @densePairSubgraph
#check @card_interedges_le_of_edgeDensity_lt
#check @card_sparse_edges_le
#check @hasNearRegularFamily_of_densePairs

#print axioms card_filter_lt_le
#print axioms card_filter_gt_le
#print axioms uniform_triple_codegree
#print axioms edgeTriangleDegree_pair
#print axioms edgeTriangleDegree_tripleGraph
#print axioms tripleGraph_near_regular_pair
#print axioms tripleGraph_near_regular
#print axioms edgeTriangleDegree_prune_ge
#print axioms sum_deletedDegree_le
#print axioms card_edges_heavy_deleted_le
#print axioms prune_near_regular
#print axioms uniform_triple_member
#print axioms card_interedges_le_of_edgeDensity_lt
#print axioms card_sparse_edges_le
#print axioms hasNearRegularFamily_of_densePairs
#print axioms edgeDensity_sub_lt_of_isUniform
#print axioms isUniform_subblock
#print axioms sum_fracPacking_over_edges_le
#print axioms nu3star_le_of_edgeCover
#print axioms partClass_card_three_of_isNClique
#print axioms sum_split_partClass
#print axioms sum_pair_classes_le

end Nibble.AX1
