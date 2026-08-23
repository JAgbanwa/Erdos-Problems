/-
# Nibble — axiom gate for the deterministic block-allocation route to AX1

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapBlockCover
import Nibble.GridTripleDesign
import Nibble.GridTripleDesignRect

namespace Nibble.AX1

-- the local design form of the residual and its reductions
#check @SubTripleDesignLocalAt
#check @SubTripleDesignLocalResidual
#check @reducedFamilyAt_of_subTripleDesignLocalAt
#check @reducedFamilyResidual_of_subTripleDesignLocal
#check @ax1_of_subTripleDesignLocal

#print axioms reducedFamilyAt_of_subTripleDesignLocalAt
#print axioms reducedFamilyResidual_of_subTripleDesignLocal
#print axioms ax1_of_subTripleDesignLocal

-- the blocks of a good cluster triple, their rectangles and their edge counts
#check @IsGridSubTriple
#check @gridSubTriple_data
#check @subTripleShape_of_gridSubTriples
#check @tripleRect
#check @tripleGraph_edgeDisjoint_of_rect_disjoint
#check @sum_area_le_of_rect_disjoint
#check @three_edgeDensity_mul_le_tripleGraph_edges

#print axioms gridSubTriple_data
#print axioms subTripleShape_of_gridSubTriples
#print axioms tripleGraph_edgeDisjoint_of_rect_disjoint
#print axioms sum_area_le_of_rect_disjoint
#print axioms three_edgeDensity_mul_le_tripleGraph_edges

-- the line design (allocation of diagonals between cluster triples)
#check @lineTriple
#check @diagIndex_bijective
#check @lineTriple_UW_unique
#check @lineTriple_UX_unique
#check @lineTriple_WX_unique
#check @lineTriple_pair_disjoint

#print axioms diagIndex_bijective
#print axioms lineTriple_UW_unique
#print axioms lineTriple_UX_unique
#print axioms lineTriple_WX_unique
#print axioms lineTriple_pair_disjoint

-- the global (multi-triple) design: a simultaneously consistent choice of diagonals
#check @triShift
#check @triBlock
#check @triShift_diff
#check @triBlock_bijective
#check @triBlock_eq_lineTriple
#check @triPairSet
#check @card_triPairSet
#check @triPairSet_disjoint
#check @triPairSet_disjoint_of_third
#check @card_triPairSet_biUnion

#print axioms triShift_diff
#print axioms triBlock_bijective
#print axioms triBlock_eq_lineTriple
#print axioms card_triPairSet
#print axioms triPairSet_disjoint
#print axioms triPairSet_disjoint_of_third
#print axioms card_triPairSet_biUnion

-- the design at the level of vertices: the rectangles of the family are pairwise disjoint
#check @triCells
#check @triCells_inter_subsingleton
#check @tripleRect_disjoint_of_design

#print axioms triCells_inter_subsingleton
#print axioms tripleRect_disjoint_of_design

-- the capacity constraint of a cluster pair
#check @sum_fracPacking_cluster_pair_le
#check @nu3star_le_of_clusterPairCover

#print axioms sum_fracPacking_cluster_pair_le
#print axioms nu3star_le_of_clusterPairCover

-- the residual itself and the closure of AX1 from it
#check @BlockCoverResidual
#check @subTripleDesignLocalResidual_of_blockCover
#check @ax1_of_blockCover

#print axioms subTripleDesignLocalResidual_of_blockCover
#print axioms ax1_of_blockCover

end Nibble.AX1
