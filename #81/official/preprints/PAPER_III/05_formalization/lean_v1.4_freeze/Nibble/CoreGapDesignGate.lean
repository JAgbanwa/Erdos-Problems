/-
# Nibble — axiom gate for the sub-triple design route

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapDesign
import Nibble.GridDesign
import Nibble.CoreGapGridResidual
import Nibble.CoreGapTripleShape
import Nibble.TripleEdges

namespace Nibble.AX1

-- the design and the bridge
#check @designBad
#check @IsSubTripleDesign
#check @hasNearRegularFamily_of_subTripleDesign
#check @hasNearRegularFamily_of_isSubTripleDesign

-- the diagonal grid inside one cluster triple
#check @gridIdx_AB_inj
#check @gridIdx_AC_inj
#check @gridIdx_BC_inj
#check @gridDesign_pairwise_edgeDisjoint

-- the residual in design form and its reductions
#check @SubTripleDesignAt
#check @SubTripleDesignResidual
#check @reducedFamilyAt_of_subTripleDesignAt
#check @reducedFamilyResidual_of_subTripleDesign
#check @ax1_of_subTripleDesign

#print axioms hasNearRegularFamily_of_subTripleDesign
#print axioms hasNearRegularFamily_of_isSubTripleDesign
#print axioms gridIdx_AB_inj
#print axioms gridIdx_AC_inj
#print axioms gridIdx_BC_inj
#print axioms gridDesign_pairwise_edgeDisjoint
#print axioms reducedFamilyAt_of_subTripleDesignAt
#print axioms reducedFamilyResidual_of_subTripleDesign
#print axioms ax1_of_subTripleDesign

-- the rectangular grid, the scale window and the shape of one cluster triple
#check @tripleFamily_pairwise_edgeDisjoint
#check @rectDesign_pairwise_edgeDisjoint
#check @scale_window
#check @IsSubTripleShape
#check @isSubTripleDesign_of_shape
#check @subTripleShape_grid
#check @interedges_card_le_tripleGraph_edges
#check @edgeDensity_mul_le_tripleGraph_edges

#print axioms tripleFamily_pairwise_edgeDisjoint
#print axioms rectDesign_pairwise_edgeDisjoint
#print axioms scale_window
#print axioms isSubTripleDesign_of_shape
#print axioms subTripleShape_grid
#print axioms interedges_card_le_tripleGraph_edges
#print axioms edgeDensity_mul_le_tripleGraph_edges

end Nibble.AX1
