/-
# Nibble — axiom gate for the weighted nibble file (`Nibble.WeightedNibble`)

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.WeightedNibble

namespace Nibble

-- the packing/cover arithmetic
#check @exists_maximum_packing
#check @exists_mem_of_maximum_packing
#check @nu3star_le_three_nu3
#check @edge_card_le_half_card_sq
#check @nu3star_sub_nu3_le_ninth
#check @triangleHypergraphE_degree_le_card
#check @nu3star_nonneg

-- the newly proved sub-range of the AX1 residual
#check @AX1.coreGapAt_of_ninth

-- the reusable weighted (fractional) nibble, its proved near-regular instance, and the reductions
#check @FracNibbleTheorem
#check @fracMatching_sum_le
#check @fracNibble_nearlyRegular
#check @AX1.haxellRodlGap_of_fracNibble
#check @AX1.coreGapResidual_of_fracNibble

#print axioms exists_maximum_packing
#print axioms exists_mem_of_maximum_packing
#print axioms nu3star_le_three_nu3
#print axioms edge_card_le_half_card_sq
#print axioms nu3star_sub_nu3_le_ninth
#print axioms triangleHypergraphE_degree_le_card
#print axioms nu3star_nonneg
#print axioms AX1.coreGapAt_of_ninth
#print axioms fracMatching_sum_le
#print axioms fracNibble_nearlyRegular
#print axioms AX1.haxellRodlGap_of_fracNibble
#print axioms AX1.coreGapResidual_of_fracNibble

end Nibble
