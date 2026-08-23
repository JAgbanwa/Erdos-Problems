/-
# Nibble — axiom gate for the structural reduction (`Nibble.CoreGapRegularDecomp`)

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapRegularDecomp

namespace Nibble.AX1

#check @edgeSelect
#check @colorPart
#check @nu3_sum_colorParts_le
#check @nu3_ge_of_regular_triangle_degrees
#check @RegularDecompAt
#check @RegularDecompResidual
#check @coreGapResidual_of_regularDecomp
#check @ax1_of_regularDecomp

#print axioms nu3_sum_colorParts_le
#print axioms nu3_ge_of_regular_triangle_degrees
#print axioms coreGapResidual_of_regularDecomp
#check @colorPart_const
#check @regularDecomp_witness_of_regular

#print axioms ax1_of_regularDecomp
#print axioms regularDecomp_witness_of_regular

end Nibble.AX1
