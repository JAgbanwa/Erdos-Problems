/-
# Nibble — axiom gate for the removal branch of the AX1 core gap (`Nibble.CoreGapRemoval`)

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapRemoval

namespace Nibble.AX1

#check @card_clique2_sdiff_le
#check @nu3star_eq_zero_of_cliqueFree
#check @nu3star_le_of_few_triangles
#check @gap_le_of_few_triangles
#check @CoreGapAtRich
#check @CoreGapRichResidual
#check @coreGapResidual_of_rich
#check @rich_of_coreGapResidual
#check @ax1_of_coreGapRichResidual

#print axioms card_clique2_sdiff_le
#print axioms nu3star_eq_zero_of_cliqueFree
#print axioms nu3star_le_of_few_triangles
#print axioms gap_le_of_few_triangles
#print axioms CoreGapAtRich.mono_kappa
#print axioms coreGapResidual_of_rich
#print axioms rich_of_coreGapResidual
#print axioms ax1_of_coreGapRichResidual

end Nibble.AX1
