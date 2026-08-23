/-
# Nibble — axiom gate for the near-complete branch (`Nibble.CoreGapNearComplete`)

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapNearComplete

namespace Nibble.AX1

#check @card_clique2_le_card_edgeFinset
#check @card_lowDeg_mul_le
#check @card_deleted_restrictAway_le
#check @degree_restrictAway_ge
#check @gap_le_of_near_complete
#check @exists_gap_const_lt_ninth
#check @coreGapAt_of_lt_ninth

#print axioms card_clique2_le_card_edgeFinset
#print axioms card_lowDeg_mul_le
#print axioms card_deleted_restrictAway_le
#print axioms degree_restrictAway_ge
#print axioms gap_le_of_near_complete
#print axioms exists_gap_const_lt_ninth
#print axioms coreGapAt_of_lt_ninth

end Nibble.AX1
