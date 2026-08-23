/-
# Nibble — axiom gate for the AX1 core-gap reduction (`Nibble.CoreGapAX1`)

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapAX1
import Nibble.CoreGapOpenRange

namespace Nibble.AX1

-- the packing-number stability lemmas
#check @nu3_mono
#check @nu3star_le_add_deleted
#check @gap_le_core_gap

-- the low-degree core
#check @exists_core

-- the dense branch, tolerating isolated vertices
#check @nibbleGap_denseCore
#check @nibbleGap_of_dense_core

-- the residual, its proved instances, and the reductions
#check @CoreGapAt
#check @CoreGapResidual
#check @coreGapAt_of_third
#check @coreGapAt_dense
#check @nibbleGapResidual_of_coreGapResidual
#check @nibbleGapHyp_of_coreGapResidual
#check @ax1_of_coreGapResidual
#check @coreGapResidual_of_haxellRodl
#check @coreGapResidual_of_nibbleGapResidual

#print axioms nu3_mono
#print axioms nu3star_le_add_deleted
#print axioms gap_le_core_gap
#print axioms exists_core
#print axioms nibbleGap_denseCore
#print axioms nibbleGap_of_dense_core
#print axioms coreGapAt_of_third
#print axioms coreGapAt_dense
#print axioms CoreGapAt.mono_delta
#print axioms CoreGapAt.mono_eps
#print axioms nibbleGapResidual_of_coreGapResidual
#print axioms nibbleGapHyp_of_coreGapResidual
#print axioms ax1_of_coreGapResidual
#print axioms coreGapResidual_of_haxellRodl
#print axioms coreGapResidual_of_nibbleGapResidual

-- the open range of the residual is non-vacuous
#check @exists_openRange_graph
#print axioms exists_openRange_graph

end Nibble.AX1
