/-
# Nibble — axiom gate for the near-regular branch (`Nibble.CoreGapRegularDegrees`)

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapRegularDegrees

namespace Nibble.AX1

#check @edgeTriangleDegree
#check @edgeTriangleDegree_eq
#check @gap_le_of_regular_triangle_degrees
#check @gap_le_of_regular_triangle_degrees'
#check @gap_le_of_regular_triangle_degrees_core
#check @gap_le_of_small_triangle_degrees
#check @gap_le_of_few_heavy_edges

#print axioms edgeTriangleDegree_eq
#print axioms gap_le_of_regular_triangle_degrees
#print axioms gap_le_of_regular_triangle_degrees'
#print axioms gap_le_of_regular_triangle_degrees_core
#print axioms gap_le_of_small_triangle_degrees
#print axioms gap_le_of_few_heavy_edges

end Nibble.AX1
