/-
# Nibble — axiom gate for the family/covering form of the AX1 structural residual

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapRegularFamily
import Nibble.CoreGapRegularCover

namespace Nibble.AX1

-- families and the colouring they induce
#check @EdgeDisjointFamily
#check @familyColoring
#check @colorPart_familyColoring
#check @HasNearRegularFamily

-- the structural moves
#check @HasNearRegularFamily.mono_eps
#check @HasNearRegularFamily.mono_of_le
#check @hasNearRegularFamily_of_few_triangles
#check @hasNearRegularFamily_of_reduced

-- the reductions of `RegularDecompResidual`
#check @regularDecompAt_of_family
#check @hasNearRegularFamily_of_regularDecomp
#check @ReducedFamilyAt
#check @ReducedFamilyResidual
#check @regularDecompResidual_of_reducedFamily
#check @reducedFamilyResidual_of_regularDecompResidual
#check @ax1_of_reducedFamily

-- the covering criterion: the residual with no `ν₃*` in its hypotheses
#check @triangleSupport
#check @GoodTriple
#check @regularityReduced_triangle_parts
#check @triangleSupport_regularityReduced_goodTriple
#check @nu3star_triangleSupport
#check @unionFamily
#check @card_cliqueFinset_two_unionFamily
#check @hasNearRegularFamily_of_cover

#print axioms colorPart_familyColoring
#print axioms HasNearRegularFamily.mono_of_le
#print axioms hasNearRegularFamily_of_few_triangles
#print axioms hasNearRegularFamily_of_reduced
#print axioms regularDecompAt_of_family
#print axioms hasNearRegularFamily_of_regularDecomp
#print axioms regularDecompResidual_of_reducedFamily
#print axioms reducedFamilyResidual_of_regularDecompResidual
#print axioms ax1_of_reducedFamily
#print axioms regularityReduced_triangle_parts
#print axioms triangleSupport_regularityReduced_goodTriple
#print axioms nu3star_triangleSupport
#print axioms card_cliqueFinset_two_unionFamily
#print axioms hasNearRegularFamily_of_cover

end Nibble.AX1
