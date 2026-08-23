/-
# Nibble — axiom gate for the refutation and the repaired weighted nibble

Every declaration listed here must print exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.FracNibbleRepaired
import Nibble.GreedyFracMatching
import Nibble.FracNibbleMultiScale
import Nibble.K4Obstruction

namespace Nibble

-- the refutation of the target statement `Nibble.FracNibbleTheorem`
#check @FracNibbleAt
#check @fracNibbleTheorem_iff
#check @FracRefutation.completeK
#check @FracRefutation.card_completeK
#check @FracRefutation.isUniform_completeK
#check @FracRefutation.degree_completeK_le
#check @FracRefutation.codegree_completeK_le
#check @FracRefutation.not_disjoint_completeK
#check @FracRefutation.card_le_one_of_isMatching
#check @FracRefutation.unifWeight_vertex_le
#check @FracRefutation.unifWeight_total
#check @not_fracNibbleAt
#check @not_fracNibbleTheorem
#check @not_fracNibbleAt_three

-- Beck–Fiala rounding with codegree control
#check @BeckFiala.pairClosure
#check @BeckFiala.card_pairClosure_le
#check @BeckFiala.exists_rounding_pairs

-- the proved weighted nibble
#check @fracNibble_spread_weightedCodegree
#check @weight_le_weightedCodegree
#check @fracNibble_weightedCodegree
#check @fracNibble_spread_codegree
#check @fracNibble_weightedCodegree_on
#check @fracNibble_weightedCodegree_on_scaled

-- the unconditional greedy bound
#check @exists_matching_sum_le_mul
#check @fracNibbleAt_of_one_sub_inv_le

-- the padded and multi-scale weighted nibble
#check @fracNibble_weightedCodegree_pad
#check @sum_load_region
#check @defic_eq
#check @exists_matching_of_load_le
#check @weight_le_of_codegree
#check @fracNibble_weightedCodegree_dense
#check @fracNibble_weightedCodegree_heavy

-- the repaired obligation, the residual and its non-vacuity certificate
#check @FracNibbleWeightedTheorem
#check @fracNibbleWeighted_nearPerfect
#check @FracNibbleWeightedHeavyEdge
#check @FracNibbleWeightedMixed
#check @fracNibbleWeightedMixed_of_heavyEdge
#check @fracNibbleWeightedTheorem_of_mixed
#check @fracNibbleWeightedTheorem_of_heavyEdge
#check @FracRefutation.half_le_weightedCodegree_completeK

-- the `K₄` obstruction to a spread near-optimal fractional triangle packing
#check @K4.k4Tri_uniform
#check @K4.halfWeight_load
#check @K4.halfWeight_sum
#check @K4.k4_matching_card_le_one
#check @K4.k4_spread_sum_le
#check @K4.k4_no_spread_near_optimal

#print axioms FracRefutation.card_completeK
#print axioms FracRefutation.isUniform_completeK
#print axioms FracRefutation.degree_completeK_le
#print axioms FracRefutation.codegree_completeK_le
#print axioms FracRefutation.not_disjoint_completeK
#print axioms FracRefutation.card_le_one_of_isMatching
#print axioms FracRefutation.unifWeight_vertex_le
#print axioms FracRefutation.unifWeight_total
#print axioms fracNibbleTheorem_iff
#print axioms not_fracNibbleAt
#print axioms not_fracNibbleTheorem
#print axioms not_fracNibbleAt_three
#print axioms BeckFiala.card_pairClosure_le
#print axioms BeckFiala.exists_rounding_pairs
#print axioms fracNibble_spread_weightedCodegree
#print axioms weight_le_weightedCodegree
#print axioms fracNibble_weightedCodegree
#print axioms fracNibble_spread_codegree
#print axioms fracNibble_weightedCodegree_on
#print axioms fracNibble_weightedCodegree_on_scaled
#print axioms fracNibbleWeighted_nearPerfect
#print axioms fracNibble_weightedCodegree_pad
#print axioms sum_load_region
#print axioms defic_eq
#print axioms exists_matching_of_load_le
#print axioms weight_le_of_codegree
#print axioms fracNibble_weightedCodegree_dense
#print axioms fracNibble_weightedCodegree_heavy
#print axioms fracNibbleWeightedMixed_of_heavyEdge
#print axioms fracNibbleWeightedTheorem_of_mixed
#print axioms fracNibbleWeightedTheorem_of_heavyEdge
#print axioms FracRefutation.half_le_weightedCodegree_completeK
#print axioms exists_matching_sum_le_mul
#print axioms fracNibbleAt_of_one_sub_inv_le
#print axioms K4.k4Tri_uniform
#print axioms K4.halfWeight_load
#print axioms K4.halfWeight_sum
#print axioms K4.k4_matching_card_le_one
#print axioms K4.k4_spread_sum_le
#print axioms K4.k4_no_spread_near_optimal

end Nibble
