import ThreeRegime.AggregateRefutation
import ThreeRegime.CompleteStateObligation
import ThreeRegime.TrianglePackingParity
import ThreeRegime.SeparatorBudget
import ThreeRegime.CompleteStateAllOrders
import ThreeRegime.TriplePackingBound

/-!
# Auditoría de axiomas

Todos los resultados de `ThreeRegime` deben usar sólo los axiomas estándar
`[propext, Classical.choice, Quot.sound]`: ni `sorry`, ni axiomas propios, ni
`native_decide`, ni `implemented_by`.
-/

#print axioms ThreeRegime.Selector.exists_le_of_weighted_aggregate
#print axioms ThreeRegime.Selector.aggregate_not_necessary
#print axioms ThreeRegime.Selector.weighted_aggregate_fails_of_one_expensive
#print axioms ThreeRegime.reserve_lt_missing
#print axioms ThreeRegime.extreme_route_fails_on_complete
#print axioms ThreeRegime.complete_state_has_no_separator
#print axioms ThreeRegime.centre_route_closes_on_small_complete
#print axioms ThreeRegime.centre_closes_of_triangle_packing
#print axioms ThreeRegime.clique_removal_over_budget
#print axioms ThreeRegime.AggregateRefutation.K4_picture
#print axioms ThreeRegime.AggregateRefutation.aggregate_fails_under_unavailability_pricing

-- Revisión propia: la obligación sólo-triángulos es insatisfacible en `n ≡ 4 (mod 6)`,
-- y la forma mixta que sí la reemplaza.
#print axioms ThreeRegime.TrianglePackingParity.card_filter_mem_pairs
#print axioms ThreeRegime.TrianglePackingParity.two_mul_card_pieces_at_le
#print axioms ThreeRegime.TrianglePackingParity.six_mul_card_pieces_le
#print axioms ThreeRegime.TrianglePackingParity.not_triangle_obligation_of_four_mod_six
#print axioms ThreeRegime.TrianglePackingParity.centre_closes_of_gain

-- El estado completo, cerrado para todo orden.
#print axioms ThreeRegime.Transport.gain_eq_two_mul_card_add_three_mul_card_four
#print axioms ThreeRegime.Owner.packingOfOwn
#print axioms ThreeRegime.Owner.six_mul_card_pieces_avoiding
#print axioms ThreeRegime.Latin.Frame.own_spec
#print axioms ThreeRegime.Latin.Frame.biUnion_eq_edgeFinset
#print axioms ThreeRegime.Latin.Frame.filter_card_four_card
#print axioms ThreeRegime.Latin.oddFrame
#print axioms ThreeRegime.Latin.evenFrame
#print axioms ThreeRegime.CompleteStateAllOrders.closes_zero_mod_six
#print axioms ThreeRegime.CompleteStateAllOrders.closes_one_mod_six
#print axioms ThreeRegime.CompleteStateAllOrders.closes_two_mod_six
#print axioms ThreeRegime.CompleteStateAllOrders.closes_three_mod_six
#print axioms ThreeRegime.CompleteStateAllOrders.closes_four_mod_six
#print axioms ThreeRegime.CompleteStateAllOrders.closes_five_mod_six
#print axioms ThreeRegime.CompleteStateAllOrders.exists_packing
#print axioms ThreeRegime.CompleteStateAllOrders.complete_state_closes

-- El complemento: la cota superior de empaquetamiento de ternas para todo orden.
#print axioms ThreeRegime.TriplePackingBound.three_mul_card_pieces_le
#print axioms ThreeRegime.TriplePackingBound.six_mul_card_pieces_le_of_odd
#print axioms ThreeRegime.TriplePackingBound.six_mul_card_pieces_le_of_even
