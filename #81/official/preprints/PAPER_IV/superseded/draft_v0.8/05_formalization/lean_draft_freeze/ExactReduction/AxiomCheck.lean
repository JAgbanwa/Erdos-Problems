import ExactReduction.MinimalKernel
import ExactReduction.ShellObstruction
import ExactReduction.JointStar

/-!
# Auditoría de axiomas de `ExactReduction`

Todo lo demostrado en esta biblioteca debe apoyarse únicamente en
`[propext, Classical.choice, Quot.sound]`.  No hay `axiom`, `sorry`, `admit`,
`native_decide` ni `implemented_by` en ninguno de los módulos.
-/

#print axioms ExactReduction.targetSize_succ
#print axioms ExactReduction.targetSize_sub_one
#print axioms ExactReduction.leafShell_budget_lt
#print axioms ExactReduction.deleteAt_isChordal
#print axioms ExactReduction.exists_cliquePartition_of_deleteAt
#print axioms ExactReduction.target_of_small_degree
#print axioms ExactReduction.minDegree_of_minimal_counterexample
#print axioms ExactReduction.exists_large_clique_of_minimal_counterexample
#print axioms ExactReduction.card_eq_of_minimal_counterexample
#print axioms ExactReduction.card_edges_of_minimal_counterexample
#print axioms ExactReduction.kernel_of_minimal_counterexample
#print axioms ExactReduction.targetOn_of_small_degree_vertex
#print axioms ExactReduction.ShellObstruction.shellCover_card_ge
#print axioms ExactReduction.ShellObstruction.card_trivialShellCover
#print axioms ExactReduction.ShellObstruction.leafShell_reduction_fails
#print axioms ExactReduction.ShellObstruction.shell_three_two_exceeds_budget
#print axioms ExactReduction.ShellObstruction.shellCoverCredit_card_ge
#print axioms ExactReduction.ShellObstruction.credit_bound_within_budget
#print axioms ExactReduction.JointStar.starCover_card_ge
#print axioms ExactReduction.JointStar.star_bound_within_target
