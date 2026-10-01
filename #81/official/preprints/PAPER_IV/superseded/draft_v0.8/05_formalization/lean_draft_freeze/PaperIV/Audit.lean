import PaperIV.Erdos81Unconditional
import PaperIV.HybridRoute
import PaperIV.SeparationAbsorptionRoute
import PaperIV.SplitCompleteSharpValue
import PaperIV.PaperTheorems
import PaperIV.Erdos81AllOrders
import PaperIV.SplitCompleteRigidity
import PaperIV.SplitCompleteDefect
import PaperIV.LinearCoefficient
import PaperIV.BalancedReserve
import PaperIV.SplitMixedGap
import PaperIV.SimplicialReduction
import PaperIV.SimplicialReductionRefined
import PaperIV.IntegralStability
import PaperIV.ExtremalClassification
import PaperIV.SpreadLedgerAbsorption
import PaperIV.SpreadAbsorptionCompatibility
import PaperIV.CliqueTree
import PaperIV.NearThresholdSensitivity
import PaperIV.FourHostClosure
import PaperIV.ReserveIdentity
import PaperIV.LossBudget

/-!
# Auditoría canónica de Paper IV

Un solo fichero, un solo comando. Imprime la huella de axiomas de **todos los enunciados que van
al paper** y de sus byproducts.

La lista permitida es exactamente `propext`, `Classical.choice`, `Quot.sound`. Cualquier otra
cosa —en particular `sorryAx`— es un fallo.

La organización es la del manuscrito, no la del árbol de ficheros: primero la prueba, después lo
que el método produce además. Los árboles de cliques van aparte, en `PaperIV/CliqueTreeAudit.lean`
(53 resultados), porque son biblioteca reutilizable y no un paso de la demostración.

## Qué garantiza esto, y qué no

Garantiza que cada enunciado listado se deriva sólo de los tres axiomas fundacionales de Lean.
**No** garantiza por sí solo que el enunciado diga lo que uno cree: eso lo da leer el enunciado.
Y no sustituye a la auditoría del **cono de constantes**, que es la que certifica de qué
desarrollos depende realmente cada teorema.
-/

/-! ## 0. Teorema A — la respuesta al problema, para **todos** los órdenes

Es el enunciado que responde a Erdős, Ordman y Zalcstein sin excepciones de orden.  Va primero
porque es el que da título al paper. -/

#print axioms PaperIV.Erdos81AllOrders.erdos81_all_orders
#print axioms PaperIV.Erdos81AllOrders.erdos81_all_orders_additive
#print axioms PaperIV.Erdos81AllOrders.exists_trivial_cliquePartition

/-! ## 1. Teorema B — la forma aguda -/

#print axioms PaperIV.Erdos81Unconditional.erdos81_cliquePartition
#print axioms PaperIV.Erdos81Unconditional.erdos81_linear_form
#print axioms PaperIV.Erdos81Unconditional.erdos81_chordalTarget

/-! ## 2. La infraestructura que lo alimenta

El óptimo fraccional se **construye** internamente; no se postula. El kernel LP es el resultado
de Paper I, reprobado aquí sobre `ℚ` porque el modelo mixto necesita el óptimo racional. -/

#print axioms PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum
#print axioms PaperI.FiniteLP.exists_optimal_pair

/-! ## 3. Las dos ramas del régimen

Lejana por redondeo mixto subcuadrático, cercana por construcción física. -/

#print axioms PaperIV.RC01Final.rc01_uniformRoundingTarget
#print axioms PaperIV.RC01FarAssembly.farRegime_cliquePartition
#print axioms PaperIV.NearH1GlobalAssembly.nearRegimeAt
#print axioms PaperIV.NearH1GlobalAssembly.chordalTargetAt
#print axioms PaperIV.RootRegularizationBridge.exists_regularizedRoot_engineFree

/-! ## 4. La restricción estructural común

`chordal_far_or_nearStructure` es el enunciado que organiza el paper: todo cordal grande o tiene
holgura cuadrática, o exhibe un testigo estructural literal.  Cada mecanismo descarga una rama. -/

#print axioms PaperIV.HybridDichotomy.chordal_far_or_nearStructure
#print axioms PaperIV.HybridDichotomy.chordal_near_extremal_stability
#print axioms PaperIV.HybridDichotomy.erdos81_of_structuralDichotomy

/-! ## 4bis. Los enunciados del paper que no viven en un módulo técnico

La forma lineal del cierre híbrido, la cordalidad del testigo extremal y el máximo eventual
sobre todos los cordales.  Los tres demostrados sobre esta cadena. -/

#print axioms PaperIV.PaperTheorems.erdos81_hybrid_linear_form
#print axioms PaperIV.PaperTheorems.splitGraph_isChordal
#print axioms PaperIV.PaperTheorems.exists_chordal_extremal_witness
#print axioms PaperIV.PaperTheorems.erdos81_max_eq

/-! ## 5. Rigidez extremal: el valor exacto de los completo-split

La cota inferior es sobre **todas** las particiones en cliques, no sólo las de orden a lo sumo
cuatro.  Eso la convierte en un enunciado de rigidez y no en una mera construcción. -/

#print axioms PaperIV.SplitCompleteExactValue.exists_optimal_cliquePartition
#print axioms PaperIV.SplitCompleteExactValueAllParities.exists_optimal_cliquePartition_allParities
#print axioms PaperIV.SplitCompleteSharpLower.cliquePartition_size_ge_baseline_unrestricted
#print axioms PaperIV.SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities
#print axioms PaperIV.SplitCompleteSharpLower.critical_baseline_eq_targetSize

/-! ### Casos de igualdad dentro de la familia completo-split

Clasificación completa de los núcleos que alcanzan `targetSize n`: uno, salvo cuando
`n ≡ 1 (mod 3)`, donde son exactamente dos y consecutivos.  **No** clasifica todos los cordales
extremales: eso sigue abierto. -/

#print axioms PaperIV.SplitCompleteRigidity.six_mul_baseline_add_sq
#print axioms PaperIV.SplitCompleteRigidity.baseline_le_targetSize
#print axioms PaperIV.SplitCompleteRigidity.baseline_eq_targetSize_iff
#print axioms PaperIV.SplitCompleteRigidity.optimal_cores

/-! ### BP-03 — defecto exacto de las particiones completo-split

Refina la cota inferior a una **identidad**: el exceso sobre el óptimo es la suma de los defectos
por pieza.  Con la clasificación de las piezas que no pagan y la versión cuantitativa. -/

#print axioms PaperIV.SplitCompleteDefect.size_add_choose_eq_mul_add_sum_defect
#print axioms PaperIV.SplitCompleteDefect.defect_eq_zero_iff
#print axioms PaperIV.SplitCompleteDefect.defect_pos_of_no_host
#print axioms PaperIV.SplitCompleteDefect.card_paying_pieces_le_excess

/-! ### BP-05 — el coeficiente lineal `1/6` es óptimo -/

#print axioms PaperIV.LinearCoefficient.linear_coefficient_optimal

/-! ### HT-01 — reserva de aristas equilibrada (herramienta de apéndice) -/

#print axioms PaperIV.BalancedReserve.card_filter_edgeFamily
#print axioms PaperIV.BalancedReserve.exists_balanced_reserve

/-! ## 6. Absorción spread, y su presupuesto pagado por el ledger RD09 -/

#print axioms PaperIV.SpreadAbsorption.exists_certificate
#print axioms PaperIV.SpreadAbsorption.exists_lowConflict_certificate
#print axioms PaperIV.SpreadAbsorption.physical_triangle_absorber
#print axioms PaperIV.SpreadAbsorption.totalGain_physical_triangle_absorber
#print axioms PaperIV.SpreadAbsorption.exists_budgeted_physical_triangle_absorber
#print axioms PaperIV.SpreadLedgerAbsorption.total_ledgerBad_le_two_accounts
#print axioms PaperIV.SpreadLedgerAbsorption.total_ledgerBad_le_paid_mass
#print axioms PaperIV.SpreadLedgerAbsorption.exists_spread_absorber_count_add_cost_le_baseline
#print axioms PaperIV.SpreadAbsorptionCompatibility.isPacking_union_absorber
#print axioms PaperIV.SpreadAbsorptionCompatibility.exists_compatible_spread_absorber

/-! ### BP-07 — un mismo certificado, presupuestado y compatible

Primero se elige el certificado de coste acotado y **después** se le aplican los lemas de unión;
no se combinan dos elecciones existenciales independientes. -/

#print axioms PaperIV.SpreadAbsorptionCompatibility.exists_budgeted_compatible_spread_absorber

/-! ## 7. Ruta de separación y absorción -/

#print axioms PaperIV.SeparationAbsorptionRoute.chordal_dualSeparated_or_absorbable
#print axioms PaperIV.SeparationAbsorptionRoute.AbsorbableCriticalStructure.exists_target_partition
#print axioms PaperIV.SeparationAbsorptionRoute.erdos81_of_dualSeparation_absorption

/-! ## 8. BP-01 y BP-02 — estabilidad integral y clasificación de extremizadores -/

#print axioms PaperIV.SplitEditIdentity.editDist_split_eq
#print axioms PaperIV.FarSlackQuantitative.farRegime_cliquePartition_slack
#print axioms PaperIV.IntegralStability.chordal_linear_stability
#print axioms PaperIV.ExtremalClassification.split_value
#print axioms PaperIV.ExtremalClassification.chordal_extremal_classification

/-! ## 9. BP-04 — gap mixto cero en el completo-split -/

#print axioms PaperIV.SplitMixedGap.fracPacking_value_le
#print axioms PaperIV.SplitMixedGap.sum_gainOf_add_size
#print axioms PaperIV.SplitMixedGap.exists_integral_gain_eq
#print axioms PaperIV.SplitMixedGap.mixed_gap_zero

/-! ## 10. Reducción simplicial y el rango pequeño -/

#print axioms PaperIV.SimplicialReduction.exists_cliquePartition_of_delete_vertex
#print axioms PaperIV.SimplicialReduction.targetSize_succ_sub_targetSize
#print axioms PaperIV.SimplicialReduction.sharpBound_of_degree_le
#print axioms PaperIV.SimplicialReduction.sharpBoundAt_of_largeCliqueRegime
#print axioms PaperIV.SimplicialReductionRefined.exists_cliquePartition_freeStar
#print axioms PaperIV.SimplicialReductionRefined.not_strongLoosePieceHypothesis

/-! ## 11. Sensibilidad del umbral cercano

Las tres desigualdades escalares que fijan `2·10^13`, aisladas de todo grafo.  Dicen que el
umbral es cuadrático en el presupuesto de regularización `B`, y por tanto qué constante hay que
atacar si alguna vez interesa bajarlo. -/

#print axioms PaperIV.NearThresholdSensitivity.eps_le_of_physical_budget
#print axioms PaperIV.NearThresholdSensitivity.descent_threshold
#print axioms PaperIV.NearThresholdSensitivity.near_threshold_of_budget
#print axioms PaperIV.NearThresholdSensitivity.edit_mass_of_budget

/-! ## 12. BP-06 — remate con cuatro anfitriones

Cuatro anfitriones exteriores universales absorben entero un residuo de grado máximo tres. El
puente que faltaba era que las clases de color de Vizing sean emparejamientos **literales**. Los
anfitriones son hipótesis del enunciado, no se afirma su existencia universal. -/

#print axioms PaperIV.FourHostClosure.colourClass_isLiteralMatching
#print axioms PaperIV.FourHostClosure.exists_fourHost_packing
#print axioms PaperIV.FourHostClosure.fourHost_saving

/-! ## 13. La identidad de reserva

`M(n) = B_n(k) + M(d)`, exacta en `ℕ` con los pisos puestos. El centro consume todo el
presupuesto; alejarse genera reserva. De ahí salen en una línea la cota `B_n(k) ≤ M(n)` y la
clasificación de los núcleos óptimos, y la hipótesis de calibración `residual² ≤ 24·δ` se lee
como `Mq(d) + 1/24 ≤ δ`. -/

#print axioms PaperIV.ReserveIdentity.centreDefect_mul_succ
#print axioms PaperIV.ReserveIdentity.targetSize_eq_baseline_add_reserve
#print axioms PaperIV.ReserveIdentity.baseline_le_targetSize_of_reserve
#print axioms PaperIV.ReserveIdentity.baseline_eq_targetSize_iff_reserve
#print axioms PaperIV.ReserveIdentity.centreDefect_le_one_iff
#print axioms PaperIV.ReserveIdentity.sq_residual_eq
#print axioms PaperIV.ReserveIdentity.residual_sq_le_iff

/-! ## 14. El presupuesto de pérdida, sin restricción de orden

La identidad (1.3) del manuscrito no depende del modelo mixto: vale para toda partición en
cliques. Y la forma `cp` —la que pide literalmente Erdős, Ordman y Zalcstein— se sigue de la
nuestra olvidando la restricción de orden, nunca al revés. -/

#print axioms PaperIV.LossBudget.budget_iff
#print axioms PaperIV.LossBudget.size_add_gain_eq
#print axioms PaperIV.LossBudget.erdos81_cp_form
#print axioms PaperIV.LossBudget.erdos81_cp_form_all_orders
