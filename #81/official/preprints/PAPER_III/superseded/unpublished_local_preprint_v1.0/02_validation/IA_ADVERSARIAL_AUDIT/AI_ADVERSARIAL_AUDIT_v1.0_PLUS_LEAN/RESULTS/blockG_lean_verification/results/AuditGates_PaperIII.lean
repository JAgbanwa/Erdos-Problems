import PaperIII

/- Audit gates for Paper III.
   Goal: (1) confirm the two external axioms AX1, AX2 are the ONLY project axioms;
         (2) confirm Theorem_1_1 / Corollary_1_2 depend on exactly [AX1, AX2, + standard];
         (3) confirm the corridor node Prop_10_1 is CLOSED (no AX1/AX2);
         (4) confirm bulk (E_4_3) depends on AX1 and sparse (E_8) on AX2. -/

-- The two external axioms themselves
#check @PaperIII.AX1
#check @PaperIII.AX2
#print axioms PaperIII.AX1
#print axioms PaperIII.AX2

-- Main results (expected: depend on AX1 + AX2 + standard)
#check @PaperIII.Theorem_1_1
#print axioms PaperIII.Theorem_1_1

#check @PaperIII.Corollary_1_2
#print axioms PaperIII.Corollary_1_2

-- Weak duality (expected: CLOSED, standard axioms only)
#check @PaperIII.nu3Star_le_tau3Star
#print axioms PaperIII.nu3Star_le_tau3Star

-- Corridor node Prop 10.1 (expected: CLOSED, no AX1/AX2)
#check @PaperIII.Prop_10_1_low
#print axioms PaperIII.Prop_10_1_low

#check @PaperIII.Prop_10_1_mid
#print axioms PaperIII.Prop_10_1_mid

-- Bulk assembly E-4.3 (expected: depends on AX1 only)
#check @PaperIII.E_4_3
#print axioms PaperIII.E_4_3

-- Sparse assembly E-8 (expected: depends on AX2 only)
#check @PaperIII.E_8
#print axioms PaperIII.E_8

-- High-ratio disposal (expected: CLOSED)
#check @PaperIII.Phi_le_high_ratio
#print axioms PaperIII.Phi_le_high_ratio

-- Three packing-form corollaries claimed UNCONDITIONAL by the manuscript
#print axioms PaperIII.factorization_assignment_packing
#print axioms PaperIII.double_factorization_packing
#print axioms PaperIII.reserved_gain_packing_bound_subset

-- Effective corridor cp-bound claimed axiom-free
#print axioms PaperIII.Corollary_12_2_bound

-- cp ≤ Phi bridge (expected: CLOSED)
#print axioms PaperIII.cp_le_Phi
