# Frozen headers for the supplemental E1 review

Static extraction; namespace and inherited variables must be read in the linked source. No new Lean execution.

## PaperIV.NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp

Source `PaperIV/NearH1LocalConstructor.lean:36`; SHA-256 `f5994eefb45a008f92a51c47a05ff8fcc071f19f49467cd0fff06dad4aefa5b2`.

```lean
theorem exists_near_partition_paid_by_root_sharp {n : ℕ}
    (hn : 4 * 10 ^ 12 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G) {w : ℚ}
    (hw : CertifiedFractionalOptimum G w)
    (hdist : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty G
        ((n : ℚ) ^ 2) < PaperIV.NearH1Calibration.eps)
    (hnear : (n : ℚ) ^ 2 / 6 -
        PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2 ≤
      (G.edgeFinset.card : ℚ) - w) :
    ∃ (R : Finset (Fin n)) (Q : CliquePartition G),
      G.IsClique (R : Set (Fin n)) ∧
      |3 * (R.card : ℚ) - (n : ℚ)| ≤ (n : ℚ) / 50 ∧
      Q.OrderAtMost 4 ∧
      (Q.size : ℚ) ≤
        splitBaseline (n : ℚ) (R.card : ℚ) -
          ((outsideEdges G R).card : ℚ) / 20 -
          (missingIncidences G R : ℚ) / 2
```

## PaperIV.NearH1LocalConstructor.exists_near_partition_paid_by_root

Source `PaperIV/NearH1LocalConstructor.lean:121`; SHA-256 `f5994eefb45a008f92a51c47a05ff8fcc071f19f49467cd0fff06dad4aefa5b2`.

```lean
theorem exists_near_partition_paid_by_root {n : ℕ}
    (hn : 4 * 10 ^ 12 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G) {w : ℚ}
    (hw : CertifiedFractionalOptimum G w)
    (hdist : graphFamDistNorm
      (allSplitSupports (V := Fin n)) allSplitSupports_nonempty G
        ((n : ℚ) ^ 2) < PaperIV.NearH1Calibration.eps)
    (hnear : (n : ℚ) ^ 2 / 6 -
        PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2 ≤
      (G.edgeFinset.card : ℚ) - w) :
    ∃ (R : Finset (Fin n)) (Q : CliquePartition G),
      G.IsClique (R : Set (Fin n)) ∧
      (n : ℚ) / 4 ≤ (R.card : ℚ) ∧
      (R.card : ℚ) ≤ (n : ℚ) / 2 ∧
      Q.OrderAtMost 4 ∧
      (Q.size : ℚ) ≤
        splitBaseline (n : ℚ) (R.card : ℚ) -
          ((outsideEdges G R).card : ℚ) / 20 -
          (missingIncidences G R : ℚ) / 2
```

## PaperIV.NearCriticalDichotomy.chordal_far_or_criticalRoot

Source `PaperIV/NearCriticalDichotomy.lean:41`; SHA-256 `f122406defdfdbd802c6aab17d4bd929d18ec639046aa02ab2fe77654d87bd72`.

```lean
theorem chordal_far_or_criticalRoot :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ((G.edgeFinset.card : ℚ) - w <
            (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) ∨
          ∃ R C : Finset (Fin n),
            G.IsClique (R : Set (Fin n)) ∧
            |3 * (R.card : ℚ) - (n : ℚ)| ≤ (n : ℚ) / 50 ∧
            C.Nonempty ∧
            (PaperIV.EditMetric.editDist G.edgeFinset
                (graphEdgeSupport
                  (PaperIV.SplitUniformIncidence.splitGraph C
                    (Finset.univ \ C))) : ℚ) ≤
              PaperIV.NearH1Calibration.eps * (n : ℚ) ^ 2 ∧
            |3 * (C.card : ℚ) - (n : ℚ)| ≤ (n : ℚ) / 10000 ∧
            |(R.card : ℚ) - (C.card : ℚ)| ≤ (n : ℚ) / 100
```

## PaperIV.NearCriticalDichotomy.chordal_far_or_edge_density

Source `PaperIV/NearCriticalDichotomy.lean:103`; SHA-256 `f122406defdfdbd802c6aab17d4bd929d18ec639046aa02ab2fe77654d87bd72`.

```lean
theorem chordal_far_or_edge_density :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ((G.edgeFinset.card : ℚ) - w <
            (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) ∨
          |(G.edgeFinset.card : ℚ) - 5 * (n : ℚ) ^ 2 / 18| ≤ (n : ℚ) ^ 2 / 10000
```

## PaperIV.HybridDichotomy.chordal_far_or_nearStructure

Source `PaperIV/HybridDichotomy.lean:69`; SHA-256 `7cb1a1c46e20403cefa5abbf9f08ea531a70015a02524e4182343c27beafb81a`.

```lean
theorem chordal_far_or_nearStructure :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G → ∀ w : ℚ, CertifiedFractionalOptimum G w →
        ((G.edgeFinset.card : ℚ) - w <
            (n : ℚ) ^ 2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ) ^ 2) ∨
          Nonempty (NearStructureWitness G)
```

## PaperIV.SharpConstantOptimality.erdos81_quadratic_constant_optimal

Source `PaperIV/SharpConstantOptimality.lean:52`; SHA-256 `9661832fc84ea6f051cb825fa66e5d6d10508722ce3604429f7591b97dc092e7`.

```lean
theorem erdos81_quadratic_constant_optimal {c C : ℚ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      SimpleGraph.IsChordal G → ∃ Q : CliquePartition G, (Q.size : ℚ) ≤ c * (n : ℚ) ^ 2 +
        C * (n : ℚ)) :
    1 / 6 ≤ c
```

## PaperIV.SharpConstantOptimality.erdos81_quadratic_constant_isLeast

Source `PaperIV/SharpConstantOptimality.lean:93`; SHA-256 `9661832fc84ea6f051cb825fa66e5d6d10508722ce3604429f7591b97dc092e7`.

```lean
theorem erdos81_quadratic_constant_isLeast :
    IsLeast {c : ℚ | ∃ (C : ℚ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), SimpleGraph.IsChordal G →
        ∃ Q : CliquePartition G, (Q.size : ℚ) ≤ c * (n : ℚ) ^ 2 + C * (n : ℚ)}
      (1 / 6)
```

## PaperIV.LinearCoefficient.linear_coefficient_optimal

Source `PaperIV/LinearCoefficient.lean:49`; SHA-256 `b4a643cc5b5d099fc7b9f50af57e840394a75582153acdf1f5278a523494e614`.

```lean
theorem linear_coefficient_optimal (c B : ℚ) (hc : c < 1 / 6) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        SimpleGraph.IsChordal G ∧
        ∀ Q : CliquePartition G, (n : ℚ) ^ 2 / 6 + c * (n : ℚ) + B < (Q.size : ℚ)
```

## PaperIV.RootPartitionStability.sum_rootPieceDefect_eq

Source `PaperIV/RootPartitionStability.lean:200`; SHA-256 `7253ae28570782a7682ccb94e1b87241912d3c75f01fc573bb4a908c0c5f58dd`.

```lean
theorem sum_rootPieceDefect_eq (R : Finset V)
    (hR : G.IsClique (R : Set V)) (Q : CliquePartition G) :
    ∑ K ∈ Q.pieces, rootPieceDefect R K =
      (Q.size : ℚ) - splitBaseline (Fintype.card V) R.card
        + missingIncidences G R + 3 * (outsideEdges G R).card
```

## PaperIV.SplitMixedGap.mixed_gap_zero

Source `PaperIV/SplitMixedGap.lean:167`; SHA-256 `d340f1cc207de1238f7d3fbebf02615702b645edf91644ebfb8c7342689c51cb`.

```lean
theorem mixed_gap_zero {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcore : 2 ≤ Core.card) (hhosts : Core.card ≤ Hosts.card) :
    (∀ x : FracPacking (splitGraph Core Hosts) ℚ,
        x.value ≤ 2 * (Core.card.choose 2 : ℚ)) ∧
      ∃ Q : CliquePartition (splitGraph Core Hosts),
        ∑ K ∈ Q.pieces, FarRounding.gainOf K = 2 * Core.card.choose 2
```

## PaperIV.SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities

Source `PaperIV/SplitCompleteSharpValue.lean:14`; SHA-256 `cd650a63d4ae5b908881ea415e24dfaa486c2c9a5fa463c14f4258fddd2885f7`.

```lean
theorem exists_sharp_cliquePartition_allParities
    {Core Hosts : Finset V} (hd : Disjoint Core Hosts)
    (hcore : 2 ≤ Core.card) (hhosts : Core.card ≤ Hosts.card) :
    ∃ Q : CliquePartition (splitGraph Core Hosts),
      Q.OrderAtMost 4 ∧
      Q.size = Core.card * Hosts.card - Core.card.choose 2 ∧
      ∀ R : CliquePartition (splitGraph Core Hosts), Q.size ≤ R.size
```

## FarExploration.CleanupRigidVerdict.threshold_gt_exp

Source `FarExploration/CleanupRigidVerdict.lean:194`; SHA-256 `186e1ea1f241592a70e3a99a1159592fac63cfcf0f51d22e152f50dcea53b9a6`.

```lean
theorem threshold_gt_exp (eps : ℚ) (heps : 0 < eps) (gam Cst : ℝ) (hgam : gam ≤ 1 / 2) (N₀ : ℕ)
    (hN : CleanupAtWith gam Cst (eps / 30) (eps / 4) N₀) (t : ℝ) (ht : 4 ≤ t)
    (hteps : 7 * (eps : ℝ) ≤ Real.exp (-t)) :
    Real.exp (t ^ 2 / 16) < (N₀ : ℝ)
```

## FarExploration.CleanupRigidVerdict.threshold_gt_exp_seventy_two

Source `FarExploration/CleanupRigidVerdict.lean:271`; SHA-256 `186e1ea1f241592a70e3a99a1159592fac63cfcf0f51d22e152f50dcea53b9a6`.

```lean
theorem threshold_gt_exp_seventy_two (eps : ℚ) (heps : 0 < eps) (gam Cst : ℝ) (hgam : gam ≤ 1 / 2)
    (N₀ : ℕ) (hN : CleanupAtWith gam Cst (eps / 30) (eps / 4) N₀)
    (hsmall : (eps : ℝ) ≤ 1 / (7 * Real.exp 34)) :
    Real.exp 72 < (N₀ : ℝ)
```

