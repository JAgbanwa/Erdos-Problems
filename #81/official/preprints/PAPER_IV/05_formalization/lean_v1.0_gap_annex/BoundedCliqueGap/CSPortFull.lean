import BoundedCliqueGap.BoseSub
import BoundedCliqueGap.CSPortRich

/-
`BoundedCliqueGap.CSPortFull` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung G1 — the full-range port-poor packing theorem for complete split graphs

Assembling the pieces:

* the Bose Steiner triple system on the clique part `K = R × Fin 3`
  (`|K| = 3m`, `m = |R|`);
* its `6δ`-regular sub-family `sub` cut out by a difference set `D` of size
  `δ` (`BoundedCliqueGap.BoseSub`);
* Vizing's theorem (`BoundedCliqueGap.GVizing`) applied to the port graph, giving
  `6δ + 1` matchings, of which `6δ` are handed to the independent vertices;
* the Bose blocks *outside* `sub`, which pack the remaining clique edges with
  no loss at all.

The outcome, `nu3_CS_bose`, is a lower bound for `ν₃(CS(3m, 6δ))` matching the
LP ceiling `(C(3m,2) + 3m·6δ)/3` up to `3m/2`, for **every** `δ ≤ (m-1)/2` —
the divisibility constraints of rung C3 have disappeared.
-/

namespace BoundedCliqueGap

open Finset

namespace BoseSub

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] {ih : R} {D : Finset R}

/-- A subfamily of an edge-disjoint triangle family is edge-disjoint. -/
lemma isPacking_subset {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {P Q : Finset (Finset V)} (hP : IsPacking G P) (hQ : Q ⊆ P) : IsPacking G Q :=
  ⟨fun T hT => hP.1 T (hQ hT), fun T hT T' hT' hne => hP.2 T (hQ hT) T' (hQ hT') hne⟩

/-- **Rung G1, core packing bound.**  With `m = |R|` clique vertices per layer
(so `3m` clique vertices) and `s = 6δ` independent vertices, the complete split
graph has an edge-disjoint triangle family of size at least
`(C(3m,2) + 3m·6δ)/3 - 3m/2`. -/
theorem nu3_CS_bose (hih : (2 : R) * ih = 1) (hD0 : (0 : R) ∉ D)
    (hDsum : ∀ d ∈ D, ∀ d' ∈ D, d + d' ≠ 0) :
    3 * Fintype.card R * Fintype.card R + 12 * Fintype.card R * D.card
      ≤ 2 * nu3 (CS (R × Fin 3) (Fin (6 * D.card))) + 4 * Fintype.card R := by
  classical
  set m := Fintype.card R with hm
  set δ := D.card with hδ
  set H := portGraph ih D with hH
  -- Vizing: `6δ + 1` matchings exhausting the port graph
  obtain ⟨M, hcard2, hedge, hmatch, hglob, htot⟩ :=
    exists_matchingFamily H (6 * δ) (portGraph_maxDegree_le hih hD0 hDsum)
  -- the residual Bose blocks
  set P : Finset (Finset (R × Fin 3)) := Bose.family ih \ sub ih D with hP
  have hPsub : P ⊆ Bose.family ih := Finset.sdiff_subset
  have hPpack : IsPacking (⊤ : SimpleGraph (R × Fin 3)) P :=
    isPacking_subset (Bose.family_isPacking hih) hPsub
  -- the `6δ` matchings actually handed out
  set M' : Fin (6 * δ) → Finset (Finset (R × Fin 3)) := fun j => M j.succ with hM'
  have hports : ∑ j : Fin (6 * δ), (M' j).card + (M (0 : Fin (6 * δ + 1))).card
      = H.edgeFinset.card := by
    rw [← htot, Fin.sum_univ_succ]
    ring
  -- the port engine
  have hkey := nu3_CS_ge (K := R × Fin 3) (S := Fin (6 * δ)) M' P
    (fun j e he => hcard2 _ e he)
    (fun j e he e' he' hne => hmatch _ e he e' he' hne)
    (fun j j' e hj hj' => Fin.succ_injective _ (hglob _ _ e hj hj'))
    hPpack
    (by
      -- a port edge is an edge of a *selected* Bose block, hence not inside a residual one
      intro T hT j e he hsub
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hcard2 _ e he)
      have hadj : H.Adj a b := hedge _ _ he a (by simp) b (by simp) hab
      have hTa : a ∈ T := hsub (by simp)
      have hTb : b ∈ T := hsub (by simp)
      have hTfam : T ∈ Bose.family ih := hPsub hT
      have hTblk : T = Bose.blk ih a b := Bose.eq_blk_of_mem_family hih hTfam hTa hTb hab
      have : T ∈ sub ih D := by
        rw [hTblk]
        exact blk_mem_sub_of_adj hih hD0 hadj
      exact (Finset.mem_sdiff.1 hT).2 this)
  -- cardinalities
  have hcardK : Fintype.card (R × Fin 3) = 3 * m := by
    rw [Fintype.card_prod, Fintype.card_fin, hm]; ring
  have hM0 : 2 * (M (0 : Fin (6 * δ + 1))).card ≤ 3 * m := by
    have := card_le_half_of_matching (M (0 : Fin (6 * δ + 1)))
      (fun e he => hcard2 _ e he) (fun e he e' he' hne => hmatch _ e he e' he' hne)
    rwa [hcardK] at this
  have hE : 2 * H.edgeFinset.card = m * (18 * δ) :=
    card_edgeFinset_portGraph hih hD0 hDsum
  have hfam : 2 * (Bose.family ih).card = m * (3 * m - 1) := Bose.card_family hih
  have hsubcard : (sub ih D).card ≤ 3 * (m * δ) := card_sub_le
  have hsubfam : sub ih D ⊆ Bose.family ih := sub_subset_family hD0
  have hPcard : P.card + (sub ih D).card = (Bose.family ih).card :=
    Finset.card_sdiff_add_card_eq_card hsubfam
  -- put everything together
  set X := m * δ with hX
  set Y := m * m with hY
  have h1 : 2 * (∑ j : Fin (6 * δ), (M' j).card) + 2 * (M (0 : Fin (6 * δ + 1))).card
      = 18 * X := by
    have : m * (18 * δ) = 18 * X := by rw [hX]; ring
    rw [← this, ← hE, ← hports]; ring
  have hYeq : m * (3 * m - 1) + m = 3 * Y := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · simp [hY, hm0]
    · have h : 3 * m - 1 + 1 = 3 * m := by omega
      calc m * (3 * m - 1) + m = m * (3 * m - 1 + 1) := by ring
        _ = m * (3 * m) := by rw [h]
        _ = 3 * Y := by rw [hY]; ring
  have h2 : 2 * P.card + 2 * (sub ih D).card + m = 3 * Y := by
    have : 2 * ((Bose.family ih).card) = m * (3 * m - 1) := hfam
    rw [← hPcard] at this
    omega
  have h3 : (sub ih D).card ≤ 3 * X := by rw [hX]; exact hsubcard
  have hgoal : 3 * Y + 12 * X ≤ 2 * nu3 (CS (R × Fin 3) (Fin (6 * δ))) + 4 * m := by
    have hchain : ∑ j : Fin (6 * δ), (M' j).card + P.card
        ≤ nu3 (CS (R × Fin 3) (Fin (6 * δ))) := hkey
    omega
  calc 3 * m * m + 12 * m * δ = 3 * Y + 12 * X := by rw [hX, hY]; ring
    _ ≤ 2 * nu3 (CS (R × Fin 3) (Fin (6 * δ))) + 4 * m := hgoal

end BoseSub

/-! ## Instantiation at `R = ZMod n` -/

open BoseSub in
/-- **Rung G1, integral core.**  For `n` odd and `2δ ≤ n - 1`, the complete
split graph with `3n` clique vertices and `6δ` independent vertices satisfies
`3n² + 12nδ ≤ 2·ν₃ + 4n`, i.e. `ν₃ ≥ (C(3n,2) + 3n·6δ)/3 − 3n/2`. -/
theorem nu3_CS_bose_fin (n δ : ℕ) (hn : Odd n) (hδ : 2 * δ ≤ n - 1) :
    3 * n * n + 12 * n * δ ≤ 2 * nu3 (CS (Fin (3 * n)) (Fin (6 * δ))) + 4 * n := by
  classical
  have hn0 : 0 < n := hn.pos
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨ih, hih⟩ := zmod_two_mul_half (n := n) hn
  set D : Finset (ZMod n) := (Finset.range δ).image (fun j => ((j + 1 : ℕ) : ZMod n)) with hD
  have hlt : ∀ j < δ, j + 1 < n := by intro j hj; omega
  have hmemD : ∀ d : ZMod n, d ∈ D ↔ ∃ j < δ, d = ((j + 1 : ℕ) : ZMod n) := by
    intro d
    simp only [hD, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  have hcardD : D.card = δ := by
    rw [hD, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    have h := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (hlt a ha), ZMod.val_natCast_of_lt (hlt b hb)] at h
    omega
  have hD0 : (0 : ZMod n) ∉ D := by
    intro h
    obtain ⟨j, hj, hje⟩ := (hmemD 0).1 h
    have h2 := congrArg ZMod.val hje
    rw [ZMod.val_natCast_of_lt (hlt j hj), ZMod.val_zero] at h2
    omega
  have hDsum : ∀ d ∈ D, ∀ d' ∈ D, d + d' ≠ 0 := by
    intro d hd d' hd' hcon
    obtain ⟨a, ha, rfl⟩ := (hmemD d).1 hd
    obtain ⟨b, hb, rfl⟩ := (hmemD d').1 hd'
    have hsum : (((a + 1) + (b + 1) : ℕ) : ZMod n) = 0 := by push_cast at hcon ⊢; linear_combination hcon
    have h2 := congrArg ZMod.val hsum
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at h2
    omega
  have hcore := nu3_CS_bose (R := ZMod n) hih hD0 hDsum
  rw [ZMod.card n, hcardD] at hcore
  refine le_trans hcore ?_
  have hcardK : Fintype.card (ZMod n × Fin 3) = 3 * n := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]; ring
  have hmono : nu3 (CS (ZMod n × Fin 3) (Fin (6 * δ))) ≤ nu3 (CS (Fin (3 * n)) (Fin (6 * δ))) :=
    nu3_CS_mono (Fintype.equivFinOfCardEq hcardK).toEmbedding (Function.Embedding.refl _)
  omega

/-! ## Rung G1 — the full-range CS gap theorem -/

/-- Monotonicity of `ν₃(CS -, -)` in the two sizes. -/
lemma nu3_CS_fin_mono {k k' s s' : ℕ} (hk : k' ≤ k) (hs : s' ≤ s) :
    nu3 (CS (Fin k') (Fin s')) ≤ nu3 (CS (Fin k) (Fin s)) :=
  nu3_CS_mono (Fin.castLEEmb hk) (Fin.castLEEmb hs)

/-! ## Axiom audit -/

end BoundedCliqueGap
