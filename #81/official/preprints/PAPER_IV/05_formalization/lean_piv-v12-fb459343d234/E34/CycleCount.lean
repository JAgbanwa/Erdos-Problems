import PaperIV.EditRouteUnconditional

/-!
# E34 — Lemma L1: induced cycles are polynomially rare under rooted defect `s`

If `G` (on `Fin n`) has rooted defect `≤ s`, then for every `k ≥ 4`
`indCopies (cycleGraph k) G ≤ 2·k·s·n^(k-1)`.

Proof (by induction on a vertex set `U`): the rooted-defect property with empty root gives a
vertex `v ∈ U` whose neighbourhood in `U` is a clique `C` plus a set `X` of at most `s`
vertices.  An induced cycle inside `U` either avoids `v`, or passes through `v` at some
position `p`; its two cycle-neighbours are adjacent to `v` and non-adjacent to each other, so
they are not both in `C`, and one of them lies in `X`.  The cycles through `v` are therefore
at most `k · 2 · s · |U|^(k-2)`, and `(u-1)^(k-1) + u^(k-2) ≤ u^(k-1)`.
-/

namespace E34

open Finset PaperIV.RootedSimplicialDefect PaperIV.EditRoute

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- `AlonShapira.editDist` with arbitrary `Fintype` instances on the edge sets. -/
theorem editDist_eq_card {m : ℕ} (G H : SimpleGraph (Fin m)) [Fintype G.edgeSet]
    [Fintype H.edgeSet] : AlonShapira.editDist G H = (symmDiff G.edgeFinset H.edgeFinset).card := by
  unfold AlonShapira.editDist
  congr!

/-- Labelled induced `k`-cycles all of whose vertices lie in `U`. -/
def cycTuplesIn (k : ℕ) (U : Finset (Fin n)) : Finset (Fin k → Fin n) :=
  (cycTuples G k).filter (fun f => ∀ i, f i ∈ U)

/-- The box of tuples with a prescribed value at `p`, values in `X` at `q`, values in `U`
elsewhere. -/
def box {k : ℕ} (p q : Fin k) (v : Fin n) (X U : Finset (Fin n)) : Finset (Fin k → Fin n) :=
  Fintype.piFinset fun i => if i = p then {v} else if i = q then X else U

theorem card_box_le {k : ℕ} (p q : Fin k) (hpq : p ≠ q) (v : Fin n) (X U : Finset (Fin n)) :
    (box p q v X U).card ≤ X.card * U.card ^ (k - 2) := by
  classical
  unfold box
  rw [Fintype.card_piFinset]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ p)]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ q⟩)]
  have hrest : ∀ i ∈ ((univ : Finset (Fin k)).erase p).erase q,
      (if i = p then ({v} : Finset (Fin n)) else if i = q then X else U).card = U.card := by
    intro i hi
    have h1 : i ≠ q := (Finset.mem_erase.1 hi).1
    have h2 : i ≠ p := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    simp [h1, h2]
  rw [Finset.prod_congr rfl hrest, Finset.prod_const]
  have hcard : (((univ : Finset (Fin k)).erase p).erase q).card = k - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ q⟩),
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcard]
  simp [hpq.symm]
  rw [mul_comm]

/-- Cyclic successor and predecessor positions. -/
def succPos {k : ℕ} (hk : 0 < k) (p : Fin k) : Fin k :=
  ⟨if p.val + 1 < k then p.val + 1 else 0, by split_ifs <;> omega⟩

def predPos {k : ℕ} (hk : 0 < k) (p : Fin k) : Fin k :=
  ⟨if p.val = 0 then k - 1 else p.val - 1, by split_ifs <;> omega⟩

theorem mod_succ_eq {k a : ℕ} (ha : a < k) :
    (a + 1) % k = if a + 1 < k then a + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : a + 1 = k := by omega
    rw [this, Nat.mod_self]

theorem cyc_adj_succ {k : ℕ} (hk : 4 ≤ k) (p : Fin k) :
    (SimpleGraph.cycleGraph k).Adj p (succPos (by omega) p) := by
  rw [cycleGraph_adj_iff_mod (by omega)]
  left
  simp only [succPos]
  exact mod_succ_eq p.isLt

theorem cyc_adj_pred {k : ℕ} (hk : 4 ≤ k) (p : Fin k) :
    (SimpleGraph.cycleGraph k).Adj p (predPos (by omega) p) := by
  rw [cycleGraph_adj_iff_mod (by omega)]
  right
  simp only [predPos]
  rw [mod_succ_eq (by split_ifs <;> omega)]
  split_ifs <;> omega

theorem succ_ne_pred {k : ℕ} (hk : 4 ≤ k) (p : Fin k) :
    succPos (by omega) p ≠ predPos (by omega) p := by
  intro h
  have := congrArg Fin.val h
  simp only [succPos, predPos] at this
  have hp := p.isLt
  split_ifs at this <;> omega

theorem not_cyc_adj_succ_pred {k : ℕ} (hk : 4 ≤ k) (p : Fin k) :
    ¬ (SimpleGraph.cycleGraph k).Adj (succPos (by omega) p) (predPos (by omega) p) := by
  rw [cycleGraph_adj_iff_mod (by omega)]
  have hp := p.isLt
  simp only [succPos, predPos]
  rw [mod_succ_eq (by split_ifs <;> omega), mod_succ_eq (by split_ifs <;> omega)]
  rintro (h | h) <;> split_ifs at h <;> omega

/-- The covering step. -/
theorem cycTuplesIn_subset {k : ℕ} (hk : 4 ≤ k) (U : Finset (Fin n)) (v : Fin n)
    (C : Finset (Fin n)) (hC : G.IsClique (C : Set (Fin n))) :
    cycTuplesIn G k U ⊆ cycTuplesIn G k (U.erase v) ∪
      (univ : Finset (Fin k)).biUnion (fun p =>
        box p (succPos (by omega) p) v (neighborsIn G U v \ C) U ∪
        box p (predPos (by omega) p) v (neighborsIn G U v \ C) U) := by
  intro f hf
  simp only [cycTuplesIn, cycTuples, mem_filter, mem_univ, true_and] at hf
  obtain ⟨⟨hinj, hadj⟩, hU⟩ := hf
  by_cases hv : ∃ p, f p = v
  · obtain ⟨p, hp⟩ := hv
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_univ _, ?_⟩
    set q₁ := succPos (by omega) p
    set q₂ := predPos (by omega) p
    have hq : q₁ ≠ q₂ := succ_ne_pred hk p
    have hp1 : p ≠ q₁ := (cyc_adj_succ hk p).ne
    have hp2 : p ≠ q₂ := (cyc_adj_pred hk p).ne
    have ha1 : G.Adj v (f q₁) := by rw [← hp]; exact (hadj _ _).2 (cyc_adj_succ hk p)
    have ha2 : G.Adj v (f q₂) := by rw [← hp]; exact (hadj _ _).2 (cyc_adj_pred hk p)
    have hn12 : ¬ G.Adj (f q₁) (f q₂) := fun h => not_cyc_adj_succ_pred hk p ((hadj _ _).1 h)
    have hne12 : f q₁ ≠ f q₂ := fun h => hq (hinj h)
    have hN1 : f q₁ ∈ neighborsIn G U v := by
      simp only [neighborsIn, mem_filter]; exact ⟨hU _, ha1⟩
    have hN2 : f q₂ ∈ neighborsIn G U v := by
      simp only [neighborsIn, mem_filter]; exact ⟨hU _, ha2⟩
    have hmemBox : ∀ q, p ≠ q → f q ∈ neighborsIn G U v \ C →
        f ∈ box p q v (neighborsIn G U v \ C) U := by
      intro q hpq hq
      simp only [box, Fintype.mem_piFinset]
      intro i
      by_cases hip : i = p
      · subst hip; simp [hp]
      · by_cases hiq : i = q
        · subst hiq; simp [hip, hq]
        · simp [hip, hiq, hU i]
    by_cases h1 : f q₁ ∈ C
    · by_cases h2 : f q₂ ∈ C
      · exact absurd (hC h1 h2 hne12) hn12
      · exact Finset.mem_union_right _ (hmemBox q₂ hp2 (Finset.mem_sdiff.2 ⟨hN2, h2⟩))
    · exact Finset.mem_union_left _ (hmemBox q₁ hp1 (Finset.mem_sdiff.2 ⟨hN1, h1⟩))
  · push_neg at hv
    apply Finset.mem_union_left
    simp only [cycTuplesIn, cycTuples, mem_filter, mem_univ, true_and]
    exact ⟨⟨hinj, hadj⟩, fun i => Finset.mem_erase.2 ⟨hv i, hU i⟩⟩

theorem card_cycTuplesIn_step {k : ℕ} (hk : 4 ≤ k) {s : ℕ} (U : Finset (Fin n)) (v : Fin n)
    (hv : DefectSimplicialOn G U s v) :
    (cycTuplesIn G k U).card ≤
      (cycTuplesIn G k (U.erase v)).card + k * (2 * (s * U.card ^ (k - 2))) := by
  obtain ⟨C, hCsub, hC, hcard⟩ := hv
  have hX : (neighborsIn G U v \ C).card ≤ s := by
    rw [Finset.card_sdiff_of_subset hCsub]; omega
  refine (Finset.card_le_card (cycTuplesIn_subset G hk U v C hC)).trans ?_
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  refine (Finset.card_biUnion_le).trans ?_
  have hb : ∀ p ∈ (univ : Finset (Fin k)),
      (box p (succPos (by omega) p) v (neighborsIn G U v \ C) U ∪
        box p (predPos (by omega) p) v (neighborsIn G U v \ C) U).card ≤
          2 * (s * U.card ^ (k - 2)) := by
    intro p _
    refine (Finset.card_union_le _ _).trans ?_
    have e1 := card_box_le p (succPos (by omega) p) (cyc_adj_succ hk p).ne v
      (neighborsIn G U v \ C) U
    have e2 := card_box_le p (predPos (by omega) p) (cyc_adj_pred hk p).ne v
      (neighborsIn G U v \ C) U
    have e3 : (neighborsIn G U v \ C).card * U.card ^ (k - 2) ≤ s * U.card ^ (k - 2) :=
      Nat.mul_le_mul_right _ hX
    omega
  refine (Finset.sum_le_sum hb).trans ?_
  simp

theorem pow_step (u k : ℕ) (hu : 1 ≤ u) (hk : 2 ≤ k) :
    (u - 1) ^ (k - 1) + u ^ (k - 2) ≤ u ^ (k - 1) := by
  have e : k - 1 = (k - 2) + 1 := by omega
  rw [e, pow_succ, pow_succ]
  have : (u - 1) ^ (k - 2) ≤ u ^ (k - 2) := Nat.pow_le_pow_left (Nat.sub_le u 1) _
  have h2 : (u - 1) ^ (k - 2) * (u - 1) ≤ u ^ (k - 2) * (u - 1) := Nat.mul_le_mul_right _ this
  have h3 : u ^ (k - 2) * (u - 1) + u ^ (k - 2) = u ^ (k - 2) * u := by
    obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
    simp [Nat.mul_succ]
  omega

/-- L1 on an arbitrary vertex set. -/
theorem card_cycTuplesIn_le {s : ℕ} (hG : RootedDefectAt G s) {k : ℕ} (hk : 4 ≤ k) :
    ∀ U : Finset (Fin n), (cycTuplesIn G k U).card ≤ 2 * k * s * U.card ^ (k - 1) := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    rcases U.eq_empty_or_nonempty with hU | hU
    · subst hU
      have : cycTuplesIn G k (∅ : Finset (Fin n)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro f hf
        simp only [cycTuplesIn, mem_filter] at hf
        exact Finset.notMem_empty _ (hf.2 ⟨0, by omega⟩)
      rw [this]; simp
    · obtain ⟨v, hvU, hv⟩ := hG U ∅ (Finset.empty_subset _) (by simp) (by simpa using hU)
      have hvU' : v ∈ U := (Finset.mem_sdiff.1 hvU).1
      have hstep := card_cycTuplesIn_step G hk U v hv
      have hih := ih (U.erase v) (Finset.erase_ssubset hvU')
      rw [Finset.card_erase_of_mem hvU'] at hih
      have hu : 1 ≤ U.card := Finset.card_pos.2 hU
      have hp := pow_step U.card k hu (by omega)
      have := Nat.mul_le_mul_left (2 * k * s) hp
      calc (cycTuplesIn G k U).card
          ≤ 2 * k * s * (U.card - 1) ^ (k - 1) + k * (2 * (s * U.card ^ (k - 2))) := by omega
        _ = 2 * k * s * ((U.card - 1) ^ (k - 1) + U.card ^ (k - 2)) := by ring
        _ ≤ 2 * k * s * U.card ^ (k - 1) := this

/-- **Lemma L1.** Under rooted defect `≤ s`, `indCopies (C_k) G ≤ 2·k·s·n^(k-1)` for `k ≥ 4`. -/
theorem indCopies_cycle_le {s : ℕ} (hG : RootedDefectAt G s) {k : ℕ} (hk : 4 ≤ k) :
    AlonShapira.indCopies (SimpleGraph.cycleGraph k) G ≤ 2 * k * s * n ^ (k - 1) := by
  rw [indCopies_eq_card_cycTuples]
  have h := card_cycTuplesIn_le G hG hk univ
  have e : cycTuplesIn G k univ = cycTuples G k := by
    unfold cycTuplesIn; simp
  rw [e, Finset.card_univ, Fintype.card_fin] at h
  exact h

end E34
