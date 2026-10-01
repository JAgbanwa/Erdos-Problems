import PaperIV.SplitCompleteExactValueAllParities

/-!
# The unrestricted lower bound for complete-split clique partitions

The earlier exact-value theorem bounded partitions whose pieces have order at
most four.  Here the same baseline is proved for arbitrary clique partitions:
a clique contains at most one host, hence its cross edges cost at most one plus
its number of inner core edges.
-/

namespace PaperIV.SplitCompleteSharpLower

open Finset
open PaperIV.Model PaperIV.FarRounding PaperIV.SplitUniformIncidence
open PaperIV.SplitEdgeCount PaperIV.SplitPackingObstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem card_le_one_add_choose_two (c : ℕ) : c ≤ 1 + c.choose 2 := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      omega

/-- Filtered edge resources add exactly over a clique partition. -/
theorem sum_card_filter_pairs {G : SimpleGraph V} [DecidableRel G.Adj]
    (Q : CliquePartition G) (p : Sym2 V → Prop) [DecidablePred p] :
    ∑ K ∈ Q.pieces, ((pairs K).filter p).card = (G.edgeFinset.filter p).card := by
  rw [← Q.covers, Finset.filter_biUnion]
  symm
  apply Finset.card_biUnion
  intro K hK L hL hne
  exact Finset.disjoint_filter_filter (Q.edgeDisjoint K hK L hL hne)

/-- A clique of a complete split graph has at most one more cross edge than
inner core edges. -/
theorem card_crossPart_le_one_add_innerPart {Core Hosts s : Finset V}
    (hd : Disjoint Core Hosts)
    (hclique : (splitGraph Core Hosts).IsClique (s : Set V)) (htwo : 2 ≤ s.card) :
    (crossPart Core Hosts s).card ≤ 1 + (innerPart Core s).card := by
  by_cases hhost : s ∩ Hosts = ∅
  · rw [crossPart_eq_empty_of_no_host hhost]
    simp
  · obtain ⟨z, hz⟩ : ∃ z, z ∈ s ∩ Hosts := Finset.nonempty_iff_ne_empty.mpr hhost
    have hone : s ∩ Hosts = {z} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hz, ?_⟩
      intro x hx
      have hle := card_inter_hosts_le_one hd hclique
      rw [Finset.card_le_one] at hle
      exact hle x hx z hz
    rw [card_crossPart_of_host hd hone, innerPart_eq, card_pieceEdges]
    exact card_le_one_add_choose_two _

/-- The complete-split baseline is a lower bound for every clique partition,
with no restriction on the order of its pieces. -/
theorem cliquePartition_size_ge_baseline_unrestricted {Core Hosts : Finset V}
    (hd : Disjoint Core Hosts)
    (Q : CliquePartition (splitGraph Core Hosts)) :
    Core.card * Hosts.card - Core.card.choose 2 ≤ Q.size := by
  have hlocal : ∀ K ∈ Q.pieces,
      (crossPart Core Hosts K).card ≤ 1 + (innerPart Core K).card := by
    intro K hK
    exact card_crossPart_le_one_add_innerPart hd (Q.isClique K hK) (Q.two_le_card K hK)
  have hsum : ∑ K ∈ Q.pieces, (crossPart Core Hosts K).card ≤
      Q.size + ∑ K ∈ Q.pieces, (innerPart Core K).card := by
    calc
      ∑ K ∈ Q.pieces, (crossPart Core Hosts K).card
          ≤ ∑ K ∈ Q.pieces, (1 + (innerPart Core K).card) :=
            Finset.sum_le_sum fun K hK => hlocal K hK
      _ = Q.size + ∑ K ∈ Q.pieces, (innerPart Core K).card := by
        simp [CliquePartition.size, Finset.sum_add_distrib]
  have hcross : ∑ K ∈ Q.pieces, (crossPart Core Hosts K).card =
      (crossEdges Core Hosts).card := by
    have hf : (graphEdges (splitGraph Core Hosts)).filter
        (fun e => e ∈ crossEdges Core Hosts) = crossEdges Core Hosts :=
      by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨crossEdges_subset_graphEdges hd h, h⟩
    have h := sum_card_filter_pairs Q (fun e => e ∈ crossEdges Core Hosts)
    change ∑ K ∈ Q.pieces, (crossPart Core Hosts K).card =
      ((graphEdges (splitGraph Core Hosts)).filter
        (fun e => e ∈ crossEdges Core Hosts)).card at h
    rw [hf] at h
    exact h
  have hinner : ∑ K ∈ Q.pieces, (innerPart Core K).card =
      (pieceEdges Core).card := by
    have hf : (graphEdges (splitGraph Core Hosts)).filter
        (fun e => e ∈ pieceEdges Core) = pieceEdges Core :=
      by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨innerEdges_subset_graphEdges hd h, h⟩
    have h := sum_card_filter_pairs Q (fun e => e ∈ pieceEdges Core)
    change ∑ K ∈ Q.pieces, (innerPart Core K).card =
      ((graphEdges (splitGraph Core Hosts)).filter
        (fun e => e ∈ pieceEdges Core)).card at h
    rw [hf] at h
    exact h
  rw [hcross, hinner, card_crossEdges hd, card_pieceEdges] at hsum
  omega

/-- At the critical core size `⌊(n+1)/3⌋`, the complete-split baseline is the
Erdős target exactly. -/
theorem critical_baseline_eq_targetSize (n : ℕ) (hn : 2 ≤ n) :
    let k := (n + 1) / 3
    k * (n - k) - k.choose 2 = PaperIV.targetSize n := by
  let k := (n + 1) / 3
  let f := k * (n - k) - k.choose 2
  let q : ℚ := ((n * (n + 1) : ℕ) : ℚ) / 6
  have hkpos : 0 < k := by dsimp only [k]; omega
  have hkn : k ≤ n := by dsimp only [k]; omega
  have hkout : k ≤ n - k := by dsimp only [k]; omega
  have hchooseSquare : k.choose 2 ≤ k * k := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans
      (Nat.mul_le_mul_left k (Nat.sub_le k 1))
  have hchoose : k.choose 2 ≤ k * (n - k) :=
    hchooseSquare.trans (Nat.mul_le_mul_left k hkout)
  have hcast : (f : ℚ) =
      (k : ℚ) * ((n : ℚ) - k) - (k : ℚ) * ((k : ℚ) - 1) / 2 := by
    dsimp only [f]
    rw [Nat.cast_sub hchoose, Nat.cast_mul, Nat.cast_sub hkn,
      Nat.cast_choose_two]
  let r := (n + 1) % 3
  have hr : r < 3 := by dsimp only [r]; omega
  have hdivision : n + 1 = r + 3 * k := by
    dsimp only [r, k]
    omega
  have hdivisionQ : (n : ℚ) + 1 = r + 3 * k := by
    exact_mod_cast hdivision
  have hwindow : (f : ℚ) ≤ q ∧ q < (f : ℚ) + 1 := by
    rw [hcast]
    dsimp only [q]
    push_cast
    interval_cases r <;> norm_num at hdivisionQ <;>
      constructor <;> nlinarith [sq_nonneg ((k : ℚ) - 1)]
  have htarget : PaperIV.targetSize n = ⌊q⌋₊ := by
    unfold PaperIV.targetSize
    dsimp only [q]
    change n * (n + 1) / 6 = ⌊((n * (n + 1) : ℕ) : ℚ) / (6 : ℕ)⌋₊
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hfloor : ⌊q⌋₊ = f :=
    (Nat.floor_eq_iff (show 0 ≤ q by dsimp only [q]; positivity)).2 hwindow
  exact hfloor.symm.trans htarget.symm

end PaperIV.SplitCompleteSharpLower
