/-
Erdős (1964): dense k-partite k-graphs contain complete k-partite k-graphs `K^{(k)}(t,…,t)`.

Edges are tuples `f : Fin k → Fin n` (the k classes are k copies of `Fin n`). If `|E| ≥ δ n^k` and `n` is large
(depending on `k, t, δ`), there are parts `W i` of size `t` such that every transversal of `W` is an edge.

Proof by induction on `k`. For the last class, the prefixes `x` whose neighbourhood `N(x)` has at least `⌈δn/2⌉`
elements number at least `(δ/2) n^{k-1}`; double counting over the `t`-subsets `T` of the last class gives
`Σ_T |link T| = Σ_x C(|N x|, t)`, so some `T` has a common link of size `≥ (δ/2)(δ/4)^t n^{k-1}`, where the
binomial ratio uses `Nat.pow_le_choose` and `Nat.choose_le_pow_div`. The induction hypothesis in the link gives
the other parts.

Layer E (Mathlib only): axiom target = {propext, Classical.choice, Quot.sound}.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Positivity

namespace PaperIV.ErdosKPartite

open Finset

variable {n : ℕ}

/-- Every transversal of the parts `W` is an edge of `E`. -/
def Covers {k : ℕ} (E : Finset (Fin k → Fin n)) (W : Fin k → Finset (Fin n)) : Prop :=
  ∀ f : Fin k → Fin n, (∀ i, f i ∈ W i) → f ∈ E

/-- The neighbourhood of a prefix in the last class. -/
def nbhd {k : ℕ} (E : Finset (Fin (k + 1) → Fin n)) (x : Fin k → Fin n) : Finset (Fin n) :=
  univ.filter (fun v => (Fin.snoc (α := fun _ => Fin n) x v) ∈ E)

/-- The common link of a set `T` of last-class vertices. -/
def link {k : ℕ} (E : Finset (Fin (k + 1) → Fin n)) (T : Finset (Fin n)) : Finset (Fin k → Fin n) :=
  univ.filter (fun x => T ⊆ nbhd E x)

theorem card_le_sum_nbhd {k : ℕ} (E : Finset (Fin (k + 1) → Fin n)) :
    E.card ≤ ∑ x : Fin k → Fin n, (nbhd E x).card := by
  classical
  have hsub : E ⊆ univ.biUnion (fun x => (nbhd E x).image (Fin.snoc (α := fun _ => Fin n) x)) := by
    intro f hf
    rw [mem_biUnion]
    refine ⟨Fin.init f, mem_univ _, mem_image.mpr ⟨f (Fin.last k), ?_, Fin.snoc_init_self f⟩⟩
    simp only [nbhd, mem_filter, mem_univ, true_and]
    rw [Fin.snoc_init_self]
    exact hf
  calc E.card ≤ _ := card_le_card hsub
    _ ≤ ∑ x, ((nbhd E x).image (Fin.snoc (α := fun _ => Fin n) x)).card := card_biUnion_le
    _ ≤ ∑ x, (nbhd E x).card := sum_le_sum (fun x _ => card_image_le)

theorem sum_card_link {k : ℕ} (E : Finset (Fin (k + 1) → Fin n)) (t : ℕ) :
    ∑ T ∈ (univ : Finset (Fin n)).powersetCard t, (link E T).card =
      ∑ x : Fin k → Fin n, ((nbhd E x).card).choose t := by
  classical
  simp only [link, card_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun x _ => ?_)
  rw [← card_filter, ← card_powersetCard]
  congr 1
  ext T
  simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
  tauto

/-- The binomial ratio: `(δ/4)^t · C(n,t) ≤ C(a,t)` once `a ≥ δn/2` and `δn ≥ 4t`. -/
theorem choose_ratio {δ : ℝ} (hδ : 0 < δ) {a t : ℕ} (ha : δ * n / 2 ≤ a) (hnt : 4 * (t : ℝ) ≤ δ * n) :
    (δ / 4) ^ t * (n.choose t : ℝ) ≤ (a.choose t : ℝ) := by
  have h1 : (n.choose t : ℝ) ≤ (n : ℝ) ^ t / (t.factorial : ℝ) := Nat.choose_le_pow_div t n
  have h2 : (((a + 1 - t : ℕ) : ℝ) ^ t) / (t.factorial : ℝ) ≤ (a.choose t : ℝ) := Nat.pow_le_choose t a
  have hta : t ≤ a + 1 := by
    have : (t : ℝ) ≤ a := by nlinarith
    exact_mod_cast (show (t : ℝ) ≤ (a + 1 : ℕ) by push_cast; linarith)
  have hcast : (((a + 1 - t : ℕ) : ℝ)) = (a : ℝ) + 1 - t := by
    rw [Nat.cast_sub hta]; push_cast; ring
  have hbase : δ / 4 * n ≤ ((a + 1 - t : ℕ) : ℝ) := by rw [hcast]; nlinarith
  have hpos : 0 ≤ δ / 4 * n := by positivity
  have hpow : (δ / 4 * n) ^ t ≤ (((a + 1 - t : ℕ) : ℝ)) ^ t := pow_le_pow_left₀ hpos hbase t
  have hfac : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
  calc (δ / 4) ^ t * (n.choose t : ℝ) ≤ (δ / 4) ^ t * ((n : ℝ) ^ t / (t.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (δ / 4 * n) ^ t / (t.factorial : ℝ) := by rw [mul_pow]; ring
    _ ≤ (((a + 1 - t : ℕ) : ℝ)) ^ t / (t.factorial : ℝ) := div_le_div_of_nonneg_right hpow hfac.le
    _ ≤ _ := h2

/-- **Erdős's theorem for k-partite k-graphs.** -/
theorem erdos_kpartite (t : ℕ) : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
    ∀ E : Finset (Fin k → Fin n), δ * (n : ℝ) ^ k ≤ E.card →
      ∃ W : Fin k → Finset (Fin n), (∀ i, (W i).card = t) ∧ Covers E W := by
  intro k
  induction k with
  | zero =>
    intro δ hδ
    refine ⟨0, fun n _ E hE => ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩⟩
    intro f _
    have hpos : 0 < E.card := by
      have : (0 : ℝ) < E.card := by simp at hE; linarith
      exact_mod_cast this
    obtain ⟨g, hg⟩ := card_pos.mp hpos
    have : f = g := funext (fun i => i.elim0)
    rw [this]; exact hg
  | succ k ih =>
    intro δ hδ
    set δ' : ℝ := δ / 2 * (δ / 4) ^ t with hδ'
    have hδ'pos : 0 < δ' := by positivity
    obtain ⟨N', hN'⟩ := ih δ' hδ'pos
    refine ⟨max N' (⌈4 * (t : ℝ) / δ⌉₊ + t + 1), ?_⟩
    intro n hn E hE
    have hnN' : N' ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : ⌈4 * (t : ℝ) / δ⌉₊ + t + 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn1 : 1 ≤ n := by omega
    have htn : t ≤ n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnt : 4 * (t : ℝ) ≤ δ * n := by
      have h1 : 4 * (t : ℝ) / δ ≤ ⌈4 * (t : ℝ) / δ⌉₊ := Nat.le_ceil _
      have hc : ⌈4 * (t : ℝ) / δ⌉₊ ≤ n := by omega
      have h2 : ((⌈4 * (t : ℝ) / δ⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hc
      have h3 : 4 * (t : ℝ) / δ ≤ n := le_trans h1 h2
      rw [div_le_iff₀ hδ] at h3
      linarith
    -- the prefixes of large degree
    set a : ℕ := ⌈δ * n / 2⌉₊ with ha
    set X := (univ : Finset (Fin k → Fin n)).filter (fun x => a ≤ (nbhd E x).card) with hX
    have hcardX : δ / 2 * (n : ℝ) ^ k ≤ X.card := by
      have hsplit := (sum_filter_add_sum_filter_not (univ : Finset (Fin k → Fin n))
        (fun x => a ≤ (nbhd E x).card) (fun x => ((nbhd E x).card : ℝ)))
      have hin : ∑ x ∈ X, ((nbhd E x).card : ℝ) ≤ X.card * n := by
        have := sum_le_card_nsmul X (fun x => ((nbhd E x).card : ℝ)) n (fun x _ => by
          show ((nbhd E x).card : ℝ) ≤ n
          have : (nbhd E x).card ≤ n := by
            calc (nbhd E x).card ≤ (univ : Finset (Fin n)).card := card_le_univ _
              _ = n := by simp
          exact_mod_cast this)
        simpa using this
      have hout : ∑ x ∈ (univ : Finset (Fin k → Fin n)).filter (fun x => ¬ a ≤ (nbhd E x).card),
          ((nbhd E x).card : ℝ) ≤ (n : ℝ) ^ k * (δ * n / 2) := by
        have hb := sum_le_card_nsmul ((univ : Finset (Fin k → Fin n)).filter (fun x => ¬ a ≤ (nbhd E x).card))
          (fun x => ((nbhd E x).card : ℝ)) (δ * n / 2) (fun x hx => by
            show ((nbhd E x).card : ℝ) ≤ δ * n / 2
            have hlt : (nbhd E x).card < a := by simpa using (mem_filter.mp hx).2
            exact (Nat.lt_ceil.mp hlt).le)
        have hc : (((univ : Finset (Fin k → Fin n)).filter (fun x => ¬ a ≤ (nbhd E x).card)).card : ℝ) ≤
            (n : ℝ) ^ k := by
          have : ((univ : Finset (Fin k → Fin n)).filter (fun x => ¬ a ≤ (nbhd E x).card)).card ≤ n ^ k := by
            calc _ ≤ (univ : Finset (Fin k → Fin n)).card := card_filter_le _ _
              _ = n ^ k := by simp
          exact_mod_cast this
        simp only [nsmul_eq_mul] at hb
        have hdn : 0 ≤ δ * n / 2 := by positivity
        nlinarith
      have hE' : (E.card : ℝ) ≤ ∑ x : Fin k → Fin n, ((nbhd E x).card : ℝ) := by
        exact_mod_cast card_le_sum_nbhd E
      have hEk : δ * (n : ℝ) ^ (k + 1) ≤ X.card * n + (n : ℝ) ^ k * (δ * n / 2) := by
        rw [← hX] at hsplit; linarith
      have hpk : (n : ℝ) ^ (k + 1) = (n : ℝ) ^ k * n := pow_succ _ _
      rw [hpk] at hEk
      nlinarith
    -- double counting and pigeonhole over the `t`-subsets of the last class
    have hsumX : (X.card : ℝ) * (a.choose t : ℝ) ≤
        ∑ T ∈ (univ : Finset (Fin n)).powersetCard t, ((link E T).card : ℝ) := by
      have hlink := sum_card_link E t
      have hge : (X.card : ℝ) * (a.choose t : ℝ) ≤ ∑ x : Fin k → Fin n, (((nbhd E x).card).choose t : ℝ) := by
        calc (X.card : ℝ) * (a.choose t : ℝ) = ∑ x ∈ X, (a.choose t : ℝ) := by simp
          _ ≤ ∑ x ∈ X, (((nbhd E x).card).choose t : ℝ) := sum_le_sum (fun x hx => by
              exact_mod_cast Nat.choose_le_choose t (mem_filter.mp hx).2)
          _ ≤ ∑ x : Fin k → Fin n, (((nbhd E x).card).choose t : ℝ) :=
              sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
      have : (∑ T ∈ (univ : Finset (Fin n)).powersetCard t, ((link E T).card : ℝ)) =
          ∑ x : Fin k → Fin n, (((nbhd E x).card).choose t : ℝ) := by exact_mod_cast hlink
      linarith
    have hratio := choose_ratio (n := n) hδ (a := a) (t := t) (Nat.le_ceil _) hnt
    obtain ⟨T, hT, hTcard⟩ : ∃ T ∈ (univ : Finset (Fin n)).powersetCard t,
        δ' * (n : ℝ) ^ k ≤ (link E T).card := by
      by_contra hno
      push_neg at hno
      have hne : ((univ : Finset (Fin n)).powersetCard t).Nonempty :=
        powersetCard_nonempty.mpr (by simpa using htn)
      have hlt := sum_lt_sum_of_nonempty hne hno
      rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      have hA : 0 ≤ (a.choose t : ℝ) := by positivity
      have hkey : δ' * (n : ℝ) ^ k * (n.choose t : ℝ) ≤ (X.card : ℝ) * (a.choose t : ℝ) := by
        rw [hδ']
        have hnk : 0 ≤ (n : ℝ) ^ k := by positivity
        calc δ / 2 * (δ / 4) ^ t * (n : ℝ) ^ k * (n.choose t : ℝ)
            = δ / 2 * (n : ℝ) ^ k * ((δ / 4) ^ t * (n.choose t : ℝ)) := by ring
          _ ≤ δ / 2 * (n : ℝ) ^ k * (a.choose t : ℝ) :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
          _ ≤ (X.card : ℝ) * (a.choose t : ℝ) := mul_le_mul_of_nonneg_right hcardX hA
      linarith
    obtain ⟨hTsub, hTt⟩ := mem_powersetCard.mp hT
    obtain ⟨W', hW'card, hW'cov⟩ := hN' n hnN' (link E T) hTcard
    refine ⟨Fin.snoc (α := fun _ => Finset (Fin n)) W' T, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]; exact hTt
      · simp only [Fin.snoc_castSucc]; exact hW'card j
    · intro f hf
      have hx : Fin.init f ∈ link E T := hW'cov (Fin.init f) (fun j => by
        have := hf j.castSucc
        simpa [Fin.init, Fin.snoc_castSucc] using this)
      have hlast : f (Fin.last k) ∈ T := by
        have := hf (Fin.last k)
        simpa [Fin.snoc_last] using this
      have hmem := (mem_filter.mp hx).2 hlast
      simp only [nbhd, mem_filter, mem_univ, true_and, Fin.snoc_init_self] at hmem
      exact hmem

end PaperIV.ErdosKPartite
