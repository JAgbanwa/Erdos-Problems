/-
# The greedy iteration: a *sparse pair-covering reservoir* in a dense host.

This file carries out the greedy iteration built on the deterministic averaging step
`BKLO.exists_hub_star_capturing` of `BKLO/PairCovering.lean`.

The result (`BKLO.exists_sparse_pairCovering`) is:

> for every `γ > 0` and every `K` there is a threshold beyond which every host `E ⊆ cliqueEdges S`
> of minimum degree at least `(9/10 + γ)|S|` contains a subgraph `R ⊆ E` of maximum degree at most
> `γ|S|` in which **every** pair of distinct vertices of `S` has at least `K` common neighbours.

The construction is a greedy iteration of hub stars.  At each round one picks, by the averaging
lemma, a fresh hub `z` (never used as a hub before) and a star `D` of prescribed size `k ≈ |S|/m`
inside the not-yet-reserved neighbourhood of `z`, capturing at least the average number of the
pairs that still lack `K` reserved common neighbours; the star `{z} × D` is added to the reservoir.
Since the hub is fresh and the star avoids already reserved edges, every captured pair gains a
*new* common reserved neighbour, so the potential

  `pot K R S = ∑_{e ⊆ S} (K − #(reserved common neighbours of e))`

drops by the number of captured pairs.  The averaging inequality turns this into a fixed
multiplicative decay `q · pot(R') ≤ (q−1) · pot(R)` with `q` a constant depending only on `γ` and
`K`, so `q · (log₂ (K|S|²) + 1)` rounds suffice.  Each round costs degree `1` at each vertex of the
star and degree `k` at the (fresh) hub, so the final maximum degree is at most
`(number of rounds) + k ≤ γ|S|`.

Everything here is `sorry`-free.
-/
import BKLO.PairCovering
import BKLO.ApexCover

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Arithmetic preliminaries -/

/-- `q^q ≥ 2 (q−1)^q` for `q ≥ 2`: a geometric decay of ratio `(q−1)/q` halves in `q` steps. -/
theorem two_mul_pred_pow_le (q : ℕ) (hq : 2 ≤ q) : 2 * (q - 1) ^ q ≤ q ^ q := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  have hgoal : (2 : ℝ) * ((p : ℝ) + 1) ^ (p + 2) ≤ ((p : ℝ) + 2) ^ (p + 2) := by
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have hber := one_add_mul_le_pow (a := 1 / ((p : ℝ) + 1)) (by
      have : (0 : ℝ) ≤ 1 / ((p : ℝ) + 1) := by positivity
      linarith) (p + 2)
    push_cast at hber
    have hkey : ((p : ℝ) + 2) * (1 / ((p : ℝ) + 1)) = ((p : ℝ) + 2) / ((p : ℝ) + 1) := by ring
    have h1' : (1 : ℝ) ≤ ((p : ℝ) + 2) / ((p : ℝ) + 1) := by
      rw [le_div_iff₀ hp1]; linarith only []
    have h2 : (2 : ℝ) ≤ 1 + ((p : ℝ) + 2) * (1 / ((p : ℝ) + 1)) := by
      rw [hkey]; linarith only [h1']
    have h3 : (2 : ℝ) ≤ (1 + 1 / ((p : ℝ) + 1)) ^ (p + 2) := le_trans h2 hber
    have h4 : (1 + 1 / ((p : ℝ) + 1)) = ((p : ℝ) + 2) / ((p : ℝ) + 1) := by
      field_simp; ring
    rw [h4, div_pow, le_div_iff₀ (by positivity)] at h3
    linarith only [h3]
  have := hgoal
  push_cast at this ⊢
  exact_mod_cast this

/-- Iterating the halving: `2^j · (q−1)^(q j) ≤ q^(q j)`. -/
theorem pow_decay (q : ℕ) (hq : 2 ≤ q) : ∀ j : ℕ, 2 ^ j * (q - 1) ^ (q * j) ≤ q ^ (q * j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : 2 * (q - 1) ^ q ≤ q ^ q := two_mul_pred_pow_le q hq
    calc 2 ^ (j + 1) * (q - 1) ^ (q * (j + 1))
        = (2 * (q - 1) ^ q) * (2 ^ j * (q - 1) ^ (q * j)) := by
          rw [Nat.mul_succ, pow_add]; ring
      _ ≤ (q ^ q) * (q ^ (q * j)) := Nat.mul_le_mul hstep ih
      _ = q ^ (q * (j + 1)) := by rw [Nat.mul_succ, pow_add]; ring

/-- `(log₂ n)² ≤ 4 n`. -/
theorem log_two_sq_le (n : ℕ) : Nat.log 2 n * Nat.log 2 n ≤ 4 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have key : ∀ L : ℕ, L * L ≤ 4 * 2 ^ L := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      have hL : L < 2 ^ L := Nat.lt_two_pow_self
      calc (L + 1) * (L + 1) = L * L + (2 * L + 1) := by ring
        _ ≤ 4 * 2 ^ L + (2 * L + 1) := by omega
        _ ≤ 4 * 2 ^ L + 4 * 2 ^ L := by omega
        _ = 4 * 2 ^ (L + 1) := by ring
  exact le_trans (key (Nat.log 2 n)) (by omega)

/-- For `n` large, `c · (log₂ n + 1) ≤ n`: the number of greedy rounds is logarithmic, hence far
below the linear degree budget. -/
theorem mul_log_le_self {c n : ℕ} (hc : 1 ≤ c) (hn : 400 * c * c ≤ n) :
    c * (Nat.log 2 n + 1) ≤ n := by
  set L := Nat.log 2 n with hL
  have hsq : L * L ≤ 4 * n := log_two_sq_le n
  by_contra hcon
  push_neg at hcon
  have h1 : n < c * (L + 1) := hcon
  have hn0 : 0 < n := by nlinarith only [hc, hn]
  have hL1 : 1 ≤ L := by
    by_contra h
    have hL0 : L = 0 := by omega
    rw [hL0] at h1
    nlinarith only [hn, h1]
  have h2 : n < 2 * c * L := by nlinarith only [h1, hL1]
  nlinarith only [hsq, h2, hn]

/-! ### The reservoir statistics -/

/-- The reserved common neighbours of the endpoints of `e` inside `S` — the *apexes* available for
the pair `e`. -/
def apexSet (R : Finset (Sym2 V)) (S : Finset V) (e : Sym2 V) : Finset V :=
  S.filter (fun z => ∀ u ∈ e.toFinset, s(u, z) ∈ R)

/-- How many further apexes the pair `e` needs. -/
def defic (K : ℕ) (R : Finset (Sym2 V)) (S : Finset V) (e : Sym2 V) : ℕ :=
  K - (apexSet R S e).card

/-- The potential driving the greedy iteration: the total deficiency over all pairs. -/
def pot (K : ℕ) (R : Finset (Sym2 V)) (S : Finset V) : ℕ :=
  ∑ e ∈ cliqueEdges S, defic K R S e

/-- The pairs that still need apexes. -/
def deficSet (K : ℕ) (R : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) :=
  (cliqueEdges S).filter (fun e => (apexSet R S e).card < K)

/-- The reserved neighbours of `x` inside `S`. -/
def resNbhd (R : Finset (Sym2 V)) (S : Finset V) (x : V) : Finset V :=
  S.filter (fun z => s(x, z) ∈ R)

theorem card_resNbhd_le (R : Finset (Sym2 V)) (S : Finset V) (x : V) :
    (resNbhd R S x).card ≤ edeg R x := by
  classical
  refine Finset.card_le_card_of_injOn (fun z => s(x, z)) ?_ ?_
  · intro z hz
    simp only [Finset.coe_filter, Set.mem_setOf_eq, resNbhd] at hz ⊢
    exact ⟨hz.2, by simp⟩
  · intro z _ z' _ h
    rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact h2.trans h1

/-- Monotonicity of the apex sets. -/
theorem apexSet_mono {R R' : Finset (Sym2 V)} (h : R ⊆ R') (S : Finset V) (e : Sym2 V) :
    apexSet R S e ⊆ apexSet R' S e := by
  intro z hz
  rw [apexSet, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, fun u hu => h (hz.2 u hu)⟩

theorem defic_mono {K : ℕ} {R R' : Finset (Sym2 V)} (h : R ⊆ R') (S : Finset V) (e : Sym2 V) :
    defic K R' S e ≤ defic K R S e :=
  Nat.sub_le_sub_left (Finset.card_le_card (apexSet_mono h S e)) _

/-! ### The invariant maintained by the greedy iteration -/

/-- The invariant of the greedy construction after `t` rounds with stars of size `k`: the reservoir
lies in the host, the hubs used so far are at most `t` vertices of `S`, every non-hub has degree at
most `t` and every vertex has degree at most `t + k`. -/
structure GreedyInv (E : Finset (Sym2 V)) (S : Finset V) (k t : ℕ)
    (R : Finset (Sym2 V)) (Hb : Finset V) : Prop where
  sub : R ⊆ E
  hbS : Hb ⊆ S
  hbcard : Hb.card ≤ t
  degOut : ∀ v, v ∉ Hb → edeg R v ≤ t
  deg : ∀ v, edeg R v ≤ t + k

theorem GreedyInv.mono {E : Finset (Sym2 V)} {S : Finset V} {k t t' : ℕ} {R : Finset (Sym2 V)}
    {Hb : Finset V} (h : GreedyInv E S k t R Hb) (htt : t ≤ t') : GreedyInv E S k t' R Hb :=
  ⟨h.sub, h.hbS, le_trans h.hbcard htt, fun v hv => le_trans (h.degOut v hv) htt,
    fun v => le_trans (h.deg v) (by omega)⟩

/-- Gaining a new apex strictly decreases the deficiency of a pair that still needs apexes. -/
theorem defic_succ_le {K : ℕ} {R R' : Finset (Sym2 V)} {S : Finset V} {e : Sym2 V} {z : V}
    (hRR : R ⊆ R') (hz : z ∈ apexSet R' S e) (hznot : z ∉ apexSet R S e)
    (hdef : (apexSet R S e).card < K) : defic K R' S e + 1 ≤ defic K R S e := by
  have hsub : insert z (apexSet R S e) ⊆ apexSet R' S e := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hz
    · exact apexSet_mono hRR S e hw
  have hcard : (apexSet R S e).card + 1 ≤ (apexSet R' S e).card := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem hznot] at h
  unfold defic
  omega

/-- The potential is at most `K` times the number of deficient pairs. -/
theorem pot_le_card_deficSet (K : ℕ) (R : Finset (Sym2 V)) (S : Finset V) :
    pot K R S ≤ K * (deficSet K R S).card := by
  classical
  have h : pot K R S = ∑ e ∈ deficSet K R S, defic K R S e := by
    rw [pot, deficSet, ← Finset.sum_filter_ne_zero]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext e
    simp only [Finset.mem_filter, defic, ne_eq]
    constructor
    · rintro ⟨he, hlt⟩; exact ⟨he, by omega⟩
    · rintro ⟨he, hne⟩; exact ⟨he, by omega⟩
  rw [h, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  have := (Finset.mem_filter.1 he).2
  simp only [defic]
  omega

/-! ### Stars -/

/-- The star at `z` with leaves `D`. -/
def star (z : V) (D : Finset V) : Finset (Sym2 V) := D.image (fun d => s(z, d))

theorem mem_star {z : V} {D : Finset V} {d : V} (hd : d ∈ D) : s(z, d) ∈ star z D :=
  Finset.mem_image.2 ⟨d, hd, rfl⟩

theorem edeg_star_le (z : V) (D : Finset V) (v : V) : edeg (star z D) v ≤ D.card := by
  classical
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
  exact Finset.card_image_le

theorem edeg_star_le_one {z v : V} (D : Finset V) (h : v ≠ z) : edeg (star z D) v ≤ 1 := by
  classical
  have hsub : (star z D).filter (fun e => v ∈ e) ⊆ {s(z, v)} := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 he.1
    have := he.2
    rw [Sym2.mem_iff] at this
    rcases this with rfl | rfl
    · exact absurd rfl h
    · simp
  have := Finset.card_le_card hsub
  simpa [edeg] using this

/-! ### One greedy round -/

/-- **One round of the greedy construction.**  Given a reservoir satisfying the invariant after `t`
rounds, one more hub star can be reserved, and the potential decays by the fixed factor
`(q−1)/q`. -/
theorem greedy_round
    {E : Finset (Sym2 V)} {S : Finset V} {K k t a q Tm : ℕ}
    (hk : 2 ≤ k) (hq : 1 ≤ q) (hapos : 0 < a)
    (hcn : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ W : Finset V, W.card ≤ 3 * Tm + 2 * k →
        a ≤ ((nbhdIn E x S ∩ nbhdIn E y S) \ W).card)
    (hnb : ∀ z ∈ S, 2 * k + Tm ≤ (nbhdIn E z S).card)
    (hZlt : Tm < S.card)
    (hqbig : K * (S.card * (S.card * S.card)) ≤ q * (a * (k * (k - 1))))
    {R : Finset (Sym2 V)} {Hb : Finset V}
    (hinv : GreedyInv E S k t R Hb) (ht : t ≤ Tm) :
    ∃ (R' : Finset (Sym2 V)) (Hb' : Finset V), GreedyInv E S k (t + 1) R' Hb' ∧ R ⊆ R' ∧
      q * pot K R' S ≤ (q - 1) * pot K R S := by
  classical
  set Z : Finset V := S \ Hb with hZdef
  set nb : V → Finset V := fun z => (nbhdIn E z S).filter (fun x => s(z, x) ∉ R) with hnbdef
  set U : Finset (Sym2 V) := deficSet K R S with hUdef
  set C : Sym2 V → Finset V := fun e => Z.filter (fun z => ∀ u ∈ e.toFinset, u ∈ nb z) with hCdef
  have hZS : Z ⊆ S := Finset.sdiff_subset
  have hZne : Z.Nonempty := by
    rw [← Finset.card_pos, hZdef]
    have hcs : (S \ Hb).card + Hb.card = S.card := Finset.card_sdiff_add_card_eq_card hinv.hbS
    have : Hb.card ≤ Tm := le_trans hinv.hbcard ht
    omega
  -- every deficient pair has many admissible hubs
  have hsize : ∀ e ∈ U, a ≤ (C e).card := by
    intro e he
    have heC : e ∈ cliqueEdges S := (Finset.mem_filter.1 he).1
    revert heC
    induction e using Sym2.ind with
    | _ x y =>
      intro heC
      have hx : x ∈ S := (mem_cliqueEdgesV.1 heC).1 x (by simp)
      have hy : y ∈ S := (mem_cliqueEdgesV.1 heC).1 y (by simp)
      have hxy : x ≠ y := by
        have := (mem_cliqueEdgesV.1 heC).2
        simpa [Sym2.isDiag_iff_proj_eq] using this
      set W : Finset V := Hb ∪ (resNbhd R S x ∪ resNbhd R S y) with hWdef
      have hWcard : W.card ≤ 3 * Tm + 2 * k := by
        have h1 : W.card ≤ Hb.card + (resNbhd R S x).card + (resNbhd R S y).card := by
          refine le_trans (Finset.card_union_le _ _) ?_
          have := Finset.card_union_le (resNbhd R S x) (resNbhd R S y)
          omega
        have h2 : Hb.card ≤ Tm := le_trans hinv.hbcard ht
        have h3 : (resNbhd R S x).card ≤ Tm + k :=
          le_trans (card_resNbhd_le R S x) (le_trans (hinv.deg x) (by omega))
        have h4 : (resNbhd R S y).card ≤ Tm + k :=
          le_trans (card_resNbhd_le R S y) (le_trans (hinv.deg y) (by omega))
        omega
      have hsub : (nbhdIn E x S ∩ nbhdIn E y S) \ W ⊆ C s(x, y) := by
        intro z hz
        rw [Finset.mem_sdiff, Finset.mem_inter] at hz
        obtain ⟨⟨hzx, hzy⟩, hzW⟩ := hz
        have hzS : z ∈ S := (Finset.mem_filter.1 hzx).1
        have hzHb : z ∉ Hb := fun h => hzW (Finset.mem_union_left _ h)
        have hzrx : z ∉ resNbhd R S x := fun h =>
          hzW (Finset.mem_union_right _ (Finset.mem_union_left _ h))
        have hzry : z ∉ resNbhd R S y := fun h =>
          hzW (Finset.mem_union_right _ (Finset.mem_union_right _ h))
        have hxE : s(x, z) ∈ E := (Finset.mem_filter.1 hzx).2
        have hyE : s(y, z) ∈ E := (Finset.mem_filter.1 hzy).2
        have hxR : s(x, z) ∉ R := fun h => hzrx (Finset.mem_filter.2 ⟨hzS, h⟩)
        have hyR : s(y, z) ∉ R := fun h => hzry (Finset.mem_filter.2 ⟨hzS, h⟩)
        rw [hCdef]
        refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hzS, hzHb⟩, ?_⟩
        intro u hu
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hu
        rcases hu with rfl | rfl
        · refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hx, ?_⟩, ?_⟩
          · rwa [Sym2.eq_swap]
          · rw [Sym2.eq_swap]; exact hxR
        · refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hy, ?_⟩, ?_⟩
          · rwa [Sym2.eq_swap]
          · rw [Sym2.eq_swap]; exact hyR
      exact le_trans (hcn x hx y hy hxy W hWcard) (Finset.card_le_card hsub)
  have hC : ∀ e ∈ U, C e ⊆ Z := fun e _ => Finset.filter_subset _ _
  have hnd : ∀ e ∈ U, ¬ e.IsDiag := by
    intro e he
    exact (mem_cliqueEdgesV.1 (Finset.mem_filter.1 he).1).2
  have hmem : ∀ e ∈ U, ∀ z ∈ C e, ∀ v ∈ e, v ∈ nb z := by
    intro e _ z hz v hv
    exact (Finset.mem_filter.1 hz).2 v (Sym2.mem_toFinset.2 hv)
  have hkN : ∀ z ∈ Z, k ≤ (nb z).card := by
    intro z hz
    have hzS : z ∈ S := hZS hz
    have h1 : 2 * k + Tm ≤ (nbhdIn E z S).card := hnb z hzS
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := nbhdIn E z S) (p := fun x => s(z, x) ∉ R)
    have h2 : ((nbhdIn E z S).filter (fun x => ¬ (s(z, x) ∉ R))).card ≤ Tm + k := by
      refine le_trans (Finset.card_le_card ?_) (le_trans (card_resNbhd_le R S z)
        (le_trans (hinv.deg z) (by omega)))
      intro x hx
      rw [Finset.mem_filter] at hx
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx.1).1, by simpa using hx.2⟩
    have : (nb z).card + ((nbhdIn E z S).filter (fun x => ¬ (s(z, x) ∉ R))).card
        = (nbhdIn E z S).card := by
      rw [hnbdef]; exact hsplit
    omega
  obtain ⟨z, hzZ, D, hD, hineq⟩ :=
    exists_hub_star_capturing Z U C nb a hk hZne hC hsize hnd hmem hkN
  rw [Finset.mem_powersetCard] at hD
  obtain ⟨hDnb, hDcard⟩ := hD
  set X : Finset (Sym2 V) := star z D with hXdef
  set R' : Finset (Sym2 V) := R ∪ X with hR'def
  have hzS : z ∈ S := hZS hzZ
  have hzHb : z ∉ Hb := (Finset.mem_sdiff.1 hzZ).2
  have hRR' : R ⊆ R' := Finset.subset_union_left
  -- invariants
  have hXE : X ⊆ E := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 he
    have := hDnb hd
    rw [hnbdef, Finset.mem_filter] at this
    exact (Finset.mem_filter.1 this.1).2
  have hdeg' : ∀ v, edeg R' v ≤ edeg R v + edeg X v := fun v => edeg_union_le R X v
  have hinv' : GreedyInv E S k (t + 1) R' (insert z Hb) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.union_subset hinv.sub hXE
    · exact Finset.insert_subset hzS hinv.hbS
    · refine le_trans (Finset.card_insert_le _ _) ?_
      have := hinv.hbcard; omega
    · intro v hv
      have hvz : v ≠ z := fun h => hv (by rw [h]; exact Finset.mem_insert_self _ _)
      have hvHb : v ∉ Hb := fun h => hv (Finset.mem_insert_of_mem h)
      have h1 := hinv.degOut v hvHb
      have h2 : edeg X v ≤ 1 := edeg_star_le_one D hvz
      have := hdeg' v; omega
    · intro v
      have hXk : edeg X v ≤ k := by rw [hXdef, ← hDcard]; exact edeg_star_le z D v
      by_cases hvz : v = z
      · have h1 : edeg R v ≤ t := by rw [hvz]; exact hinv.degOut z hzHb
        have := hdeg' v; omega
      · have h1 := hinv.deg v
        have h2 : edeg X v ≤ 1 := edeg_star_le_one D hvz
        have := hdeg' v; omega
  refine ⟨R', insert z Hb, hinv', hRR', ?_⟩
  -- the potential drops by the number of captured pairs
  set Cap : Finset (Sym2 V) := U.filter (fun e : Sym2 V => e.toFinset ⊆ D) with hCapdef
  have hcapture : pot K R' S + Cap.card ≤ pot K R S := by
    have hstep : ∀ e ∈ cliqueEdges S,
        defic K R' S e + (if e ∈ Cap then 1 else 0) ≤ defic K R S e := by
      intro e he
      by_cases hcap : e ∈ Cap
      · rw [if_pos hcap]
        have heU : e ∈ U := (Finset.mem_filter.1 hcap).1
        have heD : e.toFinset ⊆ D := (Finset.mem_filter.1 hcap).2
        have hdefk : (apexSet R S e).card < K := (Finset.mem_filter.1 heU).2
        have hzin : z ∈ apexSet R' S e := by
          refine Finset.mem_filter.2 ⟨hzS, ?_⟩
          intro u hu
          have : s(z, u) ∈ X := mem_star (heD hu)
          rw [Sym2.eq_swap]
          exact Finset.mem_union_right _ this
        have hznot : z ∉ apexSet R S e := by
          have hne : e.toFinset.Nonempty := by
            have := hnd e heU
            induction e using Sym2.ind with
            | _ x y => exact ⟨x, by simp⟩
          obtain ⟨u, hu⟩ := hne
          have hunb : u ∈ nb z := hDnb (heD hu)
          rw [hnbdef, Finset.mem_filter] at hunb
          intro hcon
          have := (Finset.mem_filter.1 hcon).2 u hu
          rw [Sym2.eq_swap] at this
          exact hunb.2 this
        exact defic_succ_le hRR' hzin hznot hdefk
      · rw [if_neg hcap, add_zero]
        exact defic_mono hRR' S e
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib] at hsum
    have hcount : ∑ e ∈ cliqueEdges S, (if e ∈ Cap then 1 else 0) = Cap.card := by
      rw [Finset.sum_ite_mem]
      have hCS : Cap ⊆ cliqueEdges S := by
        intro e he
        exact (Finset.mem_filter.1 (Finset.mem_filter.1 he).1).1
      rw [Finset.inter_eq_right.2 hCS]
      simp
    rw [hcount] at hsum
    exact hsum
  -- the averaging inequality gives `pot ≤ q * Cap.card`
  have hAB : pot K R S ≤ q * Cap.card := by
    have hApos : 0 < a * (k * (k - 1)) := by
      have : 0 < k * (k - 1) := by
        have : 2 ≤ k := hk
        exact Nat.mul_pos (by omega) (by omega)
      exact Nat.mul_pos hapos this
    have hZcard : Z.card ≤ S.card := Finset.card_le_card hZS
    have hnbcard : (nb z).card ≤ S.card := by
      refine Finset.card_le_card ?_
      intro x hx
      rw [hnbdef, Finset.mem_filter] at hx
      exact (Finset.mem_filter.1 hx.1).1
    have hRHS : Cap.card * (Z.card * ((nb z).card * ((nb z).card - 1)))
        ≤ Cap.card * (S.card * (S.card * S.card)) := by
      refine Nat.mul_le_mul_left _ (Nat.mul_le_mul hZcard (Nat.mul_le_mul hnbcard ?_))
      omega
    have h1 : U.card * (a * (k * (k - 1))) ≤ Cap.card * (S.card * (S.card * S.card)) :=
      le_trans hineq hRHS
    have h2 : pot K R S * (a * (k * (k - 1))) ≤ (q * Cap.card) * (a * (k * (k - 1))) := by
      calc pot K R S * (a * (k * (k - 1)))
          ≤ (K * U.card) * (a * (k * (k - 1))) :=
            Nat.mul_le_mul_right _ (pot_le_card_deficSet K R S)
        _ = K * (U.card * (a * (k * (k - 1)))) := by ring
        _ ≤ K * (Cap.card * (S.card * (S.card * S.card))) := Nat.mul_le_mul_left _ h1
        _ = Cap.card * (K * (S.card * (S.card * S.card))) := by ring
        _ ≤ Cap.card * (q * (a * (k * (k - 1)))) := Nat.mul_le_mul_left _ hqbig
        _ = (q * Cap.card) * (a * (k * (k - 1))) := by ring
    exact Nat.le_of_mul_le_mul_right h2 hApos
  -- conclude
  have hmul : q * pot K R' S + q * Cap.card ≤ q * pot K R S := by
    have := Nat.mul_le_mul_left q hcapture
    calc q * pot K R' S + q * Cap.card = q * (pot K R' S + Cap.card) := by ring
      _ ≤ q * pot K R S := this
  have hfin : q * pot K R' S + pot K R S ≤ q * pot K R S :=
    le_trans (Nat.add_le_add_left hAB _) hmul
  have hqm : (q - 1) * pot K R S = q * pot K R S - pot K R S := by
    cases q with
    | zero => omega
    | succ q' => simp [Nat.succ_mul]
  rw [hqm]
  omega

/-! ### Iterating the rounds -/

/-- **The greedy iteration.**  After `i` rounds the potential has decayed by the factor
`((q−1)/q)^i`. -/
theorem greedy_iterate
    {E : Finset (Sym2 V)} {S : Finset V} {K k a q Tm : ℕ}
    (hk : 2 ≤ k) (hq : 1 ≤ q) (hapos : 0 < a)
    (hcn : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ W : Finset V, W.card ≤ 3 * Tm + 2 * k →
        a ≤ ((nbhdIn E x S ∩ nbhdIn E y S) \ W).card)
    (hnb : ∀ z ∈ S, 2 * k + Tm ≤ (nbhdIn E z S).card)
    (hZlt : Tm < S.card)
    (hqbig : K * (S.card * (S.card * S.card)) ≤ q * (a * (k * (k - 1)))) :
    ∀ i : ℕ, i ≤ Tm → ∃ (R : Finset (Sym2 V)) (Hb : Finset V), GreedyInv E S k i R Hb ∧
      q ^ i * pot K R S ≤ (q - 1) ^ i * pot K (∅ : Finset (Sym2 V)) S := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨∅, ∅, ⟨Finset.empty_subset _, Finset.empty_subset _, by simp, ?_, ?_⟩, by simp⟩
    · intro v _; simp [edeg]
    · intro v; simp [edeg]
  | succ i ih =>
    intro hi
    obtain ⟨R, Hb, hinv, hdec⟩ := ih (by omega)
    obtain ⟨R', Hb', hinv', _, hstep⟩ :=
      greedy_round hk hq hapos hcn hnb hZlt hqbig hinv (by omega)
    refine ⟨R', Hb', hinv', ?_⟩
    calc q ^ (i + 1) * pot K R' S = q ^ i * (q * pot K R' S) := by ring
      _ ≤ q ^ i * ((q - 1) * pot K R S) := Nat.mul_le_mul_left _ hstep
      _ = (q - 1) * (q ^ i * pot K R S) := by ring
      _ ≤ (q - 1) * ((q - 1) ^ i * pot K (∅ : Finset (Sym2 V)) S) := Nat.mul_le_mul_left _ hdec
      _ = (q - 1) ^ (i + 1) * pot K (∅ : Finset (Sym2 V)) S := by ring

/-! ### The pair-covering reservoir, in natural-number form -/

/-- **A sparse pair-covering reservoir (arithmetic form).**  Under the stated counting hypotheses
the greedy iteration terminates with a reservoir of maximum degree at most `Tm + k` in which every
pair of `S` has at least `K` reserved common neighbours. -/
theorem exists_pairCovering_nat
    {E : Finset (Sym2 V)} {S : Finset V} {K k a q Tm : ℕ}
    (hk : 2 ≤ k) (hq : 2 ≤ q) (hapos : 0 < a)
    (hcn : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ W : Finset V, W.card ≤ 3 * Tm + 2 * k →
        a ≤ ((nbhdIn E x S ∩ nbhdIn E y S) \ W).card)
    (hnb : ∀ z ∈ S, 2 * k + Tm ≤ (nbhdIn E z S).card)
    (hZlt : Tm < S.card)
    (hqbig : K * (S.card * (S.card * S.card)) ≤ q * (a * (k * (k - 1))))
    (hTm : q * (Nat.log 2 (pot K (∅ : Finset (Sym2 V)) S) + 1) ≤ Tm) :
    ∃ R : Finset (Sym2 V), R ⊆ E ∧ (∀ v, edeg R v ≤ Tm + k) ∧
      ∀ e ∈ cliqueEdges S, K ≤ (apexSet R S e).card := by
  classical
  set M := pot K (∅ : Finset (Sym2 V)) S with hM
  set j := Nat.log 2 M + 1 with hj
  set T := q * j with hT
  obtain ⟨R, Hb, hinv, hdec⟩ :=
    greedy_iterate hk (by omega) hapos hcn hnb hZlt hqbig T (by omega)
  have hMlt : M < 2 ^ j := Nat.lt_pow_succ_log_self (by norm_num) M
  have hpos : 0 < (q - 1) ^ T := Nat.pow_pos (by omega)
  have hlt : (q - 1) ^ T * M < q ^ T := by
    calc (q - 1) ^ T * M < (q - 1) ^ T * 2 ^ j := mul_lt_mul_of_pos_left hMlt hpos
      _ = 2 ^ j * (q - 1) ^ (q * j) := by rw [hT]; ring
      _ ≤ q ^ (q * j) := pow_decay q hq j
      _ = q ^ T := by rw [hT]
  have hpot : pot K R S = 0 := by
    by_contra hne
    have h2 : q ^ T ≤ q ^ T * pot K R S := Nat.le_mul_of_pos_right _ (by omega)
    exact absurd (lt_of_le_of_lt hdec hlt) (not_lt.2 h2)
  refine ⟨R, hinv.sub, fun v => le_trans (hinv.deg v) (by omega), ?_⟩
  intro e he
  have hz : defic K R S e = 0 := by
    have := (Finset.sum_eq_zero_iff (f := fun e => defic K R S e)
      (s := cliqueEdges S)).1 hpot e he
    exact this
  simp only [defic] at hz
  omega

/-! ### The pair-covering reservoir in a dense host -/

theorem pot_empty_le (K : ℕ) (S : Finset V) :
    pot K (∅ : Finset (Sym2 V)) S ≤ K * (S.card * S.card) := by
  classical
  have h1 : pot K (∅ : Finset (Sym2 V)) S ≤ K * (cliqueEdges S).card := by
    rw [pot, Finset.card_eq_sum_ones, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    simp only [defic]
    omega
  have h2 : (cliqueEdges S).card ≤ S.card * S.card := by
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    rw [Finset.card_sym2, Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos S.card with h | h
    · simp [h]
    · exact Nat.div_le_of_le_mul (by nlinarith)
  exact le_trans h1 (Nat.mul_le_mul_left _ h2)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **A sparse pair-covering reservoir in a dense host** (the case of small `γ`).  See
`BKLO.exists_sparse_pairCovering` for the statement without the restriction on `γ`. -/
theorem exists_sparse_pairCovering_small {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1 / 20) (K : ℕ) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ R : Finset (Sym2 V), R ⊆ E ∧ (∀ v : V, (edeg R v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ e ∈ cliqueEdges S, K ≤ (apexSet R S e).card := by
  classical
  set m : ℕ := ⌈(4 : ℝ) / γ⌉₊ + 1 with hmdef
  have hmpos : 0 < m := by omega
  have hmγ : (4 : ℝ) ≤ γ * m := by
    have h1 : (4 / γ : ℝ) ≤ (⌈(4 : ℝ) / γ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (4 / γ : ℝ) ≤ (m : ℝ) := by
      rw [hmdef]; push_cast; linarith only [h1]
    have h3 : γ * (4 / γ) ≤ γ * (m : ℝ) := mul_le_mul_of_nonneg_left h2 (le_of_lt hγ)
    rw [mul_div_cancel₀] at h3
    · exact h3
    · exact ne_of_gt hγ
  have hm80 : 80 ≤ m := by
    have hmc : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have h1 : (4 : ℝ) ≤ (1 / 20) * m := le_trans hmγ (by nlinarith)
    have h2 : (80 : ℝ) ≤ (m : ℝ) := by linarith only [h1]
    exact_mod_cast h2
  set q : ℕ := 16 * (K + 1) * (m * m) + 2 with hqdef
  have hq2 : 2 ≤ q := by omega
  set c : ℕ := 360 * m * q with hcdef
  have hc1 : 1 ≤ c := by
    have : 0 < 360 * m * q := by positivity
    omega
  refine ⟨max (400 * c * c) (max (8 * m) (K + 6)), ?_⟩
  intro V _ E S hn hES hdeg
  set n := S.card with hndef
  have hn1 : 400 * c * c ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 8 * m ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : K + 6 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn640 : 640 ≤ n := le_trans (by omega) hn2
  -- the star size, the common-neighbour bound and the number of rounds
  set k : ℕ := n / m with hkdef
  set a : ℕ := 3 * n / 4 with hadef
  set Tm : ℕ := q * (Nat.log 2 (K * n * n) + 1) with hTmdef
  have hP2 : m * k ≤ n := by
    calc m * k = k * m := by ring
      _ ≤ n := Nat.div_mul_le_self n m
  have hP1 : n < m * k + m := by
    have hdm : m * k + n % m = n := by rw [hkdef]; exact Nat.div_add_mod n m
    have hmod : n % m < m := Nat.mod_lt _ hmpos
    calc n = m * k + n % m := hdm.symm
      _ < m * k + m := Nat.add_lt_add_left hmod _
  have hk2 : 8 ≤ k := by
    rw [hkdef]
    exact (Nat.le_div_iff_mul_le hmpos).2 (by linarith only [hn2])
  have h80k : 80 * k ≤ n :=
    le_trans (Nat.mul_le_mul_right k hm80) hP2
  -- the number of rounds is logarithmic
  have hlogb : Nat.log 2 (K * n * n) + 1 ≤ 3 * (Nat.log 2 n + 1) := by
    have hnpos : 0 < n := by omega
    have hmono : Nat.log 2 (K * n * n) ≤ Nat.log 2 (n * n * n) := by
      refine Nat.log_mono_right ?_
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h3 : n * n * n < 2 ^ (3 * (Nat.log 2 n + 1)) := by
      have h2 : n * n * n < 2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1)
          * 2 ^ (Nat.log 2 n + 1) :=
        Nat.mul_lt_mul'' (Nat.mul_lt_mul'' h1 h1) h1
      calc n * n * n < 2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1)
            * 2 ^ (Nat.log 2 n + 1) := h2
        _ = 2 ^ (3 * (Nat.log 2 n + 1)) := by
            rw [← pow_add, ← pow_add]; ring_nf
    have h4 : Nat.log 2 (n * n * n) < 3 * (Nat.log 2 n + 1) :=
      Nat.log_lt_of_lt_pow (by positivity) h3
    omega
  have hTmbound : 120 * m * Tm ≤ n := by
    have hstep : 120 * m * Tm ≤ c * (Nat.log 2 n + 1) := by
      rw [hTmdef, hcdef]
      calc 120 * m * (q * (Nat.log 2 (K * n * n) + 1))
          = (120 * m * q) * (Nat.log 2 (K * n * n) + 1) := by ring
        _ ≤ (120 * m * q) * (3 * (Nat.log 2 n + 1)) := Nat.mul_le_mul_left _ hlogb
        _ = 360 * m * q * (Nat.log 2 n + 1) := by ring
    exact le_trans hstep (mul_log_le_self hc1 hn1)
  have hTm120 : 120 * Tm ≤ n :=
    le_trans (by calc 120 * Tm = 120 * 1 * Tm := by ring
      _ ≤ 120 * m * Tm := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmpos)) hTmbound
  have h4a : 4 * a ≤ 3 * n := by rw [hadef]; omega
  have h2a : n ≤ 2 * a := by rw [hadef]; omega
  have hq16 : 16 * (K + 1) * (m * m) ≤ q := by rw [hqdef]; exact Nat.le_add_right _ _
  have hTmlog : q * (Nat.log 2 (pot K (∅ : Finset (Sym2 V)) S) + 1) ≤ Tm := by
    have h1 : pot K (∅ : Finset (Sym2 V)) S ≤ K * n * n := by
      have hp := pot_empty_le K S
      rw [← hndef] at hp
      calc pot K (∅ : Finset (Sym2 V)) S ≤ K * (n * n) := hp
        _ = K * n * n := by ring
    have h2 : Nat.log 2 (pot K (∅ : Finset (Sym2 V)) S) ≤ Nat.log 2 (K * n * n) :=
      Nat.log_mono_right h1
    rw [hTmdef]
    exact Nat.mul_le_mul_left _ (by omega)
  clear_value Tm a k c q m
  -- the host hypotheses in arithmetic form
  have hnbd : ∀ z ∈ S, 9 * n ≤ 10 * (nbhdIn E z S).card := by
    intro z hz
    have h1 := hdeg z hz
    have h2 : (edeg E z : ℝ) ≤ ((nbhdIn E z S).card : ℝ) := by
      exact_mod_cast edeg_le_degTo hES z
    have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hγn : (0 : ℝ) ≤ γ * (n : ℝ) := mul_nonneg hγ.le h3
    have h4 : (9 : ℝ) * n ≤ 10 * ((nbhdIn E z S).card : ℝ) := by linarith only [h1, h2, hγn]
    exact_mod_cast h4
  have hnb : ∀ z ∈ S, 2 * k + Tm ≤ (nbhdIn E z S).card := by
    intro z hz
    have := hnbd z hz
    omega
  have hcn : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ W : Finset V, W.card ≤ 3 * Tm + 2 * k →
      a ≤ ((nbhdIn E x S ∩ nbhdIn E y S) \ W).card := by
    intro x hx y hy _ W hW
    have hdense := card_common_nbhd_dense hES hdeg hx hy W
    have hWr : (W.card : ℝ) ≤ 3 * (Tm : ℝ) + 2 * (k : ℝ) := by exact_mod_cast hW
    have h1 : (120 : ℝ) * (Tm : ℝ) ≤ (n : ℝ) := by exact_mod_cast hTm120
    have h2 : (80 : ℝ) * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast h80k
    have h3 : (4 : ℝ) * (a : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast h4a
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hγn : (0 : ℝ) ≤ γ * (n : ℝ) := mul_nonneg hγ.le hn0
    have hreal : (a : ℝ) ≤ (((nbhdIn E x S ∩ nbhdIn E y S) \ W).card : ℝ) := by
      linarith only [hdense, hWr, h1, h2, h3, hγn]
    exact_mod_cast hreal
  -- the counting hypothesis behind the decay factor
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h3n : 3 * n ≤ 4 * (m * (k' + 1)) := by nlinarith only [hP1, hn2]
  have h3n' : 3 * n ≤ 8 * (m * k') := by nlinarith only [hP1, hn2]
  have hbig : 9 * (n * (n * n)) ≤ 64 * (m * m) * (a * ((k' + 1) * k')) := by
    have hmul : n * ((3 * n) * (3 * n))
        ≤ (2 * a) * ((4 * (m * (k' + 1))) * (8 * (m * k'))) :=
      Nat.mul_le_mul h2a (Nat.mul_le_mul h3n h3n')
    calc 9 * (n * (n * n)) = n * ((3 * n) * (3 * n)) := by ring
      _ ≤ (2 * a) * ((4 * (m * (k' + 1))) * (8 * (m * k'))) := hmul
      _ = 64 * (m * m) * (a * ((k' + 1) * k')) := by ring
  have hqbig : K * (n * (n * n)) ≤ q * (a * ((k' + 1) * ((k' + 1) - 1))) := by
    simp only [Nat.add_sub_cancel]
    have s1 : (K + 1) * (9 * (n * (n * n)))
        ≤ (K + 1) * (64 * (m * m) * (a * ((k' + 1) * k'))) := Nat.mul_le_mul_left _ hbig
    have s2 : 4 * (K * (n * (n * n))) ≤ (K + 1) * (9 * (n * (n * n))) := by
      have e : (K + 1) * (9 * (n * (n * n)))
          = 9 * (K * (n * (n * n))) + 9 * (n * (n * n)) := by ring
      rw [e]
      exact le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.le_add_right _ _)
    have s3 : (K + 1) * (64 * (m * m) * (a * ((k' + 1) * k')))
        = 4 * ((16 * (K + 1) * (m * m)) * (a * ((k' + 1) * k'))) := by ring
    have s4 : 16 * (K + 1) * (m * m) ≤ q := hq16
    have s5 : (16 * (K + 1) * (m * m)) * (a * ((k' + 1) * k'))
        ≤ q * (a * ((k' + 1) * k')) := Nat.mul_le_mul_right _ s4
    have : 4 * (K * (n * (n * n))) ≤ 4 * (q * (a * ((k' + 1) * k'))) := by
      calc 4 * (K * (n * (n * n))) ≤ (K + 1) * (9 * (n * (n * n))) := s2
        _ ≤ (K + 1) * (64 * (m * m) * (a * ((k' + 1) * k'))) := s1
        _ = 4 * ((16 * (K + 1) * (m * m)) * (a * ((k' + 1) * k'))) := s3
        _ ≤ 4 * (q * (a * ((k' + 1) * k'))) := Nat.mul_le_mul_left _ s5
    exact Nat.le_of_mul_le_mul_left this (by norm_num)
  obtain ⟨R, hRE, hRdeg, hRcov⟩ :=
    exists_pairCovering_nat (E := E) (S := S) (K := K) (k := k' + 1) (a := a) (q := q) (Tm := Tm)
      (by omega) hq2 (by omega) hcn hnb (by omega) (by
        rw [← hndef]; exact hqbig) hTmlog
  refine ⟨R, hRE, ?_, hRcov⟩
  intro v
  have hdegv : (edeg R v : ℝ) ≤ (Tm : ℝ) + ((k' : ℝ) + 1) := by
    have := hRdeg v
    have hc : ((edeg R v : ℝ)) ≤ ((Tm + (k' + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hc
    linarith only [hc]
  have hA : (120 : ℝ) * (m : ℝ) * (Tm : ℝ) ≤ (n : ℝ) := by exact_mod_cast hTmbound
  have hB : (m : ℝ) * ((k' : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hP2
  have hk0 : (0 : ℝ) ≤ (k' : ℝ) + 1 := by positivity
  have hT0 : (0 : ℝ) ≤ (Tm : ℝ) := Nat.cast_nonneg _
  have h1 : 4 * ((k' : ℝ) + 1) ≤ γ * (n : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hB hγ.le,
      mul_le_mul_of_nonneg_right hmγ hk0]
  have h2 : 480 * (Tm : ℝ) ≤ γ * (n : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hA hγ.le,
      mul_le_mul_of_nonneg_right hmγ hT0]
  linarith only [hdegv, h1, h2]

/-- **A sparse pair-covering reservoir in a dense host.**

For every `γ > 0` and every constant `K` there is a threshold `n₀` such that every host
`E ⊆ cliqueEdges S` on at least `n₀` vertices with all degrees at least `(9/10 + γ)|S|` contains a
subgraph `R` of maximum degree at most `γ|S|` in which *every* pair of vertices of `S` has at least
`K` common `R`-neighbours.  The reservoir is produced by a deterministic greedy iteration: each
round adds one hub star (`exists_hub_star_capturing`) and multiplies the total covering deficiency
by a factor `(q-1)/q`, so `O(log |S|)` rounds suffice. -/
theorem exists_sparse_pairCovering {γ : ℝ} (hγ : 0 < γ) (K : ℕ) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ R : Finset (Sym2 V), R ⊆ E ∧ (∀ v : V, (edeg R v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ e ∈ cliqueEdges S, K ≤ (apexSet R S e).card := by
  obtain ⟨n₀, h⟩ := exists_sparse_pairCovering_small (γ := min γ (1 / 20))
    (lt_min hγ (by norm_num)) (min_le_right _ _) K
  have hmin : min γ (1 / 20) ≤ γ := min_le_left _ _
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES hdeg
  have h0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨R, hRE, hRdeg, hRcov⟩ := h E S hn hES (fun v hv => by
    have hv' := hdeg v hv
    nlinarith)
  refine ⟨R, hRE, fun v => ?_, hRcov⟩
  have hv := hRdeg v
  nlinarith

end BKLO
