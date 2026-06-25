import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 8000000

/-!
# A dyadic partition avoiding monotone three-term arithmetic progressions

This file formalizes the note *"A Dyadic Partition Avoiding Monotone Three-Term Arithmetic
Progressions"*.

We work with the positive integers `Pos = {n : ℕ | 1 ≤ n}`.

A *permutation* of a set `S ⊆ ℕ` is a function `π : ℕ → ℕ` that is injective with range `S`
(equivalently a bijection from the index set `ℕ = {0,1,2,...}` onto `S`).  For such a `π`, the
index `i` with `π i = t` plays the role of `posπ(t)`.

A *one-sided monotone three-term arithmetic progression* in `π` is a triple of indices
`i < j < k` with `π i < π j < π k` and `π i + π k = 2 * π j`: the three values form an increasing
three-term arithmetic progression and they appear in the permutation in that same increasing order.

The main results:

* `DyadicMono.main_theorem`: `Pos` can be partitioned into two sets each admitting a permutation
  avoiding one-sided monotone three-term arithmetic progressions.
* `DyadicMono.every_perm_hasMono`: every permutation of `Pos` contains such a progression
  (Proposition 6).
* `DyadicMono.least_parts_eq_two`: the least number of parts is exactly `2` (Corollary 7).
-/

namespace DyadicMono

/-- The positive integers. -/
def Pos : Set ℕ := {n : ℕ | 1 ≤ n}

/-- `π` *has* a one-sided monotone three-term arithmetic progression: there are indices
`i < j < k` with values forming an increasing AP appearing in increasing index order. -/
def HasMono (π : ℕ → ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧ π i < π j ∧ π j < π k ∧ π i + π k = 2 * π j

/-- A set `S ⊆ ℕ` *admits an avoiding permutation* if there is a bijection `π : ℕ → S`
(injective with range `S`) with no one-sided monotone three-term arithmetic progression. -/
def AdmitsAvoiding (S : Set ℕ) : Prop :=
  ∃ π : ℕ → ℕ, Function.Injective π ∧ Set.range π = S ∧ ¬ HasMono π

/-- The reversal within a dyadic block: if `n ∈ [2^m, 2^{m+1}-1]` then `rev n` is the mirror
element `2^m + (2^{m+1}-1-n)` of the same block. -/
def rev (n : ℕ) : ℕ := 2 ^ (Nat.log 2 n) + (2 ^ (Nat.log 2 n + 1) - 1 - n)

/-- The colour class with block-parity `p` (only `p = 0` and `p = 1` are interesting). -/
def col (p : ℕ) : Set ℕ := {n : ℕ | 1 ≤ n ∧ Nat.log 2 n % 2 = p}

/-- The even-block class `A`. -/
def Aset : Set ℕ := col 0

/-- The odd-block class `B`. -/
def Bset : Set ℕ := col 1

/-! ### Basic dyadic block facts -/

lemma pow_log_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ (Nat.log 2 n) ≤ n := by
  exact Nat.pow_log_le_self 2 (by omega)

lemma lt_pow_log {n : ℕ} : n < 2 ^ (Nat.log 2 n + 1) := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  simpa [Nat.succ_eq_add_one] using this

/-
Two elements with the same value of `Nat.log 2` lie in the same block; the middle value of an
ordered pair sandwiched between them keeps that block index.
-/
lemma log_mid {x y z m : ℕ} (hxy : x < y) (hyz : y < z)
    (hx : Nat.log 2 x = m) (hz : Nat.log 2 z = m) (hx1 : 1 ≤ x) : Nat.log 2 y = m := by
  refine' le_antisymm ( Nat.le_of_lt_succ _ ) ( Nat.le_of_not_lt fun hy => _ );
  · exact Nat.lt_succ_of_le ( Nat.le_trans ( Nat.log_mono_right hyz.le ) hz.le );
  · rw [ Nat.log_eq_iff ] at * <;> norm_num at *;
    · linarith [ Nat.pow_le_pow_right two_pos ( show Nat.log 2 y + 1 ≤ m from by linarith ), Nat.lt_pow_of_log_lt one_lt_two ( show Nat.log 2 y < Nat.log 2 y + 1 from Nat.lt_succ_self _ ) ];
    · grind;
    · grind

/-! ### Properties of `rev` -/

/-
`rev` keeps the block index fixed.
-/
lemma log_rev {n : ℕ} (hn : 1 ≤ n) : Nat.log 2 (rev n) = Nat.log 2 n := by
  refine' Nat.log_eq_of_pow_le_of_lt_pow _ _ <;> norm_num [ rev ];
  rw [ Nat.pow_succ ];
  linarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ Nat.log 2 n * 2 from by linarith [ pow_pos ( zero_lt_two' ℕ ) ( Nat.log 2 n ) ] ), Nat.sub_add_cancel ( show n ≤ 2 ^ Nat.log 2 n * 2 - 1 from Nat.le_sub_one_of_lt ( by rw [ ← pow_succ ] ; exact Nat.lt_pow_succ_log_self ( by decide ) _ ) ), pow_log_le hn ]

/-
`rev n` is positive for positive `n`.
-/
lemma rev_pos {n : ℕ} : 1 ≤ rev n := by
  exact le_add_of_le_of_nonneg ( Nat.one_le_pow _ _ ( by decide ) ) ( Nat.zero_le _ )

/-
`rev` is an involution on the positive integers.
-/
lemma rev_rev {n : ℕ} (hn : 1 ≤ n) : rev (rev n) = n := by
  unfold rev;
  have h_log_rev : Nat.log 2 (2 ^ Nat.log 2 n + (2 ^ (Nat.log 2 n + 1) - 1 - n)) = Nat.log 2 n := by
    convert log_rev hn using 1;
  have := pow_log_le hn; have := lt_pow_log (n := n); simp_all +decide [ pow_succ' ] ;
  omega

/-
Within a block, `rev` is strictly decreasing.
-/
lemma rev_anti {a b : ℕ}
    (hlog : Nat.log 2 a = Nat.log 2 b) (hab : a < b) : rev b < rev a := by
  unfold rev;
  rw [ hlog ];
  rw [ Nat.add_lt_add_iff_left, tsub_lt_tsub_iff_left_of_le ];
  · finiteness;
  · exact Nat.le_sub_one_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ )

/-
`rev` preserves the colour class `col p`.
-/
lemma rev_mem_col {p n : ℕ} (hn : n ∈ col p) : rev n ∈ col p := by
  exact ⟨ rev_pos, by rw [ log_rev hn.1 ] ; exact hn.2 ⟩

/-! ### The dyadic localization lemma (Lemma 4) -/

/-
**Lemma 4 (Dyadic localization).** Let `x < y < z` with `x + z = 2y`, all of whose block
indices share the parity of `m = Nat.log 2 z`.  If `x` is *not* in the top block (`Nat.log 2 x ≠ m`)
then the midpoint `y` is forced into the top block: `Nat.log 2 y = m`.
-/
lemma dyadic_localization {x y z : ℕ} (hx1 : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (hAP : x + z = 2 * y)
    (hpar_xz : Nat.log 2 x % 2 = Nat.log 2 z % 2)
    (hpar_yz : Nat.log 2 y % 2 = Nat.log 2 z % 2)
    (hne : Nat.log 2 x ≠ Nat.log 2 z) :
    Nat.log 2 y = Nat.log 2 z := by
  -- From the bounds on z and x, we get that y must be in the range [2^(m-1), 2^m).
  have hy_bounds : 2^(Nat.log 2 z - 1) ≤ y ∧ y < 2^(Nat.log 2 z + 1) := by
    rcases k : Nat.log 2 z with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
    · linarith;
    · rw [ Nat.log_eq_iff ] at k <;> norm_num at * ; omega;
  grind +suggestions

/-! ### Colour classes are infinite -/

lemma col_infinite {p : ℕ} (hp : p < 2) : (col p).Infinite := by
  -- The set {2^(2*r+p) | r : ℕ} is infinite because for each r, 2^(2*r+p) is distinct.
  have h_infinite : Set.Infinite {n : ℕ | ∃ r : ℕ, n = 2^(2*r+p)} := by
    exact Set.infinite_of_injective_forall_mem ( fun x y hxy => by simpa using hxy ) fun r => ⟨ r, rfl ⟩;
  refine h_infinite.mono ?_;
  intro n hn; obtain ⟨ r, rfl ⟩ := hn; exact ⟨ Nat.one_le_pow _ _ ( by decide ), by interval_cases p <;> simp +decide [ Nat.log_pow ] ⟩ ;

instance col_infinite_subtype0 : Infinite ↥(col 0) :=
  (col_infinite (by norm_num)).to_subtype

instance col_infinite_subtype1 : Infinite ↥(col 1) :=
  (col_infinite (by norm_num)).to_subtype

/-! ### Avoidance for a single colour class -/

/-
The core combinatorial fact: no increasing three-term arithmetic progression inside a colour
class can have its three `rev`-values increasing.  This packages Cases 1 and 2 of the proof of the
main theorem.
-/
lemma no_inc_AP_in_col {p x y z : ℕ}
    (hx : x ∈ col p) (hy : y ∈ col p) (hz : z ∈ col p)
    (hxy : x < y) (hyz : y < z) (hAP : x + z = 2 * y) :
    ¬ (rev x < rev y ∧ rev y < rev z) := by
  by_cases hlog : Nat.log 2 x = Nat.log 2 z;
  · have hlog_y : Nat.log 2 y = Nat.log 2 z := by
      apply log_mid hxy hyz hlog rfl hx.1;
    exact fun h => h.1.not_ge <| rev_anti ( by linarith ) hxy |> le_of_lt;
  · -- By dyadic localization, since $x < y < z$ and $x + z = 2y$, we have $Nat.log 2 y = Nat.log 2 z$.
    have hlog_yz : Nat.log 2 y = Nat.log 2 z := by
      apply dyadic_localization hx.1 hxy hyz hAP;
      · exact hx.2.trans hz.2.symm;
      · exact hy.2.trans hz.2.symm;
      · assumption;
    exact fun h => h.2.not_ge <| rev_anti ( by aesop ) hyz |> le_of_lt

/-
Every colour class `col p` (with `p < 2`) admits an avoiding permutation, realized by
`rev ∘ (increasing enumeration of col p)`.
-/
lemma col_admitsAvoiding {p : ℕ} [Infinite ↥(col p)] :
    AdmitsAvoiding (col p) := by
  -- Let e := Nat.orderEmbeddingOfSet (col p). We must show Injective π, range π = col p, ¬ HasMono π.
  set e := Nat.orderEmbeddingOfSet (col p)
  have hee : Set.range e = col p := by
    convert Nat.orderEmbeddingOfSet_range ( col p );
  use fun i => rev ( e i );
  refine' ⟨ _, _, _ ⟩;
  · intro i j hij;
    apply_fun rev at hij;
    rw [ rev_rev, rev_rev ] at hij;
    · exact e.injective hij;
    · exact hee.subset ( Set.mem_range_self _ ) |>.1;
    · exact hee.subset ( Set.mem_range_self i ) |>.1;
  · ext x;
    constructor <;> intro hx;
    · obtain ⟨ i, rfl ⟩ := hx; exact rev_mem_col ( hee.subset <| Set.mem_range_self i ) ;
    · obtain ⟨ i, hi ⟩ := hee.symm.subset ( rev_mem_col hx );
      use i; simp [hi, rev_rev hx.1];
  · rintro ⟨ i, j, k, hij, hjk, h₁, h₂, h₃ ⟩;
    -- Let x = π i = rev (e i), etc. They lie in col p. From hij, hjk and strict monotonicity of e, e i < e j < e k. Since e i ≥ 1, rev x = rev (rev (e i)) = e i (rev_rev), similarly rev y = e j, rev z = e k. So rev x < rev y < rev z. Also x < y < z (the π i<π j<π k) and x + z = 2 y (hAP). This contradicts no_inc_AP_in_col applied to x,y,z.
    set x := rev (e i)
    set y := rev (e j)
    set z := rev (e k)
    have hx : x ∈ col p := by
      exact rev_mem_col <| hee.subset <| Set.mem_range_self _
    have hy : y ∈ col p := by
      exact rev_mem_col <| hee.subset <| Set.mem_range_self _
    have hz : z ∈ col p := by
      exact rev_mem_col <| hee.subset <| Set.mem_range_self _
    have hxy : x < y := by
      exact h₁
    have hyz : y < z := by
      exact h₂
    have hAP : x + z = 2 * y := by
      exact h₃;
    apply no_inc_AP_in_col hx hy hz hxy hyz hAP;
    simp +zetaDelta at *;
    exact ⟨ by rw [ rev_rev ( show 1 ≤ _ from ( Nat.Subtype.ofNat ( col p ) i ) |>.2.1 ) ] ; rw [ rev_rev ( show 1 ≤ _ from ( Nat.Subtype.ofNat ( col p ) j ) |>.2.1 ) ] ; exact e.strictMono hij, by rw [ rev_rev ( show 1 ≤ _ from ( Nat.Subtype.ofNat ( col p ) j ) |>.2.1 ) ] ; rw [ rev_rev ( show 1 ≤ _ from ( Nat.Subtype.ofNat ( col p ) k ) |>.2.1 ) ] ; exact e.strictMono hjk ⟩

/-! ### Main theorem -/

/-
**Main theorem (Theorem 3).** `Pos` can be partitioned into two sets `A` and `B`, each
admitting a permutation avoiding one-sided monotone three-term arithmetic progressions.
-/
lemma Aset_union_Bset : Aset ∪ Bset = Pos := by
  ext n
  simp [Aset, Bset, Pos];
  exact ⟨ fun h => h.elim ( fun h => h.1 ) fun h => h.1, fun h => by cases Nat.mod_two_eq_zero_or_one ( Nat.log 2 n ) <;> [ left; right ] <;> exact ⟨ h, by linarith ⟩ ⟩

lemma Aset_disjoint_Bset : Disjoint Aset Bset := by
  exact Set.disjoint_left.mpr fun x hx hx' => by have := hx.2; have := hx'.2; omega;

theorem main_theorem :
    ∃ A B : Set ℕ, A ∪ B = Pos ∧ Disjoint A B ∧
      AdmitsAvoiding A ∧ AdmitsAvoiding B :=
  ⟨Aset, Bset, Aset_union_Bset, Aset_disjoint_Bset,
    col_admitsAvoiding (p := 0), col_admitsAvoiding (p := 1)⟩

/-! ### Sharpness: one set is impossible (Proposition 6) -/

/-
**Proposition 6.** Every permutation of `Pos` contains a one-sided monotone three-term
arithmetic progression.
-/
theorem every_perm_hasMono (π : ℕ → ℕ)
    (hrange : Set.range π = Pos) : HasMono π := by
  -- Set b = π j (b > a). Set c = 2*b - a. Since b > a, c = 2b - a > b > a ≥ 1, and c ≥ 1 so c ∈ Pos = range π; pick k with π k = c.
  obtain ⟨j, hj⟩ : ∃ j, π j > π 0 ∧ ∀ i < j, π i ≤ π 0 := by
    have h_exists_j : ∃ j, π j > π 0 := by
      simp_all +decide [ Set.ext_iff, Pos ];
      exact Exists.elim ( hrange ( π 0 + 1 ) |>.2 ( by linarith ) ) fun x hx => ⟨ x, by linarith ⟩;
    exact ⟨ Nat.find h_exists_j, Nat.find_spec h_exists_j, fun i hi => not_lt.1 fun contra => Nat.find_min h_exists_j hi contra ⟩
  set b := π j
  set c := 2 * b - π 0
  obtain ⟨k, hk⟩ : ∃ k, π k = c := by
    exact hrange.symm.subset <| show 1 ≤ c from Nat.le_sub_of_add_le <| by linarith;
  use 0, j, k;
  grind

/-- `Pos` itself does not admit an avoiding permutation. -/
theorem not_admitsAvoiding_pos : ¬ AdmitsAvoiding Pos := by
  rintro ⟨π, -, hrange, hno⟩
  exact hno (every_perm_hasMono π hrange)

/-! ### Corollary 7: the least number of parts is exactly two -/

/-- `Pos` can be partitioned into `n` parts each admitting an avoiding permutation. -/
def CanPartition (n : ℕ) : Prop :=
  ∃ f : Fin n → Set ℕ, (⋃ i, f i) = Pos ∧ (Pairwise (Function.onFun Disjoint f)) ∧
    ∀ i, AdmitsAvoiding (f i)

/-
**Corollary 7.** The least number of parts is exactly `2`.
-/
theorem least_parts_eq_two : IsLeast {n : ℕ | CanPartition n} 2 := by
  constructor;
  · obtain ⟨ A, B, h₁, h₂, h₃, h₄ ⟩ := main_theorem;
    refine' ⟨ fun i => if i = 0 then A else B, _, _, _ ⟩ <;> simp_all +decide [ Fin.forall_fin_two, Pairwise ];
    · simp_all +decide [ Set.ext_iff, Fin.exists_fin_two ];
    · grind;
  · intro n hn; rcases hn with ⟨ f, hf₁, hf₂, hf₃ ⟩ ; rcases n with ( _ | _ | n ) <;> simp_all +decide ;
    · exact absurd hf₁.symm ( Set.Nonempty.ne_empty ⟨ 1, by norm_num [ Pos ] ⟩ );
    · simp_all +decide [ Set.ext_iff, Fin.eq_zero ];
      exact not_admitsAvoiding_pos ( by simpa [ show f 0 = Pos from Set.ext hf₁ ] using hf₃ )

end DyadicMono
