import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# The scalar complete-split terminal LP behind (C3)

This module is completely independent of the physical completion modules, of
`FarRounding`, and of every historical aggregate result: it only uses Mathlib.

For a host size `n` and a split parameter `k ≤ n` we set

* `a = k.choose 2`  (edges inside the split clique), and
* `b = k * (n - k)` (edges from the split clique to the rest of the host).

The complete-split terminal LP in the variables `u, v, w` (rational masses of
the three admissible local moves) is

```
minimize   a + b - 2u - 5v - 5w
subject to u + 3v + 6w ≤ a,   2u + 3v ≤ b,   u, v, w ≥ 0.
```

The exact piecewise optimum is proved here:

| region      | optimal point              | optimal value |
| ----------- | -------------------------- | ------------- |
| `2a ≤ b`    | `(a, 0, 0)`                | `b - a`       |
| `a ≤ b ≤ 2a`| `(b - a, (2a - b)/3, 0)`   | `(2b - a)/3`  |
| `b ≤ a`     | `(0, b/3, (a - b)/6)`      | `(a + b)/6`   |

Each branch is proved as an `IsLeast` statement (attainment plus a matching
lower bound valid for *every* feasible point, derived from the two displayed
constraints alone), and is transported to an `IsGLB` statement.

The degenerate combinatorial cases (`k < 4`, and the zero-host cases `k = 0`
and `k = n`) are treated explicitly in the last section rather than being
assumed away.

**Unresolved graph-theoretic bridge.** Nothing here asserts that the aggregate
masses `u, v, w` are uniformly distributed over the actual split cliques of a
graph; that distribution statement is the missing bridge between this scalar LP
and a genuine graph-theoretic terminal bound, and it is *not* postulated in
this file in any form.
-/

namespace PaperIV.SplitTerminalLP

/-! ## Data of the LP -/

/-- Number of edges inside a split clique on `k` vertices. -/
def splitA (k : ℕ) : ℚ := (k.choose 2 : ℚ)

/-- Number of edges from a split clique on `k` vertices to the remaining
`n - k` vertices of the host, with natural (truncated) subtraction. -/
def splitB (k n : ℕ) : ℚ := ((k * (n - k) : ℕ) : ℚ)

/-- Under the explicit side condition `k ≤ n` the truncated subtraction in
`splitB` agrees with rational subtraction. -/
theorem splitB_eq_of_le {k n : ℕ} (h : k ≤ n) :
    splitB k n = (k : ℚ) * ((n : ℚ) - (k : ℚ)) := by
  unfold splitB
  push_cast [Nat.cast_sub h]
  ring

theorem splitA_nonneg (k : ℕ) : 0 ≤ splitA k := by
  unfold splitA; positivity

theorem splitB_nonneg (k n : ℕ) : 0 ≤ splitB k n := by
  unfold splitB; positivity

/-! ## Feasible region, objective and value set -/

/-- The feasible region of the complete-split terminal LP. -/
structure Feasible (a b u v w : ℚ) : Prop where
  nonneg_u : 0 ≤ u
  nonneg_v : 0 ≤ v
  nonneg_w : 0 ≤ w
  inner : u + 3 * v + 6 * w ≤ a
  cross : 2 * u + 3 * v ≤ b

/-- The objective of the complete-split terminal LP. -/
def cost (a b u v w : ℚ) : ℚ := a + b - 2 * u - 5 * v - 5 * w

/-- The set of attainable objective values. -/
def costSet (a b : ℚ) : Set ℚ :=
  {c | ∃ u v w : ℚ, Feasible a b u v w ∧ c = cost a b u v w}

theorem mem_costSet {a b c : ℚ} :
    c ∈ costSet a b ↔ ∃ u v w : ℚ, Feasible a b u v w ∧ c = cost a b u v w :=
  Iff.rfl

/-- The feasible region is nonempty as soon as `a` and `b` are nonnegative. -/
theorem feasible_zero {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Feasible a b 0 0 0 :=
  { nonneg_u := le_rfl, nonneg_v := le_rfl, nonneg_w := le_rfl,
    inner := by linarith, cross := by linarith }

theorem costSet_nonempty {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (costSet a b).Nonempty :=
  ⟨cost a b 0 0 0, 0, 0, 0, feasible_zero ha hb, rfl⟩

/-! ## The three lower bounds

Each bound is a nonnegative combination of the two displayed constraints, and
therefore holds at *every* feasible point; the region conditions are only
needed for attainment. -/

/-- Lower bound of the `2a ≤ b` branch: `2 · (inner)`. -/
theorem cost_ge_sub {a b u v w : ℚ} (h : Feasible a b u v w) :
    b - a ≤ cost a b u v w := by
  obtain ⟨hu, hv, hw, hin, _⟩ := h
  unfold cost
  linarith

/-- Lower bound of the `a ≤ b ≤ 2a` branch: `(4/3) · (inner) + (1/3) · (cross)`. -/
theorem cost_ge_mid {a b u v w : ℚ} (h : Feasible a b u v w) :
    (2 * b - a) / 3 ≤ cost a b u v w := by
  obtain ⟨hu, hv, hw, hin, hcr⟩ := h
  unfold cost
  linarith

/-- Lower bound of the `b ≤ a` branch: `(5/6) · (inner) + (5/6) · (cross)`. -/
theorem cost_ge_low {a b u v w : ℚ} (h : Feasible a b u v w) :
    (a + b) / 6 ≤ cost a b u v w := by
  obtain ⟨hu, hv, hw, hin, hcr⟩ := h
  unfold cost
  linarith

/-! ## Attainment in each region -/

/-- In the region `2a ≤ b` the point `(a, 0, 0)` is feasible. -/
theorem feasible_sub {a b : ℚ} (ha : 0 ≤ a) (hb : 2 * a ≤ b) :
    Feasible a b a 0 0 :=
  { nonneg_u := ha, nonneg_v := le_rfl, nonneg_w := le_rfl,
    inner := by linarith, cross := by linarith }

theorem cost_sub {a b : ℚ} : cost a b a 0 0 = b - a := by
  unfold cost; ring

/-- In the region `a ≤ b ≤ 2a` the point `(b - a, (2a - b)/3, 0)` is feasible. -/
theorem feasible_mid {a b : ℚ} (hab : a ≤ b) (hba : b ≤ 2 * a) :
    Feasible a b (b - a) ((2 * a - b) / 3) 0 :=
  { nonneg_u := by linarith, nonneg_v := by linarith, nonneg_w := le_rfl,
    inner := by linarith, cross := by linarith }

theorem cost_mid {a b : ℚ} :
    cost a b (b - a) ((2 * a - b) / 3) 0 = (2 * b - a) / 3 := by
  unfold cost; ring

/-- In the region `b ≤ a` the point `(0, b/3, (a - b)/6)` is feasible. -/
theorem feasible_low {a b : ℚ} (hb : 0 ≤ b) (hba : b ≤ a) :
    Feasible a b 0 (b / 3) ((a - b) / 6) :=
  { nonneg_u := le_rfl, nonneg_v := by linarith, nonneg_w := by linarith,
    inner := by linarith, cross := by linarith }

theorem cost_low {a b : ℚ} :
    cost a b 0 (b / 3) ((a - b) / 6) = (a + b) / 6 := by
  unfold cost; ring

/-! ## The exact piecewise optimum -/

/-- **Branch `2a ≤ b`.** The minimum of the LP is exactly `b - a`, attained at
`(a, 0, 0)`. -/
theorem isLeast_costSet_sub {a b : ℚ} (ha : 0 ≤ a) (hb : 2 * a ≤ b) :
    IsLeast (costSet a b) (b - a) := by
  constructor
  · exact ⟨a, 0, 0, feasible_sub ha hb, cost_sub.symm⟩
  · rintro c ⟨u, v, w, hf, rfl⟩
    exact cost_ge_sub hf

/-- **Branch `a ≤ b ≤ 2a`.** The minimum of the LP is exactly `(2b - a)/3`,
attained at `(b - a, (2a - b)/3, 0)`. -/
theorem isLeast_costSet_mid {a b : ℚ} (hab : a ≤ b) (hba : b ≤ 2 * a) :
    IsLeast (costSet a b) ((2 * b - a) / 3) := by
  constructor
  · exact ⟨b - a, (2 * a - b) / 3, 0, feasible_mid hab hba, cost_mid.symm⟩
  · rintro c ⟨u, v, w, hf, rfl⟩
    exact cost_ge_mid hf

/-- **Branch `b ≤ a`.** The minimum of the LP is exactly `(a + b)/6`, attained
at `(0, b/3, (a - b)/6)`. -/
theorem isLeast_costSet_low {a b : ℚ} (hb : 0 ≤ b) (hba : b ≤ a) :
    IsLeast (costSet a b) ((a + b) / 6) := by
  constructor
  · exact ⟨0, b / 3, (a - b) / 6, feasible_low hb hba, cost_low.symm⟩
  · rintro c ⟨u, v, w, hf, rfl⟩
    exact cost_ge_low hf

theorem isGLB_costSet_sub {a b : ℚ} (ha : 0 ≤ a) (hb : 2 * a ≤ b) :
    IsGLB (costSet a b) (b - a) := (isLeast_costSet_sub ha hb).isGLB

theorem isGLB_costSet_mid {a b : ℚ} (hab : a ≤ b) (hba : b ≤ 2 * a) :
    IsGLB (costSet a b) ((2 * b - a) / 3) := (isLeast_costSet_mid hab hba).isGLB

theorem isGLB_costSet_low {a b : ℚ} (hb : 0 ≤ b) (hba : b ≤ a) :
    IsGLB (costSet a b) ((a + b) / 6) := (isLeast_costSet_low hb hba).isGLB

/-- The three branches cover every pair `(a, b)` with `0 ≤ a`, `0 ≤ b`. -/
theorem branch_trichotomy (a b : ℚ) :
    2 * a ≤ b ∨ (a ≤ b ∧ b ≤ 2 * a) ∨ b ≤ a := by
  rcases le_or_gt (2 * a) b with h | h
  · exact Or.inl h
  · rcases le_or_gt b a with h' | h'
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl ⟨h'.le, h.le⟩)

/-- The piecewise optimum in one statement: for nonnegative data the LP always
has a least attained value, given by the branch that applies. -/
theorem exists_isLeast_costSet {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ c, IsLeast (costSet a b) c ∧
      ((2 * a ≤ b ∧ c = b - a) ∨
       (a ≤ b ∧ b ≤ 2 * a ∧ c = (2 * b - a) / 3) ∨
       (b ≤ a ∧ c = (a + b) / 6)) := by
  rcases branch_trichotomy a b with h | ⟨h₁, h₂⟩ | h
  · exact ⟨b - a, isLeast_costSet_sub ha h, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨(2 * b - a) / 3, isLeast_costSet_mid h₁ h₂,
      Or.inr (Or.inl ⟨h₁, h₂, rfl⟩)⟩
  · exact ⟨(a + b) / 6, isLeast_costSet_low hb h, Or.inr (Or.inr ⟨h, rfl⟩)⟩

/-! ## Instantiation at the combinatorial data `a = k.choose 2`, `b = k(n-k)`

The host-size range `4 ≤ n` and the split range `k ≤ n` are carried explicitly
as hypotheses; they are never used silently. -/

/-- The LP value set at the combinatorial data of a `k`-split of an `n`-host. -/
def splitCostSet (k n : ℕ) : Set ℚ := costSet (splitA k) (splitB k n)

/-- Branch `2·C(k,2) ≤ k(n-k)` (the "wide host" branch). -/
theorem isLeast_splitCostSet_sub {k n : ℕ} (_hn : 4 ≤ n) (_hk : k ≤ n)
    (h : 2 * splitA k ≤ splitB k n) :
    IsLeast (splitCostSet k n) (splitB k n - splitA k) :=
  isLeast_costSet_sub (splitA_nonneg k) h

/-- Branch `C(k,2) ≤ k(n-k) ≤ 2·C(k,2)` (the "balanced" branch). -/
theorem isLeast_splitCostSet_mid {k n : ℕ} (_hn : 4 ≤ n) (_hk : k ≤ n)
    (h₁ : splitA k ≤ splitB k n) (h₂ : splitB k n ≤ 2 * splitA k) :
    IsLeast (splitCostSet k n) ((2 * splitB k n - splitA k) / 3) :=
  isLeast_costSet_mid h₁ h₂

/-- Branch `k(n-k) ≤ C(k,2)` (the "dense split" branch). -/
theorem isLeast_splitCostSet_low {k n : ℕ} (_hn : 4 ≤ n) (_hk : k ≤ n)
    (h : splitB k n ≤ splitA k) :
    IsLeast (splitCostSet k n) ((splitA k + splitB k n) / 6) :=
  isLeast_costSet_low (splitB_nonneg k n) h

/-- The complete piecewise optimum at the combinatorial data, for every host of
size at least `4` and every split size `k ≤ n`. -/
theorem exists_isLeast_splitCostSet {k n : ℕ} (_hn : 4 ≤ n) (_hk : k ≤ n) :
    ∃ c, IsLeast (splitCostSet k n) c ∧
      ((2 * splitA k ≤ splitB k n ∧ c = splitB k n - splitA k) ∨
       (splitA k ≤ splitB k n ∧ splitB k n ≤ 2 * splitA k ∧
          c = (2 * splitB k n - splitA k) / 3) ∨
       (splitB k n ≤ splitA k ∧ c = (splitA k + splitB k n) / 6)) :=
  exists_isLeast_costSet (splitA_nonneg k) (splitB_nonneg k n)

/-! ## The explicitly separated degenerate cases

`k < 4` and the two zero-host cases `k = 0`, `k = n` are not covered by any
implicit assumption above; they are recorded here. -/

theorem splitA_zero : splitA 0 = 0 := by simp [splitA]

theorem splitA_one : splitA 1 = 0 := by simp [splitA]

theorem splitA_two : splitA 2 = 1 := by norm_num [splitA, Nat.choose]

theorem splitA_three : splitA 3 = 3 := by norm_num [splitA, Nat.choose]

theorem splitA_four : splitA 4 = 6 := by norm_num [splitA, Nat.choose]

/-- Zero-host case `k = 0`: the cross term vanishes. -/
theorem splitB_zero_left (n : ℕ) : splitB 0 n = 0 := by simp [splitB]

/-- Zero-host case `k = n`: the cross term vanishes. -/
theorem splitB_self (k : ℕ) : splitB k k = 0 := by simp [splitB]

/-- Degenerate split `k = 0`: both data vanish and the LP optimum is `0`. -/
theorem isLeast_splitCostSet_zero {n : ℕ} (hn : 4 ≤ n) :
    IsLeast (splitCostSet 0 n) 0 := by
  have h : IsLeast (splitCostSet 0 n) ((splitA 0 + splitB 0 n) / 6) :=
    isLeast_splitCostSet_low hn (Nat.zero_le n)
      (by rw [splitB_zero_left, splitA_zero])
  rwa [splitA_zero, splitB_zero_left, show ((0 : ℚ) + 0) / 6 = 0 by norm_num] at h

/-- Degenerate split `k = 1`: here `a = 0`, so `2a = 0 ≤ b` and the applicable
branch is the wide-host one; the LP optimum is exactly `b = n - 1`. -/
theorem isLeast_splitCostSet_one {n : ℕ} (hn : 4 ≤ n) :
    IsLeast (splitCostSet 1 n) (splitB 1 n) := by
  have h : IsLeast (splitCostSet 1 n) (splitB 1 n - splitA 1) :=
    isLeast_splitCostSet_sub hn (by omega)
      (by rw [splitA_one]; simpa using splitB_nonneg 1 n)
  rwa [splitA_one, sub_zero] at h

/-- Degenerate split `k = n` (no vertices outside the clique): the optimum is
`C(n,2)/6`. -/
theorem isLeast_splitCostSet_full {n : ℕ} (hn : 4 ≤ n) :
    IsLeast (splitCostSet n n) (splitA n / 6) := by
  have h : IsLeast (splitCostSet n n) ((splitA n + splitB n n) / 6) :=
    isLeast_splitCostSet_low hn le_rfl (by rw [splitB_self]; exact splitA_nonneg n)
  rwa [splitB_self, add_zero] at h

/-- Small splits `k < 4` are genuinely covered by the general statement: here is
the case `k = 3` of a host of size at least `4`, where `a = 3`. -/
theorem isLeast_splitCostSet_three {n : ℕ} (hn : 4 ≤ n) (hk : 3 ≤ n) :
    ∃ c, IsLeast (splitCostSet 3 n) c ∧
      ((6 ≤ splitB 3 n ∧ c = splitB 3 n - 3) ∨
       (3 ≤ splitB 3 n ∧ splitB 3 n ≤ 6 ∧ c = (2 * splitB 3 n - 3) / 3) ∨
       (splitB 3 n ≤ 3 ∧ c = (3 + splitB 3 n) / 6)) := by
  obtain ⟨c, hc, hbr⟩ := exists_isLeast_splitCostSet hn hk
  rw [splitA_three] at hbr
  refine ⟨c, hc, ?_⟩
  rcases hbr with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨by linarith, h₂⟩
  · exact Or.inr (Or.inl ⟨h₁, by linarith, h₃⟩)
  · exact Or.inr (Or.inr ⟨h₁, h₂⟩)

/-! ## Numerical sanity check -/

/-- Sanity instance `k = 4`, `n = 10`: `a = 6`, `b = 24 ≥ 2a`, so the LP
optimum is exactly `b - a = 18`, attained at `(6, 0, 0)`. -/
theorem sanity_k4_n10 :
    splitA 4 = 6 ∧ splitB 4 10 = 24 ∧
      IsLeast (splitCostSet 4 10) 18 ∧
      Feasible (splitA 4) (splitB 4 10) 6 0 0 ∧
      cost (splitA 4) (splitB 4 10) 6 0 0 = 18 := by
  have ha : splitA 4 = 6 := splitA_four
  have hb : splitB 4 10 = 24 := by norm_num [splitB]
  refine ⟨ha, hb, ?_, ?_, ?_⟩
  · have h : IsLeast (splitCostSet 4 10) (splitB 4 10 - splitA 4) :=
      isLeast_splitCostSet_sub (by norm_num) (by norm_num) (by rw [ha, hb]; norm_num)
    rwa [ha, hb, show (24 : ℚ) - 6 = 18 by norm_num] at h
  · rw [ha, hb]
    exact feasible_sub (by norm_num) (by norm_num)
  · rw [ha, hb]; unfold cost; norm_num

/-- Sanity instance `k = 6`, `n = 8`: `a = 15`, `b = 12 ≤ a`, so the LP optimum
is exactly `(a + b)/6 = 9/2`, attained at `(0, 4, 1/2)`. -/
theorem sanity_k6_n8 :
    splitA 6 = 15 ∧ splitB 6 8 = 12 ∧
      IsLeast (splitCostSet 6 8) (9 / 2) ∧
      Feasible (splitA 6) (splitB 6 8) 0 4 (1 / 2) ∧
      cost (splitA 6) (splitB 6 8) 0 4 (1 / 2) = 9 / 2 := by
  have ha : splitA 6 = 15 := by norm_num [splitA, Nat.choose]
  have hb : splitB 6 8 = 12 := by norm_num [splitB]
  refine ⟨ha, hb, ?_, ?_, ?_⟩
  · have h : IsLeast (splitCostSet 6 8) ((splitA 6 + splitB 6 8) / 6) :=
      isLeast_splitCostSet_low (by norm_num) (by norm_num) (by rw [ha, hb]; norm_num)
    rwa [ha, hb, show ((15 : ℚ) + 12) / 6 = 9 / 2 by norm_num] at h
  · rw [ha, hb]
    have := feasible_low (a := (15 : ℚ)) (b := 12) (by norm_num) (by norm_num)
    norm_num at this ⊢
    exact this
  · rw [ha, hb]; unfold cost; norm_num

end PaperIV.SplitTerminalLP
