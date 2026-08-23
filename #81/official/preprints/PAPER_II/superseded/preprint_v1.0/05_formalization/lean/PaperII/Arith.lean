import Mathlib.Tactic

/-!
# Paper II — Arithmetic core (ledger steps L10, L11)

Self-contained integer arithmetic behind the extremal value `⌊(2n+1)²/24⌋`.
No graph theory here; this is the "Integer maximization over `p`" of the ledger.

Ledger facts formalized:
* L10 (saturated branch): `Φ_τ(S_{p,q}) = p·q − C(p,2) = p(2n+1−3p)/2 =: F_n(p)`  (with `q = n−p`).
  We work with `twoFsat n p := p(2n+1−3p) = 2·F_n(p)` to avoid division.
* L11 (completing the square, denominators cleared):
  `12 · (2·F_n(p)) = (2n+1)² − (6p − (2n+1))²`,  a pure `ring` identity,
  whence `F_n(p) ≤ (2n+1)²/24 = ⌊(2n+1)²/24⌋` over `ℤ`.
-/

namespace PaperII

/-- `twoFsat n p = 2·F_n(p) = p(2n+1−3p)`; equals `2(pq − C(p,2))` with `q = n − p`
    (the saturated-branch deficit of `S_{p,q}`, ledger L10). Kept as `2·F_n` to stay in `ℤ`. -/
def twoFsat (n p : ℤ) : ℤ := p * (2 * n + 1 - 3 * p)

/-- L10 check: `twoFsat n p = 2·(p·(n−p) − C(p,2))`, i.e. `twoFsat = 2·(pq − P)` with `q=n−p`,
    `2·P = p(p−1)`. Pure ring identity. -/
theorem twoFsat_eq_two_mul_deficit (n p : ℤ) :
    twoFsat n p = 2 * (p * (n - p)) - p * (p - 1) := by
  unfold twoFsat; ring

/-- L11 core identity (completing the square, cleared of denominators):
    `12 · twoFsat n p = (2n+1)² − (6p − (2n+1))²`. -/
theorem twelve_mul_twoFsat (n p : ℤ) :
    12 * twoFsat n p = (2 * n + 1) ^ 2 - (6 * p - (2 * n + 1)) ^ 2 := by
  unfold twoFsat; ring

/-- Consequently `twoFsat` is bounded (cleared form): `12 · twoFsat n p ≤ (2n+1)²`. -/
theorem twelve_mul_twoFsat_le (n p : ℤ) :
    12 * twoFsat n p ≤ (2 * n + 1) ^ 2 := by
  have h := twelve_mul_twoFsat n p
  nlinarith [sq_nonneg (6 * p - (2 * n + 1))]

/-- `twoFsat` is even, so `F_n(p) := twoFsat/2` is a genuine integer. -/
theorem even_twoFsat (n p : ℤ) : Even (twoFsat n p) := by
  unfold twoFsat
  rcases Int.even_or_odd p with hp | hp
  · exact hp.mul_right _
  · -- p odd ⇒ (2n+1 − 3p) even
    refine Even.mul_left ?_ _
    obtain ⟨k, hk⟩ := hp
    exact ⟨n - 3 * k - 1, by rw [hk]; ring⟩

/-- The saturated-branch deficit as a genuine integer `F_n(p) = twoFsat/2`. -/
def Fsat (n p : ℤ) : ℤ := twoFsat n p / 2

theorem two_mul_Fsat (n p : ℤ) : 2 * Fsat n p = twoFsat n p := by
  unfold Fsat
  exact (Int.two_mul_ediv_two_of_even (even_twoFsat n p))

/-- L11 upper bound (integer/floor form): `F_n(p) ≤ ⌊(2n+1)²/24⌋`.
    Here `(2n+1)² ≥ 0` so `ℤ`-division by `24` is the floor. -/
theorem Fsat_le_floor (n p : ℤ) :
    Fsat n p ≤ (2 * n + 1) ^ 2 / 24 := by
  -- from `24 · Fsat = 12 · twoFsat ≤ (2n+1)²` and `Int.le_ediv_iff` style bound
  have h24 : 24 * Fsat n p ≤ (2 * n + 1) ^ 2 := by
    have : 24 * Fsat n p = 12 * twoFsat n p := by
      have := two_mul_Fsat n p; linarith [this]
    rw [this]; exact twelve_mul_twoFsat_le n p
  -- divide by 24 (positive), floor on the right
  have : Fsat n p ≤ (2 * n + 1) ^ 2 / 24 := by
    rw [Int.le_ediv_iff_mul_le (by norm_num)]
    linarith [h24]
  exact this

/-- Ledger L11 (attainment): the floor `⌊(2n+1)²/24⌋` is attained by `F_n` at `p = ⌊(2n+4)/6⌋`. -/
theorem exists_Fsat_eq_floor (n : ℤ) : ∃ p, Fsat n p = (2 * n + 1) ^ 2 / 24 := by
  refine ⟨(2 * n + 1 + 3) / 6, ?_⟩
  have h24 : 24 * Fsat n ((2 * n + 1 + 3) / 6)
      = (2 * n + 1) ^ 2 - (6 * ((2 * n + 1 + 3) / 6) - (2 * n + 1)) ^ 2 := by
    have h1 := two_mul_Fsat n ((2 * n + 1 + 3) / 6)
    have h2 := twelve_mul_twoFsat n ((2 * n + 1 + 3) / 6)
    linarith
  have hsq : (6 * ((2 * n + 1 + 3) / 6) - (2 * n + 1)) ^ 2 = (2 * n + 1) ^ 2 % 24 := by
    obtain ⟨s, hs⟩ : ∃ s, 2 * n + 1 = 12 * s + (2 * n + 1) % 12 := ⟨(2 * n + 1) / 12, by omega⟩
    have hm2 : (2 * n + 1) ^ 2
        = 24 * (6 * s ^ 2 + s * ((2 * n + 1) % 12)) + ((2 * n + 1) % 12) ^ 2 := by
      linear_combination (2 * n + 1 + 12 * s + (2 * n + 1) % 12) * hs
    have hmod : ∀ X Y : ℤ, (24 * X + Y) % 24 = Y % 24 := fun X Y => by omega
    have hdd : 6 * ((2 * n + 1 + 3) / 6) - (2 * n + 1)
        = 6 * (((2 * n + 1) % 12 + 3) / 6) - (2 * n + 1) % 12 := by omega
    rw [hm2, hmod, hdd]
    have hr : (2 * n + 1) % 12 = 1 ∨ (2 * n + 1) % 12 = 3 ∨ (2 * n + 1) % 12 = 5
            ∨ (2 * n + 1) % 12 = 7 ∨ (2 * n + 1) % 12 = 9 ∨ (2 * n + 1) % 12 = 11 := by omega
    rcases hr with h | h | h | h | h | h <;> rw [h] <;> decide
  have hfinal : 24 * Fsat n ((2 * n + 1 + 3) / 6) = 24 * ((2 * n + 1) ^ 2 / 24) := by
    rw [h24, hsq]; omega
  omega

/-- Ledger L11 (nonsaturated-branch domination), denominators cleared.
    With `n = p+q` and `2·C(p,2) = p(p−1)`: `(2n+1)² − 8(C(p,2)+pq) = 4q² + 8p + 4q + 1`. -/
theorem nonsat_domination_identity (p q : ℤ) :
    (2 * (p + q) + 1) ^ 2 - 4 * (p * (p - 1)) - 8 * (p * q)
      = 4 * q ^ 2 + 8 * p + 4 * q + 1 := by ring

/-- Hence the nonsaturated deficit is bounded: `8(C(p,2)+pq) ≤ (2n+1)²` (for `p,q ≥ 0`). -/
theorem nonsat_le (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    4 * (p * (p - 1)) + 8 * (p * q) ≤ (2 * (p + q) +