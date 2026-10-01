import E34.SetColoring

/-!
# E34 — Theorem 2 of arXiv:1902.06135: set colouring problems are testable

Counting form, sampling with repetition.  Let `P` be a set colouring problem on `Fin n` with
colours `Finset (Fin K)` and non-empty lists.  If every colouring `ψ` (with `ψ v ∈ L v`) has at
least `ε n²` ordered conflicting pairs, then at most half of the sequences `w : Fin s → Fin n`
have a proper colouring of their image, as soon as
`2 · (1 - ε/4)^s · (1 + 4 s 2^K / 3)^B ≤ 1` with `8K/ε < B + 1`.

Proof (Alon–Krivelevich, as adapted in the appendix of the paper, organised as a recursion):
`Fcount S φ t` counts the continuations `w` of length `t` of a proper partial colouring `(S, φ)`
that still admit a proper extension.  Splitting on the first vertex `v`: if `v` is not
successful the state is unchanged; if `v` is successful its colour `c ∈ Lφ` affects at least
`εn/4` vertices, so the potential `energy` drops by `εn/4` (`energy_insert`).  At least `εn/4`
vertices are successful (`card_succ`).  Hence `Fcount ≤ n^t · gb (1-ε/4) 2^K t b` where `b` is
the energy level and `gb r p t b ≤ r^t (1 + t p / r)^b`.
-/

namespace E34

open Finset

open scoped Classical

theorem card_cons_eq {X : Type*} [Fintype X] [DecidableEq X] (t : ℕ)
    (Q : (Fin (t + 1) → X) → Prop) [DecidablePred Q] :
    (univ.filter Q).card = ∑ v, (univ.filter (fun w' : Fin t → X => Q (Fin.cons v w'))).card := by
  rw [card_filter]
  simp_rw [card_filter]
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => X)) _ _ (fun p => rfl)).symm

theorem img_cons {n t : ℕ} (v : Fin n) (w : Fin t → Fin n) :
    img (Fin.cons v w : Fin (t + 1) → Fin n) = insert v (img w) := by
  ext x
  simp only [mem_img, mem_insert, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h

/-- The recursion bounding the normalised counts. -/
noncomputable def gb (r p : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | t + 1, 0 => r * gb r p t 0
  | t + 1, b + 1 => r * gb r p t (b + 1) + p * gb r p t b

/-- The previous level (`0` below level `0`). -/
noncomputable def gprev (r p : ℝ) (t : ℕ) : ℕ → ℝ
  | 0 => 0
  | b + 1 => gb r p t b

theorem gb_nonneg {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) : ∀ t b, 0 ≤ gb r p t b
  | 0, _ => by simp [gb]
  | t + 1, 0 => by simp only [gb]; exact mul_nonneg hr (gb_nonneg hr hp t 0)
  | t + 1, b + 1 => by
      simp only [gb]
      exact add_nonneg (mul_nonneg hr (gb_nonneg hr hp t _)) (mul_nonneg hp (gb_nonneg hr hp t _))

theorem gb_le {r p : ℝ} (hr : 0 < r) (hp : 0 ≤ p) :
    ∀ t b, gb r p t b ≤ r ^ t * (1 + t * p / r) ^ b
  | 0, b => by simp [gb]
  | t + 1, 0 => by
      simp only [gb, pow_zero, mul_one]
      have := gb_le hr hp t 0
      simp only [pow_zero, mul_one] at this
      rw [pow_succ]; nlinarith
  | t + 1, b + 1 => by
      simp only [gb]
      have h1 := gb_le hr hp t (b + 1)
      have h2 := gb_le hr hp t b
      have hx : 0 ≤ (t : ℝ) * p / r := by positivity
      have hy : (t : ℝ) * p / r ≤ ((t + 1 : ℕ) : ℝ) * p / r := by
        apply div_le_div_of_nonneg_right _ hr.le
        push_cast; nlinarith
      have hA : 0 ≤ r ^ t * (1 + t * p / r) ^ b := by positivity
      calc r * gb r p t (b + 1) + p * gb r p t b
          ≤ r * (r ^ t * (1 + t * p / r) ^ (b + 1)) + p * (r ^ t * (1 + t * p / r) ^ b) := by
            gcongr
        _ = r ^ (t + 1) * (1 + t * p / r) ^ b * (1 + (t * p + p) / r) := by
            have hrp : r * (p / r) = p := by field_simp
            have e : 1 + ((t : ℝ) * p + p) / r = (1 + t * p / r) + p / r := by ring
            rw [e]; linear_combination (-(r ^ t * (1 + t * p / r) ^ b)) * hrp
        _ = r ^ (t + 1) * (1 + t * p / r) ^ b * (1 + ((t + 1 : ℕ) : ℝ) * p / r) := by
            push_cast; ring
        _ ≤ r ^ (t + 1) * (1 + ((t + 1 : ℕ) : ℝ) * p / r) ^ b *
              (1 + ((t + 1 : ℕ) : ℝ) * p / r) := by gcongr
        _ = r ^ (t + 1) * (1 + ((t + 1 : ℕ) : ℝ) * p / r) ^ (b + 1) := by ring

namespace SetColoring

variable {n K : ℕ} (P : SetColoring n K)

/-- Continuations of length `t` of the partial colouring `(S, φ)` that admit a proper
extension. -/
noncomputable def Fcount (S : Finset (Fin n)) (φ : Fin n → Finset (Fin K)) (t : ℕ) : ℕ :=
  (univ.filter (fun w : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
    (∀ u ∈ S, ψ u = φ u) ∧ P.ProperOn ψ (S ∪ img w))).card

theorem properOn_insert {S : Finset (Fin n)} {φ : Fin n → Finset (Fin K)} (hφ : P.ProperOn φ S)
    {v : Fin n} (hv : v ∉ S) {c : Finset (Fin K)} (hc : c ∈ P.Lφ S φ v) :
    P.ProperOn (Function.update φ v c) (insert v S) := by
  rw [Lφ, mem_filter] at hc
  have hne : ∀ u ∈ S, u ≠ v := fun u hu h => hv (h ▸ hu)
  constructor
  · intro u hu
    rcases mem_insert.1 hu with rfl | hu
    · rw [Function.update_self]; exact hc.1
    · rw [Function.update_of_ne (hne u hu)]; exact hφ.1 u hu
  · intro u hu w hw huw
    by_cases hu' : u = v <;> by_cases hw' : w = v
    · exact absurd (hu'.trans hw'.symm) huw
    · subst hu'
      have hwS : w ∈ S := (mem_insert.1 hw).resolve_left hw'
      rw [Function.update_self, Function.update_of_ne hw']
      exact (P.compat_comm).1 (hc.2 w hwS (Ne.symm huw))
    · subst hw'
      have huS : u ∈ S := (mem_insert.1 hu).resolve_left hu'
      rw [Function.update_self, Function.update_of_ne hu']
      exact hc.2 u huS huw
    · have huS : u ∈ S := (mem_insert.1 hu).resolve_left hu'
      have hwS : w ∈ S := (mem_insert.1 hw).resolve_left hw'
      rw [Function.update_of_ne hu', Function.update_of_ne hw']
      exact hφ.2 u huS w hwS huw

theorem branch_same (S : Finset (Fin n)) (φ : Fin n → Finset (Fin K)) (t : ℕ) (v : Fin n) :
    (univ.filter (fun w' : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
      (∀ u ∈ S, ψ u = φ u) ∧ P.ProperOn ψ (S ∪ img (Fin.cons v w' : Fin (t + 1) → Fin n)))).card
      ≤ P.Fcount S φ t := by
  unfold Fcount
  apply card_le_card
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  obtain ⟨ψ, h1, h2⟩ := hw
  refine ⟨ψ, h1, ProperOn.mono P h2 ?_⟩
  rw [img_cons]
  exact union_subset_union (Subset.refl _) (subset_insert _ _)

theorem branch_succ (S : Finset (Fin n)) (φ : Fin n → Finset (Fin K)) (t : ℕ) (v : Fin n)
    (hv : v ∉ S) :
    (univ.filter (fun w' : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
      (∀ u ∈ S, ψ u = φ u) ∧ P.ProperOn ψ (S ∪ img (Fin.cons v w' : Fin (t + 1) → Fin n)))).card
      ≤ ∑ c ∈ P.Lφ S φ v, P.Fcount (insert v S) (Function.update φ v c) t := by
  refine (card_le_card (t := (P.Lφ S φ v).biUnion (fun c => univ.filter
    (fun w : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
      (∀ u ∈ insert v S, ψ u = Function.update φ v c u) ∧ P.ProperOn ψ (insert v S ∪ img w))))
    ?_).trans (card_biUnion_le.trans (le_of_eq rfl))
  intro w hw
  obtain ⟨ψ, h1, h2⟩ := (mem_filter.1 hw).2
  have hvS : v ∈ S ∪ img (Fin.cons v w : Fin (t + 1) → Fin n) := by
    rw [img_cons]; exact mem_union_right _ (mem_insert_self _ _)
  refine mem_biUnion.2 ⟨ψ v, ?_, ?_⟩
  · rw [Lφ, mem_filter]
    refine ⟨h2.1 v hvS, fun u hu huv => ?_⟩
    have := h2.2 u (mem_union_left _ hu) v hvS huv
    rwa [h1 u hu] at this
  · rw [mem_filter]
    refine ⟨mem_univ _, ψ, ?_, ProperOn.mono P h2 ?_⟩
    · intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · rw [Function.update_self]
      · rw [Function.update_of_ne (fun h => hv (by rw [← h]; exact hu))]; exact h1 u hu
    · rw [img_cons]
      intro x hx
      rcases mem_union.1 hx with h | h
      · rcases mem_insert.1 h with rfl | h
        · exact mem_union_right _ (mem_insert_self _ _)
        · exact mem_union_left _ h
      · exact mem_union_right _ (mem_insert_of_mem h)

theorem card_colours_le (S : Finset (Fin n)) (φ : Fin n → Finset (Fin K)) (v : Fin n) :
    (P.Lφ S φ v).card ≤ 2 ^ K := by
  simpa using card_le_univ (P.Lφ S φ v)

/-- **The main recursion** of the proof of Theorem 2. -/
theorem Fcount_le (hLne : ∀ v, (P.L v).Nonempty) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfar : ∀ ψ : Fin n → Finset (Fin K), (∀ v, ψ v ∈ P.L v) → ε * (n : ℝ) ^ 2 ≤ P.conf ψ) :
    ∀ (t b : ℕ) (S : Finset (Fin n)) (φ : Fin n → Finset (Fin K)), P.ProperOn φ S →
      (P.energy S φ : ℝ) < (b + 1) * (ε * n / 4) →
      (P.Fcount S φ t : ℝ) ≤ (n : ℝ) ^ t * gb (1 - ε / 4) (2 ^ K) t b := by
  have hr : 0 ≤ 1 - ε / 4 := by linarith
  have hp : (0 : ℝ) ≤ 2 ^ K := by positivity
  intro t
  induction t with
  | zero =>
    intro b S φ _ _
    simp only [pow_zero, gb, mul_one]
    have : P.Fcount S φ 0 ≤ 1 := by
      unfold Fcount; exact (card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  | succ t ih =>
    intro b S φ hφ hE
    have hsucc := P.card_succ S φ hLne ε hε.le hfar hφ
    set sc := P.succ S φ ε
    have hscn : (sc.card : ℝ) ≤ n := by exact_mod_cast (card_le_univ sc).trans (by simp)
    -- the successful branch
    have hbr : ∀ v ∈ sc, ((univ.filter (fun w' : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
        (∀ u ∈ S, ψ u = φ u) ∧ P.ProperOn ψ (S ∪ img (Fin.cons v w' : Fin (t + 1) → Fin n)))).card
          : ℝ) ≤ 2 ^ K * ((n : ℝ) ^ t * gprev (1 - ε / 4) (2 ^ K) t b) := by
      intro v hv
      have hvS : v ∉ S := mem_compl.1 (mem_filter.1 hv).1
      have hvs := (mem_filter.1 hv).2
      have h1 := P.branch_succ S φ t v hvS
      have hc : ∀ c ∈ P.Lφ S φ v, (P.Fcount (insert v S) (Function.update φ v c) t : ℝ) ≤
          (n : ℝ) ^ t * gprev (1 - ε / 4) (2 ^ K) t b := by
        intro c hc
        have hdrop := P.energy_insert S φ v hvS c
        have ha := hvs c hc
        have hdrop' : (P.energy (insert v S) (Function.update φ v c) : ℝ) +
            (P.affS S φ v c).card ≤ P.energy S φ := by exact_mod_cast hdrop
        cases b with
        | zero =>
          exfalso
          have h0 : (0 : ℝ) ≤ P.energy (insert v S) (Function.update φ v c) := by positivity
          linarith
        | succ b' =>
          show _ ≤ _ * gb (1 - ε / 4) (2 ^ K) t b'
          apply ih b' _ _ (P.properOn_insert hφ hvS hc)
          push_cast at hE ⊢
          linarith
      have hsum : (∑ c ∈ P.Lφ S φ v, (P.Fcount (insert v S) (Function.update φ v c) t : ℝ)) ≤
          (P.Lφ S φ v).card * ((n : ℝ) ^ t * gprev (1 - ε / 4) (2 ^ K) t b) := by
        rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hc
      have hcard : ((P.Lφ S φ v).card : ℝ) ≤ 2 ^ K := by exact_mod_cast P.card_colours_le S φ v
      have hnn : 0 ≤ (n : ℝ) ^ t * gprev (1 - ε / 4) (2 ^ K) t b := by
        cases b with
        | zero => simp [gprev]
        | succ b' => exact mul_nonneg (by positivity) (gb_nonneg hr hp t b')
      calc _ ≤ (∑ c ∈ P.Lφ S φ v, (P.Fcount (insert v S) (Function.update φ v c) t : ℝ)) := by
            exact_mod_cast h1
        _ ≤ _ := hsum
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard hnn
    have hsame : ∀ v, ((univ.filter (fun w' : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
        (∀ u ∈ S, ψ u = φ u) ∧ P.ProperOn ψ (S ∪ img (Fin.cons v w' : Fin (t + 1) → Fin n)))).card
          : ℝ) ≤ (n : ℝ) ^ t * gb (1 - ε / 4) (2 ^ K) t b := by
      intro v
      have h := P.branch_same S φ t v
      have h' : ((univ.filter (fun w' : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
        (∀ u ∈ S, ψ u = φ u) ∧ P.ProperOn ψ (S ∪ img (Fin.cons v w' : Fin (t + 1) → Fin n)))).card
          : ℝ) ≤ P.Fcount S φ t := by exact_mod_cast h
      exact h'.trans (ih b S φ hφ hE)
    -- assemble
    set X : ℝ := (n : ℝ) ^ t * gb (1 - ε / 4) (2 ^ K) t b
    set Y : ℝ := (n : ℝ) ^ t * gprev (1 - ε / 4) (2 ^ K) t b
    have hX : 0 ≤ X := mul_nonneg (by positivity) (gb_nonneg hr hp t b)
    have hY : 0 ≤ Y := by
      cases b with
      | zero => simp [Y, gprev]
      | succ b' => exact mul_nonneg (by positivity) (gb_nonneg hr hp t b')
    have hsplit : (P.Fcount S φ (t + 1) : ℝ) ≤ (n - sc.card) * X + n * (2 ^ K * Y) := by
      unfold Fcount
      rw [card_cons_eq]
      push_cast
      rw [← sum_filter_add_sum_filter_not univ (fun v => v ∈ sc)]
      have e1 : ∑ v ∈ univ.filter (fun v => v ∈ sc),
          ((univ.filter (fun w' : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
            (∀ u ∈ S, ψ u = φ u) ∧ P.ProperOn ψ (S ∪ img (Fin.cons v w' : Fin (t + 1) → Fin n)))).card
              : ℝ) ≤ ∑ _v ∈ univ.filter (fun v => v ∈ sc), 2 ^ K * Y :=
        sum_le_sum (fun v hv => hbr v (mem_filter.1 hv).2)
      have e2 : ∑ v ∈ univ.filter (fun v => v ∉ sc),
          ((univ.filter (fun w' : Fin t → Fin n => ∃ ψ : Fin n → Finset (Fin K),
            (∀ u ∈ S, ψ u = φ u) ∧ P.ProperOn ψ (S ∪ img (Fin.cons v w' : Fin (t + 1) → Fin n)))).card
              : ℝ) ≤ ∑ _v ∈ univ.filter (fun v => v ∉ sc), X :=
        sum_le_sum (fun v _ => hsame v)
      have hc1 : (univ.filter (fun v => v ∈ sc)).card = sc.card := by
        congr 1; ext v; simp
      have hc2 : ((univ.filter (fun v => v ∉ sc)).card : ℝ) = n - sc.card := by
        have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun v => v ∈ sc)
        rw [card_univ, Fintype.card_fin, hc1] at this
        have : (univ.filter (fun v => v ∉ sc)).card = n - sc.card := by omega
        rw [this, Nat.cast_sub (by omega)]
      have e1' : ∑ _v ∈ univ.filter (fun v => v ∈ sc), (2 : ℝ) ^ K * Y = sc.card * (2 ^ K * Y) := by
        rw [sum_const, nsmul_eq_mul, hc1]
      have e2' : ∑ _v ∈ univ.filter (fun v => v ∉ sc), X = (n - sc.card) * X := by
        rw [sum_const, nsmul_eq_mul, hc2]
      have : (sc.card : ℝ) * (2 ^ K * Y) ≤ n * (2 ^ K * Y) :=
        mul_le_mul_of_nonneg_right hscn (by positivity)
      linarith
    have hfin : (n - sc.card : ℝ) * X ≤ (n : ℝ) * (1 - ε / 4) * X :=
      mul_le_mul_of_nonneg_right (by linarith) hX
    calc (P.Fcount S φ (t + 1) : ℝ) ≤ (n - sc.card) * X + n * (2 ^ K * Y) := hsplit
      _ ≤ (n : ℝ) * (1 - ε / 4) * X + n * (2 ^ K * Y) := by linarith
      _ = (n : ℝ) ^ (t + 1) * gb (1 - ε / 4) (2 ^ K) (t + 1) b := by
          cases b with
          | zero => simp only [X, Y, gb, gprev]; ring
          | succ b' => simp only [X, Y, gb, gprev]; ring

/-- **Theorem 2 of arXiv:1902.06135** (counting form, sampling with repetition, explicit
condition on the sample size). -/
theorem thm2 (hLne : ∀ v, (P.L v).Nonempty) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfar : ∀ ψ : Fin n → Finset (Fin K), (∀ v, ψ v ∈ P.L v) → ε * (n : ℝ) ^ 2 ≤ P.conf ψ)
    (s B : ℕ) (hB : 8 * K / ε < B + 1)
    (hs : 2 * (1 - ε / 4) ^ s * (1 + s * 2 ^ K / (1 - ε / 4)) ^ B ≤ 1) :
    2 * (univ.filter (fun w : Fin s → Fin n => ∃ ψ : Fin n → Finset (Fin K),
      P.ProperOn ψ (img w))).card ≤ n ^ s := by
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; norm_num at hs
    · exact h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : IsEmpty (Fin s → Fin 0) := ⟨fun w => (w ⟨0, hs0⟩).elim0⟩
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : (P.energy ∅ (fun _ => ∅) : ℝ) < (B + 1) * (ε * n / 4) := by
    have h1 : (P.energy ∅ (fun _ => ∅) : ℝ) ≤ 2 * K * n := by exact_mod_cast P.energy_le _ _
    have h2 : 8 * K < (B + 1) * ε := by rwa [div_lt_iff₀ hε] at hB
    nlinarith
  have hprop : P.ProperOn (fun _ => ∅) ∅ := ⟨fun v hv => absurd hv (notMem_empty v),
    fun u hu => absurd hu (notMem_empty u)⟩
  have h := P.Fcount_le hLne ε hε hε1 hfar s B ∅ (fun _ => ∅) hprop hE
  have hr : 0 < 1 - ε / 4 := by linarith
  have hg := gb_le hr (by positivity : (0 : ℝ) ≤ 2 ^ K) s B
  have heq : P.Fcount ∅ (fun _ => ∅) s = (univ.filter (fun w : Fin s → Fin n =>
      ∃ ψ : Fin n → Finset (Fin K), P.ProperOn ψ (img w))).card := by
    unfold Fcount; congr 1; ext w; simp
  rw [← heq]
  have : (2 * P.Fcount ∅ (fun _ => ∅) s : ℝ) ≤ (n : ℝ) ^ s := by
    have hns : (0 : ℝ) ≤ (n : ℝ) ^ s := by positivity
    calc (2 * P.Fcount ∅ (fun _ => ∅) s : ℝ) ≤ 2 * ((n : ℝ) ^ s *
          ((1 - ε / 4) ^ s * (1 + s * 2 ^ K / (1 - ε / 4)) ^ B)) := by
          have := mul_le_mul_of_nonneg_left hg hns
          linarith
      _ = (n : ℝ) ^ s * (2 * (1 - ε / 4) ^ s * (1 + s * 2 ^ K / (1 - ε / 4)) ^ B) := by ring
      _ ≤ (n : ℝ) ^ s * 1 := mul_le_mul_of_nonneg_left hs hns
      _ = (n : ℝ) ^ s := mul_one _
  exact_mod_cast this

end SetColoring

end E34
