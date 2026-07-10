import PaperII.L6
import PaperII.L10
import PaperII.CompleteSplitChordal

/-!
# Paper II — Assembly of Theorem 1.2 (ledger L12)

`max_{|V|=n, G chordal} (|E(G)| − 2·τ₃*(G)) = ⌊(2n+1)²/24⌋`, rendered as
`(upper bound: ∀ chordal G with card = n, Φτ G ≤ floor) ∧ (attainment: some chordal G attains floor)`.

Path 3: conditional on `A2Transfer` (and `ChordalStructure` per graph). The attainment witness is a
genuine complete-split whose chordality is PROVEN (`chordalStructure_completeSplit`), not assumed — so
reachability adds no hypothesis.
-/

open scoped BigOperators

namespace PaperII

/-- Sub-lemma 1 (structural, path (a)): every complete-split graph is chordal. The Dirac-family
facts A1/A3 are proven directly (an independent-side vertex, if any, is simplicial; else any vertex
of the induced clique). Proven, not assumed. A4 (clique tree) is no longer needed — L7 is
clique-tree-free. -/
def chordalStructure_completeSplit (p q : ℕ) : ChordalStructure (completeSplit p q) where
  isChordal := isChordal_completeSplit p q
  simplicial_hereditary := completeSplit_simplicial_hereditary p q
  two_nonadj_simplicial := completeSplit_two_nonadj_simplicial p q

/-
Degenerate branch `p ≤ 1`: `Φτ(S_{p,q}) = F_{p+q}(p)` (both sides `= p·q`; `τ₃* = 0`, `C(p,2)=0`).
-/
theorem phiTau_completeSplit_eq_Fsat_of_le_one (p q : ℕ) (hp : p ≤ 1) :
    phiTau (completeSplit p q) = ((Fsat ((p : ℤ) + q) p : ℤ) : ℝ) := by
  unfold phiTau Fsat;
  interval_cases p <;> norm_num [ twoFsat ];
  · convert tau3star_completeSplit_of_le_one 0 q ( by norm_num ) using 1;
    rw [ tau3star_completeSplit_of_le_one ] <;> norm_num;
    ext ⟨ a, ha ⟩ ⟨ b, hb ⟩ ; aesop;
    · contradiction;
    · contradiction;
    · simp +decide;
  · rw [ tau3star_completeSplit_of_le_one ] <;> norm_num [ completeSplit_card_edgeFinset ]
    rw [ show (2 * (1 + (q : ℤ)) + 1 - 3) / 2 = (q : ℤ) from by omega ]
    norm_cast

/-
The maximizer value: `F_n((2n+1+3)/6) = ⌊(2n+1)²/24⌋` (the witness of `exists_Fsat_eq_floor`).
-/
theorem Fsat_witness_eq_floor (n : ℤ) :
    Fsat n ((2 * n + 1 + 3) / 6) = (2 * n + 1) ^ 2 / 24 := by
  unfold Fsat;
  unfold twoFsat; ring_nf;
  rw [ ← Int.emod_add_mul_ediv n 6 ] ; have := Int.emod_nonneg n ( by decide : ( 6 : ℤ ) ≠ 0 ) ; have := Int.emod_lt_of_pos n ( by decide : ( 6 : ℤ ) > 0 ) ; interval_cases n % 6 <;> norm_num <;> ring_nf ;
  all_goals norm_num [ show ( 4 + n / 6 * 12 ) / 6 = 2 * ( n / 6 ) + 0 by omega, show ( 6 + n / 6 * 12 ) / 6 = 2 * ( n / 6 ) + 1 by omega, show ( 8 + n / 6 * 12 ) / 6 = 2 * ( n / 6 ) + 1 by omega, show ( 10 + n / 6 * 12 ) / 6 = 2 * ( n / 6 ) + 1 by omega, show ( 12 + n / 6 * 12 ) / 6 = 2 * ( n / 6 ) + 2 by omega, show ( 14 + n / 6 * 12 ) / 6 = 2 * ( n / 6 ) + 2 by omega ] ; ring_nf ;
  all_goals omega;

/-
Sub-lemma 2 (both branches): `Φτ(S_{p,q}) ≤ ⌊(2(p+q)+1)²/24⌋`.
Saturated branch via `phiTau_completeSplit_sat_eq_Fsat` + `Fsat_le_floor`; nonsaturated via
`phiTau_completeSplit_unsat` + `nonsat_le`.
-/
theorem phiTau_completeSplit_le_floor (p q : ℕ) :
    phiTau (completeSplit p q) ≤ (((2 * ((p : ℤ) + q) + 1) ^ 2 / 24 : ℤ) : ℝ) := by
  by_cases hp : p ≤ 1;
  · interval_cases p <;> norm_num [ phiTau_completeSplit_eq_Fsat_of_le_one ]; all_goals exact Fsat_le_floor _ _;
  · by_cases hpq : p - 1 ≤ q;
    · rw [ phiTau_completeSplit_sat_eq_Fsat p q ( by linarith ) hpq ];
      exact_mod_cast Fsat_le_floor ( p + q ) p;
    · by_cases hpq : p ≥ 3;
      · have := nonsat_le_floor_int p q ( by linarith ) ( by linarith );
        rw [ phiTau_completeSplit_unsat p q hpq ( by omega ) ];
        rw [ div_le_iff₀ ] <;> norm_cast;
        rw [ Nat.choose_two_right ];
        cases p <;> norm_num at * ; linarith [ Nat.div_mul_le_self ( Nat.succ ‹_› * ‹_› ) 2 ];
      · interval_cases p ; norm_num at *;
        subst_vars; norm_num [ tau3star_completeSplit_two_zero ] ;
        unfold phiTau; norm_num [ completeSplit_card_edgeFinset, tau3star_completeSplit_two_zero ] ;

/-
Sub-lemma 3 (reachability): the maximizer `p₀ = (2n+1+3)/6` is valid (`p₀+q=n`, `q≥0`) and
SATURATED (`q ≥ p₀−1`), so `phiTau_completeSplit_sat_eq_Fsat` applies and gives `Φτ = ⌊(2n+1)²/24⌋`.
The saturation/validity of `p₀` must be proven arithmetically (check small `n=1,2`).
-/
theorem exists_completeSplit_eq_floor (n : ℕ) (hn : 1 ≤ n) :
    ∃ p q : ℕ, p + q = n ∧
      phiTau (completeSplit p q) = (((2 * (n : ℤ) + 1) ^ 2 / 24 : ℤ) : ℝ) := by
  -- Set `p := P.toNat`, `q := n - p` (natural subtraction).
  let P := (2 * (n : ℤ) + 1 + 3) / 6
  set p := P.toNat
  set q := n - p;
  -- Prove that `p` is valid and saturated.
  have hp_valid : p + q = n := by
    grind
  have hp_sat : p - 1 ≤ q := by
    omega
  have hp_ge_two : 2 ≤ p ∨ p ≤ 1 := by
    exact Classical.or_iff_not_imp_left.2 fun h => by omega;
  generalize_proofs at *; (
  -- Prove that ` phiTau (completeSplit p q) = ((Fsat (n:ℤ) P : ℤ):ℝ)`.
  have h_phiTau : phiTau (completeSplit p q) = ((Fsat (n : ℤ) P : ℤ) : ℝ) := by
    cases hp_ge_two <;> simp_all +decide [ phiTau_completeSplit_sat_eq_Fsat, phiTau_completeSplit_eq_Fsat_of_le_one ];
    · rw [ ← hp_valid ] ; norm_cast;
    · grind
  generalize_proofs at *; (
  exact ⟨ p, q, hp_valid, h_phiTau.trans ( mod_cast Fsat_witness_eq_floor n ) ⟩))

/-- **Theorem 1.2**, conditional on the chordal-structure hypotheses (`ChordalStructure` per graph +
`A2Transfer`): the chordal maximum of `Φτ` over `n`-vertex graphs equals `⌊(2n+1)²/24⌋` (upper bound ∧
attainment). Renamed in Fase 5 (`…_of_chordalStructure`); `PaperII.Unconditional.theorem_1_2` feeds it
the discharged hypotheses to obtain the unconditional statement. -/
theorem theorem_1_2_of_chordalStructure (n : ℕ) (hn : 1 ≤ n)
    (hA2 : ∀ {W : Type} [Fintype W] [DecidableEq W], A2Transfer W) :
    (∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
        Fintype.card W = n → ChordalStructure G →
        phiTau G ≤ (((2 * (n : ℤ) + 1) ^ 2 / 24 : ℤ) : ℝ))
    ∧
    (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
        Fintype.card W = n ∧ Nonempty (ChordalStructure G) ∧
        phiTau G = (((2 * (n : ℤ) + 1) ^ 2 / 24 : ℤ) : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro W _ _ G _ hcard hchord
    obtain ⟨p, q, hpq, hle⟩ := symmetrization hA2 G hchord
    have hn' : (p : ℤ) + q = n := by
      have hpqn : p + q = n := by rw [hpq, hcard]
      exact_mod_cast hpqn
    calc phiTau G ≤ phiTau (completeSplit p q) := hle
      _ ≤ (((2 * ((p : ℤ) + q) + 1) ^ 2 / 24 : ℤ) : ℝ) := phiTau_completeSplit_le_floor p q
      _ = (((2 * (n : ℤ) + 1) ^ 2 / 24 : ℤ) : ℝ) := by rw [hn']
  · obtain ⟨p, q, hpq, hval⟩ := exists_completeSplit_eq_floor n hn
    refine ⟨Fin p ⊕ Fin q, inferInstance, inferInstance, completeSplit p q, inferInstance, ?_,
      ⟨chordalStructure_completeSplit p q⟩, hval⟩
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hpq]

end PaperII