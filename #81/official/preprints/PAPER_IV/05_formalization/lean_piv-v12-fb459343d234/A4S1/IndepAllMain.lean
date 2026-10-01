import A4S1.IndepAllBudget

/-!
# E14, G2: `A4Sharp s` for every rooted defect `s` through the independent constructor

* `AllInput.partition`: the normalized data of E10 have an order-four clique partition with at
  most `Q_s(n)` pieces, now through **`A4S1.Indep.caseA_indep`** (absorption by balanced
  selection, RD09 phase I by cyclic-shift averaging and the multi-host lift, phase II by dyadic
  Galvin hosting), the capacities (`AllInput.params`, with the list condition of
  `caseA_indep`), the joint exact accounting (`AllInput.hkey`) and the final count
  (`own_final_all`).
* `minDegTerminal_all_indep s : ∃ eps > 0, MinDegTerminal s eps`.
* `a4Sharp_all_indep s : A4Sharp s`, through `a4Sharp_of_minDegTerminal`.

No module of the families `A4S1.T1*`, `A4S1.TS*`, nor `A4S1.TerminalTwoPhase`,
`A4S1.TerminalTolerantTwoPhase`, `A4S1.TerminalTolerant*`, `A4S1.OwnAllConstructor`,
`A4S1.OwnAllPairs` (or anything importing them) is in the import cone of this module; see
`A4S1/IndepAllAudit.lean` and `data/E14_RESULTS.md`.
-/

namespace A4S1.IndepAll

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect A4S1.TerminalPacking
  PaperIV.DefectTargetArithmetic

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {A : Finset V} {s : ℕ}

/-- **The terminal for the normalized data, through the independent constructor.** -/
theorem AllInput.partition (h : AllInput G A s) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s (Fintype.card V) := by
  obtain ⟨k, q, σ, τ, D, L, hσ, hτ, hΔ, hck, hθ, hq, hb, hD, hL, hLq⟩ := h.params
  have htot := card_total (G := G) (A := A) (s := s)
  have hSlo := h.card_core_lo
  have hHlo := h.card_host_lo
  have hv := h.v_pos; have hvw := h.v_le_w; have hwn := h.w_le_n
  have hSw := h.S_le_w'
  have hS1 := (S_ge_one (s := s))
  have hS3 : 3 ≤ (pCore G A s).card := by
    have : (3 : ℚ) ≤ (pCore G A s).card := by nlinarith
    exact_mod_cast this
  have hm : s + 2 ≤ (pCore G A s).card + (pHost G A s).card := by
    have : ((s + 2 : ℕ) : ℚ) ≤ (pCore G A s).card + (pHost G A s).card := by
      push_cast; nlinarith
    exact_mod_cast this
  have hσ' : ∀ v ∈ pHost G A s, ((pCore G A s).filter fun u => ¬ G.Adj v u).card +
      (pT G A s).card ≤ σ := fun v hv => by have := hσ v hv; omega
  have hτ' : ∀ u ∈ pCore G A s, ((pHost G A s).filter fun v => ¬ G.Adj u v).card +
      (pT G A s).card ≤ τ := fun u hu => by have := hτ u hu; omega
  have hk : 0 < k := by omega
  obtain ⟨Q, hQ4, hQ⟩ := A4S1.Indep.caseA_indep (pCore G A s) (pHost G A s) (pT G A s)
    core_host_disjoint core_T_disjoint host_T_disjoint cover k q σ τ D hk
    hσ' hτ' hΔ hck hθ hq hb hD
  have hsq : Nat.sqrt D ≤ L := (Nat.sqrt_lt.2 hL).le
  have hQ' : Q.size + (inEdges G (pCore G A s)).card +
      2 * ∑ w ∈ pT G A s, min ((pCore G A s).filter (G.Adj w)).card
        ((pHost G A s).filter (G.Adj w)).card ≤
      (pCore G A s).card * (pHost G A s).card + ∑ w ∈ pT G A s, G.degree w +
        2 * (pT G A s).card * (L + (pT G A s).card) := by
    have : 2 * (pT G A s).card * ((pT G A s).card + Nat.sqrt D) ≤
        2 * (pT G A s).card * (L + (pT G A s).card) := Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨Q, hQ4, ?_⟩
  rw [← htot]
  exact own_final_all _ _ _ _ _ _ _ _ _ hm hQ' (h.hkey L hLq)

end A4S1.IndepAll

namespace A4S1.IndepAll

open Finset

theorem all_missingIncidences_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) :
    PaperIV.RootVocab.missingIncidences G A =
      ∑ a ∈ A, ((univ \ A).filter fun y => ¬ G.Adj a y).card := by
  unfold PaperIV.RootVocab.missingIncidences PaperIV.RootVocab.missingColumn
    PaperIV.RootVocab.outsideVertices
  congr 1

theorem all_card_outsideEdges_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) :
    (PaperIV.RootVocab.outsideEdges G A).card =
      (A4S1.TerminalPacking.inEdges G (univ \ A)).card := by
  unfold PaperIV.RootVocab.outsideEdges PaperIV.RootVocab.outsideVertices
  congr 1
  ext e
  simp only [A4S1.TerminalPacking.inEdges, mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun v hv => h2 (Sym2.mem_toFinset.2 hv)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun v hv => h2 v (Sym2.mem_toFinset.1 hv)⟩

/-- **E14: the terminal at every rooted defect `s`, through the independent constructor**
(normalization, `(m, d)` classification, obstruction `(O_s)`, Erdős–Gallai, joint incidence by
peeling and joint exact accounting of E10; constructor `A4S1.Indep.caseA_indep`). -/
theorem minDegTerminal_all_indep (s : ℕ) :
    ∃ eps : ℚ, 0 < eps ∧ A4S1.MinDegreeAll.MinDegTerminal s eps := by
  refine ⟨epsS s, epsS_pos, ⌈(10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 8⌉₊,
    fun n hn G _ hG hdeg _ hL => ?_⟩
  obtain ⟨L⟩ := hL
  have hnq : (10 : ℚ) ^ 50 * ((s : ℚ) + 1) ^ 8 ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]; exact (Nat.ceil_le.1 hn)
  have hsz := abs_le.1 L.size_window
  have hmass := L.mass_small
  have h0 : (0 : ℚ) ≤ ((PaperIV.RootVocab.outsideEdges G L.core).card : ℚ) := by positivity
  have h1 : (0 : ℚ) ≤ ((PaperIV.RootVocab.missingIncidences G L.core : ℕ) : ℚ) := by positivity
  have hin : AllInput G L.core s :=
    { rd := hG
      hn := hnq
      deg := by rw [Fintype.card_fin]; exact hdeg
      clique := L.isClique
      size_lo := by rw [Fintype.card_fin]; linarith
      size_hi := by rw [Fintype.card_fin]; linarith
      miss := by rw [← all_missingIncidences_eq, Fintype.card_fin]; linarith
      out := by rw [← all_card_outsideEdges_eq, Fintype.card_fin]; linarith }
  obtain ⟨Q, hQ4, hQ⟩ := hin.partition
  exact ⟨Q, hQ4, by simpa using hQ⟩

/-- The statement of `A4S1.MinDegTarget.minDegTerminal_ge_two`, proved through the independent
constructor. The hypothesis `2 ≤ s` is kept only because it is part of that statement; the proof
does not need it (`minDegTerminal_all_indep` holds for every `s`). -/
theorem minDegTerminal_ge_two_indep (s : ℕ) (_hs : 2 ≤ s) :
    ∃ eps : ℚ, 0 < eps ∧ A4S1.MinDegreeAll.MinDegTerminal s eps :=
  minDegTerminal_all_indep s

/-- **G2: the literal A4 target at every rooted defect `s`**, through the independent
constructor `A4S1.Indep.caseA_indep`; same statement as `A4S1.OwnAll.a4Sharp_all_own`. -/
theorem a4Sharp_all_indep (s : ℕ) : PaperIV.A4AllDefects.A4Sharp s := by
  obtain ⟨eps, heps, h⟩ := minDegTerminal_all_indep s
  exact A4S1.MinDegreeAll.a4Sharp_of_minDegTerminal s heps h

end A4S1.IndepAll
