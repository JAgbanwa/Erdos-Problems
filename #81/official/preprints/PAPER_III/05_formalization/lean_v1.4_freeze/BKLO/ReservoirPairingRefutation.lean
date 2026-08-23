/-
# The protected level defeats the reservoir clause when it is small.

This file records a defect of `BKLO.ReservoirClauseR` — and hence of its pairing form
`BKLO.ReservoirPairingClause` — that is independent of every defect already recorded in
`BKLO/ReservoirRefutation.lean` and `BKLO/ReservoirRefutationLink.lean`.

The clause quantifies over **all** triples `W'' ⊆ W' ⊆ W` with `K|W''| ≤ |W'|`.  Nothing there
forces `W''` to be large; `|W''| = 1` is allowed.  But the repaired link cover is asked, at every
`v ∈ W'`, for

  `|resLink (famEdges Q) W'' v| ≤ γ|W''|`   with   `γ = ε/8 ≤ 1/800`,

so for `|W''| = 1` the cover may use **no** edge at all running into `W''`.  And it must: the
perturbed link system `X` is only constrained relative to the reservoir by the perturbation scale
`2η|W|`, which is `≥ 1` once `|W|` is large, so a single vertex `a ∈ W''` may be added to the link
of a single outer vertex `u₀`.  The crossing edge `s(u₀, a)` then has to be covered, and the only
triangles allowed are `{u₀, a, b}` with `b ∈ W'` — the third edge `s(a, b)` runs into `W''` at `b`.

So `BKLO.ReservoirClauseResidual` is false, and with it `BKLO.ReservoirPairingResidual`
(`BKLO.reservoirClauseResidual_of_pairingResidual` contraposed): the `loadInner` field of
`BKLO.IsPairedLinkSystem` cannot be met at a singleton protected level.

The defect is in the *quantifier*, not in the mathematics of §10: in the engine the protected level
`W''` is the next vortex level, of size at least `n₂`, and for `|W''| ≥ 8/ε` the bound `γ|W''| ≥ 1`
leaves exactly the room the cover needs.  The repaired residual, which adds that hypothesis, is
`BKLO.ReservoirPairingResidualLarge` of `BKLO/ReservoirPairingLarge.lean`.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirPairing
import BKLO.ReservoirRepairedSat

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Trimming a link to even size -/

/-- A finite set has an even subset omitting at most one of its elements, and containing any
prescribed element as soon as the set has at least two. -/
theorem exists_even_subset_of_two_le {S : Finset V} {a : V} (haS : a ∈ S) (h2 : 2 ≤ S.card) :
    ∃ T ⊆ S, a ∈ T ∧ Even T.card ∧ (S \ T).card ≤ 1 := by
  classical
  by_cases hev : Even S.card
  · exact ⟨S, Finset.Subset.refl _, haS, hev, by simp⟩
  · obtain ⟨k, hk⟩ : Odd S.card := Nat.not_even_iff_odd.1 hev
    have h3 : 3 ≤ S.card := by omega
    have hne : (S.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem haS]; omega
    obtain ⟨b, hb⟩ := hne
    obtain ⟨hba, hbS⟩ := Finset.mem_erase.1 hb
    refine ⟨S.erase b, Finset.erase_subset _ _, Finset.mem_erase.2 ⟨Ne.symm hba, haS⟩, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hbS]
      exact ⟨k, by omega⟩
    · have hsub : S \ S.erase b ⊆ {b} := by
        intro z hz
        obtain ⟨hzS, hz'⟩ := Finset.mem_sdiff.1 hz
        by_cases hzb : z = b
        · simp [hzb]
        · exact absurd (Finset.mem_erase.2 ⟨hzb, hzS⟩) hz'
      exact le_trans (Finset.card_le_card hsub) (by simp)

/-- A finite set has an even subset omitting at most one of its elements. -/
theorem exists_even_subset (S : Finset V) :
    ∃ T ⊆ S, Even T.card ∧ (S \ T).card ≤ 1 := by
  classical
  by_cases hev : Even S.card
  · exact ⟨S, Finset.Subset.refl _, hev, by simp⟩
  · obtain ⟨k, hk⟩ : Odd S.card := Nat.not_even_iff_odd.1 hev
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨b, hb⟩ := hne
    refine ⟨S.erase b, Finset.erase_subset _ _, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hb]; exact ⟨k, by omega⟩
    · have hsub : S \ S.erase b ⊆ {b} := by
        intro z hz
        obtain ⟨hzS, hz'⟩ := Finset.mem_sdiff.1 hz
        by_cases hzb : z = b
        · simp [hzb]
        · exact absurd (Finset.mem_erase.2 ⟨hzb, hzS⟩) hz'
      exact le_trans (Finset.card_le_card hsub) (by simp)

/-! ### A triangle through a prescribed edge has a third vertex -/

/-- A triangle containing the edge `s(u, a)`, with `u ≠ a`, has a third vertex, and the two other
edges of the triangle are edges of the triangle. -/
theorem exists_third_vertex {t : Finset V} (h3 : t.card = 3) {u a : V}
    (hu : u ∈ t) (ha : a ∈ t) (hua : u ≠ a) :
    ∃ b ∈ t, b ≠ u ∧ b ≠ a := by
  classical
  have hsub : ({u, a} : Finset V) ⊆ t := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact hu
    · rw [Finset.mem_singleton] at hz'; exact hz' ▸ ha
  have hcard : ({u, a} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hua), Finset.card_singleton]
  have hss : ({u, a} : Finset V) ⊂ t := by
    refine Finset.ssubset_iff_of_subset hsub |>.2 ?_
    by_contra hcon
    push_neg at hcon
    have : t ⊆ ({u, a} : Finset V) := fun z hz => by
      by_contra hz'
      exact hz' (hcon z hz)
    have := Finset.card_le_card this
    omega
  obtain ⟨b, hbt, hb⟩ := Finset.exists_of_ssubset hss
  refine ⟨b, hbt, ?_, ?_⟩
  · intro hbu; exact hb (by simp [hbu])
  · intro hba; exact hb (by simp [hba])

/-! ### The refutation -/

set_option maxHeartbeats 1000000 in
/-- **The repaired reservoir clause fails at a singleton protected level.**  For every
perturbation scale `η > 0` there are configurations satisfying every hypothesis of
`BKLO.ReservoirClauseR`, with `|W''| = 1`, in which no reservoir has its link-covering clause. -/
theorem not_reservoirClauseR_of_singleton_inner {ε η : ℝ} {f : ℕ → ℝ} {n₂ K : ℕ}
    (hε : 0 < ε) (hε' : ε < 1 / 10) (hK : 2 ≤ K) (hη : 0 < η)
    (hf : ∀ s : ℕ, n₂ ≤ s → f s ≤ 9 / 10 + ε) :
    ¬ ReservoirClauseR ε η f n₂ K := by
  classical
  intro hcl
  -- a configuration large enough that the perturbation budget `2η|W|` exceeds `1`
  obtain ⟨N, W, W', W''₀, F, hn₀, hn₂, hW'W, hW''W', hKW', hW'K, hKW''₀, hFW, hdiv, hdegW,
      hdegW', hres, hDne, hW''ne, -⟩ :=
    reservoirClauseR_hypotheses_realizable hε hε' hK hf (⌈1 / η⌉₊ + 1)
  -- the perturbation budget is at least one
  have hWcard : (1 : ℝ) ≤ η * (W.card : ℝ) := by
    have h1 : (1 : ℝ) / η ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / η⌉₊ : ℕ) : ℝ) ≤ (W.card : ℝ) := by
      have : (⌈1 / η⌉₊ : ℕ) ≤ W.card := le_trans (Nat.le_succ _) hn₀
      exact_mod_cast this
    have h3 : (1 : ℝ) / η ≤ (W.card : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hη] at h3
    linarith
  -- `W'` is nonempty
  have hW'pos : 0 < W'.card := by
    have h1 : 0 < W''₀.card := Finset.card_pos.2 hW''ne
    have : K * 1 ≤ K * W''₀.card := Nat.mul_le_mul_left _ h1
    omega
  -- an outer vertex and one of its `F`-neighbours inside `W'`
  obtain ⟨u₀, hu₀⟩ := hDne
  have hu₀W : u₀ ∈ W := (Finset.mem_sdiff.1 hu₀).1
  have hu₀W' : u₀ ∉ W' := (Finset.mem_sdiff.1 hu₀).2
  have hlinkne : (resLink F W' u₀).Nonempty := by
    rw [← Finset.card_pos]
    have h := hres u₀ hu₀W
    have hW'r : (0 : ℝ) < (W'.card : ℝ) := by exact_mod_cast hW'pos
    have : (0 : ℝ) < ((resLink F W' u₀).card : ℝ) := by nlinarith
    exact_mod_cast this
  obtain ⟨a, ha⟩ := hlinkne
  obtain ⟨haW', haF⟩ := mem_resLink.1 ha
  -- run the clause at the singleton protected level `{a}`
  have hKsingle : K * ({a} : Finset (Fin N)).card ≤ W'.card := by
    rw [Finset.card_singleton, mul_one]
    have h1 : 0 < W''₀.card := Finset.card_pos.2 hW''ne
    have h2 : K * 1 ≤ K * W''₀.card := Nat.mul_le_mul_left _ h1
    omega
  obtain ⟨R, hRF, hRcross, -, hapex, hlink⟩ :=
    hcl W W' {a} F hn₂ hW'W (by simpa using haW') hKW' hW'K hKsingle
      hFW hdiv hdegW hdegW' hres
  -- the reserved link of `u₀` has at least two vertices
  have hbase2 : 2 ≤ (resLink R W' u₀).card := by
    have hsub : apexes R W' u₀ u₀ ⊆ resLink R W' u₀ := by
      intro w hw
      obtain ⟨hwW', hw1, -⟩ := mem_apexes.1 hw
      exact mem_resLink.2 ⟨hwW', hw1⟩
    have h1 := hapex u₀ hu₀ u₀ hu₀
    have h2 : ((apexes R W' u₀ u₀).card : ℝ) ≤ ((resLink R W' u₀).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have : (2 : ℝ) ≤ ((resLink R W' u₀).card : ℝ) := by linarith
    exact_mod_cast this
  -- the adversarial link system: the reserved links, trimmed to even size, with `a` added at `u₀`
  have key : ∀ u : Fin N, ∃ T : Finset (Fin N), T ⊆ W' ∧ Even T.card ∧
      (∀ b ∈ T, s(u, b) ∈ F) ∧
      (resLink R W' u \ T).card ≤ 1 ∧ (T \ resLink R W' u).card ≤ 1 ∧
      (u ≠ u₀ → T ⊆ resLink R W' u) ∧ (u = u₀ → a ∈ T) := by
    intro u
    by_cases hu : u = u₀
    · subst hu
      set S : Finset (Fin N) := insert a (resLink R W' u) with hSdef
      have hbaseS : resLink R W' u ⊆ S := Finset.subset_insert _ _
      have haS : a ∈ S := Finset.mem_insert_self _ _
      have hS2 : 2 ≤ S.card := le_trans hbase2 (Finset.card_le_card hbaseS)
      obtain ⟨T, hTS, haT, hTev, hST⟩ := exists_even_subset_of_two_le haS hS2
      refine ⟨T, ?_, hTev, ?_, ?_, ?_, fun h => absurd rfl h, fun _ => haT⟩
      · intro z hz
        rcases Finset.mem_insert.1 (hTS hz) with rfl | hz'
        · exact haW'
        · exact (mem_resLink.1 hz').1
      · intro b hb
        rcases Finset.mem_insert.1 (hTS hb) with rfl | hb'
        · exact haF
        · exact hRF (mem_resLink.1 hb').2
      · refine le_trans (Finset.card_le_card ?_) hST
        exact Finset.sdiff_subset_sdiff hbaseS (Finset.Subset.refl _)
      · have hsub : T \ resLink R W' u ⊆ {a} := by
          intro z hz
          obtain ⟨hzT, hz'⟩ := Finset.mem_sdiff.1 hz
          rcases Finset.mem_insert.1 (hTS hzT) with rfl | hz''
          · simp
          · exact absurd hz'' hz'
        exact le_trans (Finset.card_le_card hsub) (by simp)
    · obtain ⟨T, hTS, hTev, hST⟩ := exists_even_subset (resLink R W' u)
      refine ⟨T, fun z hz => (mem_resLink.1 (hTS hz)).1, hTev,
        fun b hb => hRF (mem_resLink.1 (hTS hb)).2, hST, ?_, fun _ => hTS, fun h => absurd h hu⟩
      · have : T \ resLink R W' u = ∅ := Finset.sdiff_eq_empty_iff_subset.2 hTS
        simp [this]
  choose X hXW' hXeven hXF hXdel hXadd hXbase hXa using key
  -- the six hypotheses of the link-covering clause
  have hbudget : ∀ c : ℕ, c ≤ 1 → (c : ℝ) ≤ 2 * η * (W.card : ℝ) := by
    intro c hc
    have : (c : ℝ) ≤ 1 := by exact_mod_cast hc
    linarith
  obtain ⟨Q, hQ, hQinner⟩ := hlink X (fun u _ => hXW' u) (fun u _ b hb => hXF u b hb)
    (fun u _ => hXeven u)
    (fun u _ => hbudget _ (hXadd u))
    (fun u _ => hbudget _ (hXdel u))
    (fun c _ => by
      refine hbudget _ ?_
      have hsub : (W \ W').filter (fun u => c ∈ X u \ resLink R W' u) ⊆ {u₀} := by
        intro u hu
        obtain ⟨-, hcu⟩ := Finset.mem_filter.1 hu
        obtain ⟨hcX, hcR⟩ := Finset.mem_sdiff.1 hcu
        by_contra hne
        rw [Finset.mem_singleton] at hne
        exact hcR (hXbase u hne hcX)
      exact le_trans (Finset.card_le_card hsub) (by simp))
  obtain ⟨htri, hcov, huse, -, -⟩ := hQ
  -- the crossing edge `s(u₀, a)` is covered, and its triangle runs into `W''` at its third vertex
  have haX : a ∈ X u₀ := hXa u₀ rfl
  have hcross : s(u₀, a) ∈ famEdges Q := hcov (crossStars_mem hu₀ haX)
  obtain ⟨t, htQ, hte⟩ := exists_triangle_of_mem_famEdges hcross
  have ht3 : t.card = 3 := htri.1 t htQ
  have hmem := (mem_cliqueEdgesV.1 hte).1
  have hu₀t : u₀ ∈ t := hmem u₀ (by simp)
  have hat : a ∈ t := hmem a (by simp)
  have hua : u₀ ≠ a := fun h => hu₀W' (h ▸ haW')
  obtain ⟨b, hbt, hbu, hba⟩ := exists_third_vertex ht3 hu₀t hat hua
  have hedge : ∀ x y : Fin N, x ∈ t → y ∈ t → x ≠ y → s(x, y) ∈ famEdges Q := by
    intro x y hx hy hxy
    refine Finset.mem_biUnion.2 ⟨t, htQ, mem_cliqueEdgesV.2 ⟨?_, ?_⟩⟩
    · intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      exacts [hx, hy]
    · simpa [Sym2.isDiag_iff_proj_eq] using hxy
  have hub : s(u₀, b) ∈ famEdges Q := hedge u₀ b hu₀t hbt (Ne.symm hbu)
  have hab : s(a, b) ∈ famEdges Q := hedge a b hat hbt (Ne.symm hba)
  -- the third vertex lies in `W'`
  have hbW' : b ∈ W' := by
    rcases Finset.mem_union.1 (huse hub) with hc | hc
    · obtain ⟨w, hw, c, hc', heq⟩ := mem_crossStars.1 hc
      rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 ▸ hXW' w hc'
      · exact absurd (h1 ▸ hXW' w hc') hu₀W'
    · exact (mem_cliqueEdgesV.1 hc).1 b (by simp)
  -- but then the cover uses an edge into the singleton protected level at `b`
  have hone : (1 : ℝ) ≤ ((resLink (famEdges Q) {a} b).card : ℝ) := by
    have : a ∈ resLink (famEdges Q) {a} b :=
      mem_resLink.2 ⟨Finset.mem_singleton_self _, by rw [Sym2.eq_swap]; exact hab⟩
    have h1 : 1 ≤ (resLink (famEdges Q) {a} b).card := Finset.card_pos.2 ⟨a, this⟩
    exact_mod_cast h1
  have hbound := hQinner b hbW'
  rw [Finset.card_singleton] at hbound
  norm_num at hbound
  linarith

/-- **The residual reservoir clause of §10 is false.**  Its quantifier over the protected level
`W''` is unrestricted, and at a singleton `W''` the damage bound `γ|W''| = ε/8 < 1` forbids the
cover any edge into `W''`, while the perturbation budget `2η|W| ≥ 1` lets the link system demand
one. -/
theorem not_reservoirClauseResidual : ¬ ReservoirClauseResidual := by
  intro h
  obtain ⟨η, n₃, hη, hmain⟩ :=
    h (1 / 100) (by norm_num) (by norm_num) 800 (by norm_num) (by norm_num)
  refine not_reservoirClauseR_of_singleton_inner (ε := 1 / 100) (η := η)
    (f := fun _ => 9 / 10 + 1 / 200) (n₂ := n₃) (K := 800)
    (by norm_num) (by norm_num) (by norm_num) hη (fun s _ => by norm_num) ?_
  exact hmain (fun _ => 9 / 10 + 1 / 200) n₃ le_rfl (fun s _ => ⟨by norm_num, by norm_num⟩)

/-- **The pairing form of the residual is false as well.**  Contraposition of
`BKLO.reservoirClauseResidual_of_pairingResidual`: the `loadInner` field of
`BKLO.IsPairedLinkSystem` cannot be met at a singleton protected level. -/
theorem not_reservoirPairingResidual : ¬ ReservoirPairingResidual := fun h =>
  not_reservoirClauseResidual (reservoirClauseResidual_of_pairingResidual h)

end BKLO
