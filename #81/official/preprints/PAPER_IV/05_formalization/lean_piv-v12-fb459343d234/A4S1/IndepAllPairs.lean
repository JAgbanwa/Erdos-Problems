import A4S1.IndepAllTools

/-!
# E14 (copied from E10 `A4S1.OwnAllPairs`, no forbidden import)
# E10, own terminal for every rooted defect `s`: disjoint non-adjacent pairs

Generic tools, all for a fixed rooted defect `s`:

* `IsPairFam P`: `P` is a family of vertex-disjoint pairs of distinct vertices; `pends P` are
  its endpoints.
* `card_le_sdiff_of_pairs`: if a vertex set `N` contains the endpoints of a family of
  non-adjacent pairs, every clique misses at least one endpoint of each pair, so
  `|P| ≤ |N ∖ C|`. This is the per-vertex form of the obstruction `(O_s)`: a vertex whose
  neighbourhood contains `s + 1` disjoint non-adjacent pairs has defect `≥ s + 1`.
* `not_rootedDefect_of_rich`: a non-empty vertex set in which every vertex has defect `≥ s + 1`
  contradicts `RootedDefectAt G s` (root `R = ∅`).
* `HasMissPairs G S m`: `S` contains `m` disjoint non-adjacent pairs.
* `erdos_gallai`: **Erdős–Gallai** (in the form needed): if `S` does not contain `m + 1`
  disjoint non-adjacent pairs and `|S| ≥ 5m + 1`, then the number of missing pairs of `S` is at
  most `m |S| − C(m+1, 2)`.
* `exists_sdr`: a greedy system of distinct representatives.
* `joint_peel`: **joint incidence by peeling** (the rooted-defect condition is applied to
  successively smaller vertex sets).
-/

namespace A4S1.IndepAll

open Finset PaperIV.RootedSimplicialDefect A4S1.TerminalPacking

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Families of disjoint pairs -/

/-- A family of pairwise vertex-disjoint pairs of distinct vertices. -/
def IsPairFam (P : Finset (V × V)) : Prop :=
  (∀ p ∈ P, p.1 ≠ p.2) ∧
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

/-- The endpoints of a family of pairs. -/
def pends (P : Finset (V × V)) : Finset V := P.image Prod.fst ∪ P.image Prod.snd

omit [Fintype V] in
theorem mem_pends {P : Finset (V × V)} {v : V} : v ∈ pends P ↔ ∃ p ∈ P, p.1 = v ∨ p.2 = v := by
  simp only [pends, mem_union, mem_image]
  constructor
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, hp, Or.inl h⟩
    · exact ⟨p, hp, Or.inr h⟩
  · rintro ⟨p, hp, h | h⟩
    · exact Or.inl ⟨p, hp, h⟩
    · exact Or.inr ⟨p, hp, h⟩

omit [Fintype V] in
theorem fst_mem_pends {P : Finset (V × V)} {p : V × V} (hp : p ∈ P) : p.1 ∈ pends P :=
  mem_pends.2 ⟨p, hp, Or.inl rfl⟩

omit [Fintype V] in
theorem snd_mem_pends {P : Finset (V × V)} {p : V × V} (hp : p ∈ P) : p.2 ∈ pends P :=
  mem_pends.2 ⟨p, hp, Or.inr rfl⟩

omit [Fintype V] in
theorem card_pends_le (P : Finset (V × V)) : (pends P).card ≤ 2 * P.card := by
  unfold pends
  have h1 := card_union_le (P.image Prod.fst) (P.image Prod.snd)
  have h2 := card_image_le (s := P) (f := Prod.fst)
  have h3 := card_image_le (s := P) (f := Prod.snd)
  omega

omit [Fintype V] in
theorem IsPairFam.insert {P : Finset (V × V)} (hP : IsPairFam P) {a b : V} (hab : a ≠ b)
    (ha : a ∉ pends P) (hb : b ∉ pends P) : IsPairFam (insert (a, b) P) ∧ (a, b) ∉ P := by
  have hnot : (a, b) ∉ P := fun h => ha (fst_mem_pends h)
  refine ⟨⟨?_, ?_⟩, hnot⟩
  · intro p hp
    rcases mem_insert.1 hp with rfl | hp
    · exact hab
    · exact hP.1 p hp
  · intro p hp q hq hpq
    rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
    · exact absurd rfl hpq
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only at h
      · exact ha (h ▸ fst_mem_pends hq)
      · exact ha (h ▸ snd_mem_pends hq)
      · exact hb (h ▸ fst_mem_pends hq)
      · exact hb (h ▸ snd_mem_pends hq)
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only at h
      · exact ha (h ▸ fst_mem_pends hp)
      · exact hb (h ▸ fst_mem_pends hp)
      · exact ha (h ▸ snd_mem_pends hp)
      · exact hb (h ▸ snd_mem_pends hp)
    · exact hP.2 p hp q hq hpq

omit [Fintype V] in
/-- Union of two families with disjoint endpoint sets. -/
theorem IsPairFam.union {P P' : Finset (V × V)} (hP : IsPairFam P) (hP' : IsPairFam P')
    (hd : Disjoint (pends P) (pends P')) : IsPairFam (P ∪ P') ∧ Disjoint P P' := by
  have hx : ∀ p ∈ P, ∀ q ∈ P', p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
    intro p hp q hq
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
    · exact disjoint_left.1 hd (fst_mem_pends hp) (h ▸ fst_mem_pends hq)
    · exact disjoint_left.1 hd (fst_mem_pends hp) (h ▸ snd_mem_pends hq)
    · exact disjoint_left.1 hd (snd_mem_pends hp) (h ▸ fst_mem_pends hq)
    · exact disjoint_left.1 hd (snd_mem_pends hp) (h ▸ snd_mem_pends hq)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    rcases mem_union.1 hp with h | h
    · exact hP.1 p h
    · exact hP'.1 p h
  · intro p hp q hq hpq
    rcases mem_union.1 hp with h | h <;> rcases mem_union.1 hq with h' | h'
    · exact hP.2 p h q h' hpq
    · exact hx p h q h'
    · obtain ⟨a1, a2, a3, a4⟩ := hx q h' p h
      exact ⟨Ne.symm a1, Ne.symm a3, Ne.symm a2, Ne.symm a4⟩
    · exact hP'.2 p h q h' hpq
  · rw [disjoint_left]
    intro p hp hp'
    exact (hx p hp p hp').1 rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Per-vertex obstruction.** A clique inside `N` misses one endpoint of each non-adjacent
pair of a family inside `N`. -/
theorem card_le_sdiff_of_pairs {P : Finset (V × V)} (hP : IsPairFam P)
    (hn : ∀ p ∈ P, ¬ G.Adj p.1 p.2) {N C : Finset V} (hPN : ∀ p ∈ P, p.1 ∈ N ∧ p.2 ∈ N)
    (hC : G.IsClique (C : Set V)) : P.card ≤ (N \ C).card := by
  let f : V × V → V := fun p => if p.1 ∈ C then p.2 else p.1
  apply card_le_card_of_injOn f
  · intro p hp
    simp only [f]
    split_ifs with h1
    · refine mem_sdiff.2 ⟨(hPN p hp).2, fun h2 => hn p hp (hC h1 h2 (hP.1 p hp))⟩
    · exact mem_sdiff.2 ⟨(hPN p hp).1, h1⟩
  · intro p hp q hq hpq
    by_contra hne
    obtain ⟨a1, a2, a3, a4⟩ := hP.2 p hp q hq hne
    simp only [f] at hpq
    split_ifs at hpq
    · exact a4 hpq
    · exact a3 hpq
    · exact a2 hpq
    · exact a1 hpq

/-! ## Rooted defect -/

omit [Fintype V] in
/-- One step of the rooted-defect condition with empty root. -/
theorem defect_step {s : ℕ} (hG : RootedDefectAt G s) {U : Finset V} (hU : U.Nonempty) :
    ∃ v ∈ U, ∃ C ⊆ neighborsIn G U v, G.IsClique (C : Set V) ∧
      (neighborsIn G U v \ C).card ≤ s := by
  obtain ⟨v, hv, C, hCsub, hC, hcard⟩ := hG U ∅ (empty_subset _) (by simp) (by simpa using hU)
  refine ⟨v, by simpa using hv, C, hCsub, hC, ?_⟩
  rw [card_sdiff_of_subset hCsub]
  omega

omit [Fintype V] in
/-- A non-empty vertex set in which every vertex has defect at least `s + 1`. -/
theorem not_rootedDefect_of_rich {s : ℕ} (hG : RootedDefectAt G s) (U : Finset V)
    (hU : U.Nonempty)
    (hrich : ∀ v ∈ U, ∀ C ⊆ neighborsIn G U v, G.IsClique (C : Set V) →
      s + 1 ≤ (neighborsIn G U v \ C).card) : False := by
  obtain ⟨v, hv, C, hCsub, hC, hcard⟩ := defect_step hG hU
  have := hrich v hv C hCsub hC
  omega

omit [Fintype V] [DecidableEq V] in
theorem mem_neighborsIn {U : Finset V} {v w : V} : w ∈ neighborsIn G U v ↔ w ∈ U ∧ G.Adj v w :=
  mem_filter

/-! ## Erdős–Gallai -/

variable (G) in
/-- `S` contains `m` disjoint non-adjacent pairs. -/
def HasMissPairs (S : Finset V) (m : ℕ) : Prop :=
  ∃ P : Finset (V × V), IsPairFam P ∧ P.card = m ∧ ∀ p ∈ P, p.1 ∈ S ∧ p.2 ∈ S ∧ ¬ G.Adj p.1 p.2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem hasMissPairs_zero (S : Finset V) : HasMissPairs G S 0 :=
  ⟨∅, ⟨by simp, by simp⟩, by simp, by simp⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem hasMissPairs_mono {S T : Finset V} (h : S ⊆ T) {m : ℕ} (hS : HasMissPairs G S m) :
    HasMissPairs G T m := by
  obtain ⟨P, hP, hc, hm⟩ := hS
  exact ⟨P, hP, hc, fun p hp => ⟨h (hm p hp).1, h (hm p hp).2.1, (hm p hp).2.2⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem hasMissPairs_le {S : Finset V} {m m' : ℕ} (hmm : m' ≤ m) (hS : HasMissPairs G S m) :
    HasMissPairs G S m' := by
  obtain ⟨P, hP, hc, hm⟩ := hS
  obtain ⟨P', hP'P, hP'c⟩ := exists_subset_card_eq (show m' ≤ P.card by omega)
  refine ⟨P', ⟨fun p hp => hP.1 p (hP'P hp), fun p hp q hq => hP.2 p (hP'P hp) q (hP'P hq)⟩,
    hP'c, fun p hp => hm p (hP'P hp)⟩

omit [Fintype V] [DecidableEq V] in
theorem isClique_of_not_hasMissPairs_one {S : Finset V} (h : ¬ HasMissPairs G S 1) :
    G.IsClique (S : Set V) := by
  intro a ha b hb hab
  by_contra hn
  apply h
  refine ⟨{(a, b)}, ⟨by simpa using hab, by simp⟩, by simp, ?_⟩
  intro p hp
  rw [mem_singleton] at hp
  subst hp
  exact ⟨ha, hb, hn⟩

theorem card_inEdges_insert {T : Finset V} {x : V} (hx : x ∉ T) :
    (inEdges G (insert x T)).card = (inEdges G T).card + (T.filter (G.Adj x)).card := by
  rw [insert_eq, card_inEdges_union (disjoint_singleton_left.2 hx),
    A4S1.IndepAll.card_inEdges_singleton, A4S1.IndepAll.crossCount_singleton]
  ring

omit [Fintype V] [DecidableEq V] in
theorem card_filter_adj_ge (T : Finset V) (x : V) (d : ℕ)
    (hd : (T.filter fun y => ¬ G.Adj x y).card ≤ d) : T.card ≤ (T.filter (G.Adj x)).card + d := by
  have := card_filter_add_card_filter_not (s := T) (G.Adj x)
  omega

/-- The low-degree case of Erdős–Gallai. -/
theorem eg_low (d : ℕ) : ∀ (p : ℕ) (S : Finset V), ¬ HasMissPairs G S (p + 1) →
    (∀ x ∈ S, (S.filter fun y => y ≠ x ∧ ¬ G.Adj x y).card ≤ d) →
    S.card.choose 2 ≤ (inEdges G S).card + (2 * d + 1) * p := by
  intro p
  induction p with
  | zero =>
    intro S hS _
    rw [card_inEdges_of_isClique (isClique_of_not_hasMissPairs_one hS)]
    omega
  | succ p ih =>
    intro S hS hd
    by_cases hex : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ¬ G.Adj a b
    · obtain ⟨a, ha, b, hb, hab, hnab⟩ := hex
      set S' := (S.erase a).erase b with hS'
      have hbS' : b ∉ S' := by simp [hS']
      have haS' : a ∉ insert b S' := by
        simp only [hS', mem_insert, mem_erase]; push_neg; exact ⟨hab, fun _ h => absurd rfl h⟩
      have hSeq : S = insert a (insert b S') := by
        rw [hS', insert_erase (mem_erase.2 ⟨hab.symm, hb⟩), insert_erase ha]
      have hS'no : ¬ HasMissPairs G S' (p + 1) := by
        rintro ⟨P, hP, hc, hm⟩
        have ha' : a ∉ pends P := by
          intro h
          obtain ⟨q, hq, h1 | h1⟩ := mem_pends.1 h
          · have := (hm q hq).1; rw [h1] at this; simp [hS'] at this
          · have := (hm q hq).2.1; rw [h1] at this; simp [hS'] at this
        have hb' : b ∉ pends P := by
          intro h
          obtain ⟨q, hq, h1 | h1⟩ := mem_pends.1 h
          · have := (hm q hq).1; rw [h1] at this; exact hbS' this
          · have := (hm q hq).2.1; rw [h1] at this; exact hbS' this
        obtain ⟨hP2, hnot⟩ := hP.insert hab ha' hb'
        apply hS
        refine ⟨insert (a, b) P, hP2, by rw [card_insert_of_notMem hnot, hc], ?_⟩
        intro q hq
        rcases mem_insert.1 hq with rfl | hq
        · exact ⟨ha, hb, hnab⟩
        · have := hm q hq
          exact ⟨mem_of_mem_erase (mem_of_mem_erase this.1),
            mem_of_mem_erase (mem_of_mem_erase this.2.1), this.2.2⟩
      have hd' : ∀ x ∈ S', (S'.filter fun y => y ≠ x ∧ ¬ G.Adj x y).card ≤ d := by
        intro x hx
        have hxS : x ∈ S := mem_of_mem_erase (mem_of_mem_erase hx)
        exact (card_le_card (filter_subset_filter _
          ((erase_subset _ _).trans (erase_subset _ _)))).trans (hd x hxS)
      have hIH := ih S' hS'no hd'
      have hcS : S.card = S'.card + 2 := by
        rw [hSeq, card_insert_of_notMem haS', card_insert_of_notMem hbS']
      have he : (inEdges G S).card = (inEdges G S').card + (S'.filter (G.Adj b)).card +
          ((insert b S').filter (G.Adj a)).card := by
        rw [hSeq, card_inEdges_insert haS', card_inEdges_insert hbS']
      have hdb : (S'.filter fun y => ¬ G.Adj b y).card ≤ d := by
        refine (card_le_card ?_).trans (hd b hb)
        intro y hy
        obtain ⟨hy1, hy2⟩ := mem_filter.1 hy
        refine mem_filter.2 ⟨mem_of_mem_erase (mem_of_mem_erase hy1), ?_, hy2⟩
        rintro rfl; exact hbS' hy1
      have hda : (S'.filter fun y => ¬ G.Adj a y).card ≤ d := by
        refine (card_le_card ?_).trans (hd a ha)
        intro y hy
        obtain ⟨hy1, hy2⟩ := mem_filter.1 hy
        refine mem_filter.2 ⟨mem_of_mem_erase (mem_of_mem_erase hy1), ?_, hy2⟩
        rintro rfl; exact haS' (mem_insert_of_mem hy1)
      have e1 := card_filter_adj_ge (G := G) S' b d hdb
      have e2 := card_filter_adj_ge (G := G) S' a d hda
      have e3 : (S'.filter (G.Adj a)).card ≤ ((insert b S').filter (G.Adj a)).card :=
        card_le_card (filter_subset_filter _ (subset_insert _ _))
      have hch : (S'.card + 2).choose 2 = S'.card.choose 2 + 2 * S'.card + 1 := by
        rw [Nat.choose_succ_succ, Nat.choose_succ_succ, Nat.choose_one_right,
          Nat.choose_succ_succ, Nat.choose_zero_right, Nat.choose_one_right]
        ring
      rw [hcS, hch]
      nlinarith
    · push_neg at hex
      have hcl : G.IsClique (S : Set V) := fun a ha b hb hab => hex a ha b hb hab
      rw [card_inEdges_of_isClique hcl]
      omega

/-- **Erdős–Gallai (1959)**, in the form used: if `S` contains no `m + 1` disjoint
non-adjacent pairs and `|S| ≥ 5m + 1`, then `C(|S|,2) + C(m+1,2) ≤ e(G[S]) + m|S|`, i.e. at
most `m|S| − C(m+1,2)` pairs of `S` are missing. -/
theorem erdos_gallai : ∀ (m : ℕ) (S : Finset V), 5 * m + 1 ≤ S.card →
    ¬ HasMissPairs G S (m + 1) →
    S.card.choose 2 + (m + 1).choose 2 ≤ (inEdges G S).card + m * S.card := by
  intro m
  induction m with
  | zero =>
    intro S _ hS
    rw [card_inEdges_of_isClique (isClique_of_not_hasMissPairs_one hS)]
    simp
  | succ m ih =>
    intro S hc hS
    by_cases hx : ∃ x ∈ S, 2 * m + 3 ≤ (S.filter fun y => y ≠ x ∧ ¬ G.Adj x y).card
    · obtain ⟨x, hxS, hxd⟩ := hx
      have hno : ¬ HasMissPairs G (S.erase x) (m + 1) := by
        rintro ⟨P, hP, hPc, hm⟩
        have hpe := card_pends_le P
        obtain ⟨y, hy, hyP⟩ : ∃ y ∈ S.filter (fun y => y ≠ x ∧ ¬ G.Adj x y), y ∉ pends P := by
          by_contra hcon
          push_neg at hcon
          have := card_le_card (show S.filter (fun y => y ≠ x ∧ ¬ G.Adj x y) ⊆ pends P from
            fun y hy => hcon y hy)
          omega
        obtain ⟨hyS, hyx, hnxy⟩ := mem_filter.1 hy
        have hxP : x ∉ pends P := by
          intro h
          obtain ⟨q, hq, h1 | h1⟩ := mem_pends.1 h
          · have := (hm q hq).1; rw [h1] at this; simp at this
          · have := (hm q hq).2.1; rw [h1] at this; simp at this
        obtain ⟨hP2, hnot⟩ := hP.insert (Ne.symm hyx) hxP hyP
        apply hS
        refine ⟨insert (x, y) P, hP2, by rw [card_insert_of_notMem hnot, hPc], ?_⟩
        intro q hq
        rcases mem_insert.1 hq with rfl | hq
        · exact ⟨hxS, hyS, hnxy⟩
        · have := hm q hq
          exact ⟨mem_of_mem_erase this.1, mem_of_mem_erase this.2.1, this.2.2⟩
      have hce : (S.erase x).card + 1 = S.card := card_erase_add_one hxS
      have hIH := ih (S.erase x) (by omega) hno
      have hmono : (inEdges G (S.erase x)).card ≤ (inEdges G S).card :=
        card_le_card (A4S1.IndepAll.inEdges_mono (erase_subset x S))
      have h1 : S.card.choose 2 = (S.erase x).card.choose 2 + (S.erase x).card := by
        rw [← hce, Nat.choose_succ_succ, Nat.choose_one_right]; ring
      have h2 : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
      rw [h1, h2, ← hce]
      nlinarith
    · push_neg at hx
      have hlow := eg_low (G := G) (2 * m + 2) (m + 1) S hS (fun x hx' => by
        have := hx x hx'; omega)
      have h2 : 2 * (m + 1 + 1).choose 2 = (m + 2) * (m + 1) := by
        rw [Nat.choose_two_right]
        have := Nat.even_mul_pred_self (m + 2)
        rw [show m + 1 + 1 = m + 2 by ring, show m + 2 - 1 = m + 1 by omega] at *
        exact Nat.mul_div_cancel' this.two_dvd
      nlinarith

/-! ## A greedy system of distinct representatives -/

omit [Fintype V] in
theorem exists_sdr (B : Finset V) (F : V → Finset V) :
    ∀ X : Finset V, (∀ t ∈ X, B.card + X.card < (F t).card) →
      ∃ c : V → V, (∀ t ∈ X, c t ∈ F t ∧ c t ∉ B) ∧ Set.InjOn c X := by
  intro X
  induction X using Finset.induction_on with
  | empty => exact fun _ => ⟨id, by simp, by simp⟩
  | insert t X ht ih =>
    intro hF
    rw [card_insert_of_notMem ht] at hF
    obtain ⟨c, hc, hinj⟩ := ih (fun u hu => by have := hF u (mem_insert_of_mem hu); omega)
    obtain ⟨y, hy, hyn⟩ : ∃ y ∈ F t, y ∉ B ∪ X.image c := by
      by_contra hcon
      push_neg at hcon
      have h1 := card_le_card (show F t ⊆ B ∪ X.image c from fun y hy => hcon y hy)
      have h2 := card_union_le B (X.image c)
      have h3 := card_image_le (s := X) (f := c)
      have := hF t (mem_insert_self t X)
      omega
    have hyB : y ∉ B := fun h => hyn (mem_union_left _ h)
    have hyX : ∀ u ∈ X, c u ≠ y := fun u hu h => hyn (mem_union_right _ (mem_image.2 ⟨u, hu, h⟩))
    refine ⟨Function.update c t y, ?_, ?_⟩
    · intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · simp only [Function.update_self]; exact ⟨hy, hyB⟩
      · have hut : u ≠ t := fun h => ht (h ▸ hu)
        simp only [Function.update_of_ne hut]; exact hc u hu
    · intro u hu u' hu' huu
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hu hu'
      rcases hu with rfl | hu <;> rcases hu' with rfl | hu'
      · rfl
      · have hut : u' ≠ u := fun h => ht (h ▸ hu')
        simp only [Function.update_self, Function.update_of_ne hut] at huu
        exact absurd huu.symm (hyX u' hu')
      · have hut : u ≠ u' := fun h => ht (h ▸ hu)
        simp only [Function.update_self, Function.update_of_ne hut] at huu
        exact absurd huu (hyX u hu)
      · have hut : u ≠ t := fun h => ht (h ▸ hu)
        have hut' : u' ≠ t := fun h => ht (h ▸ hu')
        simp only [Function.update_of_ne hut, Function.update_of_ne hut'] at huu
        exact hinj hu hu' huu

end A4S1.IndepAll
