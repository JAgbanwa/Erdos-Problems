/-
# The three-class cycle block, at the threshold of an ordinary two-class block

`BKLO/AX2CornerSplit.lean` shows what a cross-side leftover discipline forces the pairing of a link
to look like: the corner class of the link splits into **two halves**, one taken by a column class
`A` and one by a row class `B`, and the remaining halves of `A` and of `B` pair with each other.
That is the three-class cycle whose ledger `BKLO.excLedgerSpread_of_cycleRouted` shows to be almost
free.

The obstacle was thought to be that the cycle asks for *half* bundles: a matching of `c / 2` places
of the corner into `A`, and the half-degree tool `BKLO.exists_matching_of_half_degree` produces a
bundle of size `s` only when `q + 4 m + 4 < 2 s`, which a bundle of size `c / 2 ≤ q / 2` never
satisfies.  That is an artefact of building the three bundles one after another.  Building them
**together** costs nothing beyond an ordinary two-class block:

* take a full matching `f : Kc → A` and a full matching `g : Kc → B` — each is an ordinary
  two-class block, and needs only `q + 4 m + 4 < 2 c`;
* pair the places of the corner with **each other** by Dirac's threshold
  (`BKLO.exists_involution_of_half_degree`) for the relation
  `k ~ k'  ↔  r (f k) (g k') ∨ r (f k') (g k)`; a place `k` fails to be related to `k'` only if
  `f k` is a bad partner of `g k'`, so the degree of `~` is at least `c - 1 - (bad in a class)`,
  and Dirac asks only for `c / 2`;
* for a pair `{k, k'}` of that involution — say with `r (f k') (g k)` — output the three pairs
  `(k, f k)`, `(k', g k')`, `(f k', g k)`.

Every place of the corner goes across, half of them into `A` and half into `B`; the `c / 2`
remaining places `f k'` of `A` and the `c / 2` remaining places `g k` of `B` are paired with each
other.  So the cycle is produced under exactly the hypothesis of an ordinary two-class block —
`2 · (bad partners in a class) + 2 ≤ c` — and **not** under the `c > q + 4 m + 4` that the
one-bundle-at-a-time route seemed to need.

* `BKLO.exists_three_class_cycle_involution` — the abstract form.
* `BKLO.three_class_cycle_threshold` — the arithmetic: the design's own bound on bad partners
  (`BKLO.card_bad_partners_in_class_le`, `4 · bad ≤ q + 4 m + 4`) meets the hypothesis as soon as
  `q + 4 m + 8 ≤ 2 c`, which `3 q ≤ 4 c` gives whenever `8 m + 16 ≤ q`.

Everything here is `sorry`-free.
-/
import BKLO.ClassPairing
import BKLO.ClassPairingPerturbed

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- **The three-class cycle block.**  Three pairwise disjoint sets of the same even size, a
symmetric relation `r` under which every place of one of them is related to more than half of each
of the others, and under which a place of `A` has at most `(|Kc| - 2) / 2` unrelated places in `B`.

Then `Kc ∪ A ∪ B` carries a fixed-point-free `r`-involution in which

* every place of `Kc` is paired across, into `A` or into `B`;
* exactly half of `A` — the set `LA` — and exactly half of `B` — the set `LB` — are paired with
  each other, and the other halves are paired with `Kc`.

This is the pairing a three-class cycle of a link needs, and its hypotheses are those of an
ordinary two-class block. -/
theorem exists_three_class_cycle_involution {Kc A B : Finset V}
    (hKA : Disjoint Kc A) (hKB : Disjoint Kc B) (hAB : Disjoint A B)
    (r : V → V → Prop) [DecidableRel r] (hsymm : ∀ a b, r a b → r b a)
    (hcardA : A.card = Kc.card) (hcardB : B.card = Kc.card)
    (heven : Even Kc.card)
    (hKAdeg : ∀ z ∈ Kc, A.card < 2 * (A.filter (fun b => r z b)).card)
    (hAKdeg : ∀ b ∈ A, Kc.card < 2 * (Kc.filter (fun z => r z b)).card)
    (hKBdeg : ∀ z ∈ Kc, B.card < 2 * (B.filter (fun b => r z b)).card)
    (hBKdeg : ∀ b ∈ B, Kc.card < 2 * (Kc.filter (fun z => r z b)).card)
    (hABbad : ∀ a ∈ A, 2 * (B.filter (fun b => ¬ r a b)).card + 2 ≤ Kc.card) :
    ∃ (p : V → V) (LA LB : Finset V),
      LA ⊆ A ∧ LB ⊆ B ∧ 2 * LA.card = Kc.card ∧ 2 * LB.card = Kc.card ∧
      (∀ z ∈ Kc ∪ A ∪ B, p z ∈ Kc ∪ A ∪ B) ∧ (∀ z ∈ Kc ∪ A ∪ B, p (p z) = z) ∧
      (∀ z ∈ Kc ∪ A ∪ B, p z ≠ z) ∧ (∀ z ∈ Kc ∪ A ∪ B, r z (p z)) ∧
      (∀ z ∈ Kc, p z ∈ A ∪ B) ∧
      (∀ z ∈ A, z ∉ LA → p z ∈ Kc) ∧ (∀ z ∈ B, z ∉ LB → p z ∈ Kc) ∧
      (∀ z ∈ LA, p z ∈ LB) ∧ (∀ z ∈ LB, p z ∈ LA) := by
  classical
  -- the two full class matchings out of the corner
  obtain ⟨f, hfmem, hfr, hfinj⟩ :=
    exists_matching_of_half_degree (A := Kc) (B := A) (r := r) hcardA.symm hKAdeg hAKdeg
  obtain ⟨g, hgmem, hgr, hginj⟩ :=
    exists_matching_of_half_degree (A := Kc) (B := B) (r := r) hcardB.symm hKBdeg hBKdeg
  have hfinj' : ∀ k ∈ Kc, ∀ k' ∈ Kc, f k = f k' → k = k' := by
    intro k hk k' hk' hkk
    exact hfinj (by exact_mod_cast hk) (by exact_mod_cast hk') hkk
  have hginj' : ∀ k ∈ Kc, ∀ k' ∈ Kc, g k = g k' → k = k' := by
    intro k hk k' hk' hkk
    exact hginj (by exact_mod_cast hk) (by exact_mod_cast hk') hkk
  have hfimg : Kc.image f = A := by
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
      exact hfmem k hk
    · rw [Finset.card_image_of_injOn hfinj]
      omega
  have hgimg : Kc.image g = B := by
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
      exact hgmem k hk
    · rw [Finset.card_image_of_injOn hginj]
      omega
  -- the inverse of `g`
  set ginv : V → V := fun w => if h : ∃ k ∈ Kc, g k = w then h.choose else w with hginvdef
  have hginveq : ∀ k ∈ Kc, ginv (g k) = k := by
    intro k hk
    have hex : ∃ k' ∈ Kc, g k' = g k := ⟨k, hk, rfl⟩
    have h1 : ginv (g k) = hex.choose := by
      rw [hginvdef]
      simp only [dif_pos hex]
    rw [h1]
    exact hginj' _ hex.choose_spec.1 k hk hex.choose_spec.2
  -- Dirac inside the corner, for the relation that lets a pair of the corner close a cycle
  have hssymm : ∀ a b, (r (f a) (g b) ∨ r (f b) (g a)) → (r (f b) (g a) ∨ r (f a) (g b)) := by
    intro a b h
    exact h.symm
  have hdeg : ∀ k ∈ Kc, Kc.card ≤ 2 * (Kc.filter (fun k' => k' ≠ k ∧
      (r (f k) (g k') ∨ r (f k') (g k)))).card := by
    intro k hk
    set Bad : Finset V := Kc.filter (fun k' => ¬ r (f k) (g k')) with hBaddef
    have hBadcard : Bad.card = (B.filter (fun b => ¬ r (f k) b)).card := by
      refine Finset.card_bij (fun k' _ => g k') ?_ ?_ ?_
      · intro k' hk'
        obtain ⟨hk'K, hk'r⟩ := Finset.mem_filter.1 hk'
        exact Finset.mem_filter.2 ⟨hgmem k' hk'K, hk'r⟩
      · intro k₁ h₁ k₂ h₂ heq
        exact hginj' _ (Finset.mem_filter.1 h₁).1 _ (Finset.mem_filter.1 h₂).1 heq
      · intro b hb
        obtain ⟨hbB, hbr⟩ := Finset.mem_filter.1 hb
        rw [← hgimg] at hbB
        obtain ⟨k', hk'K, rfl⟩ := Finset.mem_image.1 hbB
        exact ⟨k', Finset.mem_filter.2 ⟨hk'K, hbr⟩, rfl⟩
    have hbad := hABbad (f k) (hfmem k hk)
    rw [← hBadcard] at hbad
    have hsub : Kc \ (insert k Bad) ⊆ Kc.filter (fun k' => k' ≠ k ∧
        (r (f k) (g k') ∨ r (f k') (g k))) := by
      intro k' hk'
      obtain ⟨hk'K, hk'n⟩ := Finset.mem_sdiff.1 hk'
      have hne : k' ≠ k := fun hcon => hk'n (by rw [hcon]; exact Finset.mem_insert_self k Bad)
      have hgood : r (f k) (g k') := by
        by_contra hcon
        exact hk'n (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hk'K, hcon⟩))
      exact Finset.mem_filter.2 ⟨hk'K, hne, Or.inl hgood⟩
    have hcard1 : Kc.card ≤ (Kc \ (insert k Bad)).card + (insert k Bad).card := by
      have h1 : (Kc \ (insert k Bad)).card + (insert k Bad).card
          = (Kc ∪ insert k Bad).card := Finset.card_sdiff_add_card _ _
      have h2 : Kc.card ≤ (Kc ∪ insert k Bad).card :=
        Finset.card_le_card Finset.subset_union_left
      omega
    have hcard2 : (insert k Bad).card ≤ Bad.card + 1 := Finset.card_insert_le _ _
    have hcard3 := Finset.card_le_card hsub
    omega
  obtain ⟨pi, hpimem, hpiinv, hpine, hpir⟩ :=
    exists_involution_of_half_degree Kc (fun k k' => r (f k) (g k') ∨ r (f k') (g k))
      hssymm heven hdeg
  -- which place of a pair of the corner takes its partner in `A`
  set usesA : V → Prop := fun k =>
    if (r (f k) (g (pi k)) ∧ r (f (pi k)) (g k)) then WellOrderingRel k (pi k)
    else r (f (pi k)) (g k) with husesAdef
  have husesA_r : ∀ k, usesA k → r (f (pi k)) (g k) := by
    intro k hk
    by_cases hcase : r (f k) (g (pi k)) ∧ r (f (pi k)) (g k)
    · exact hcase.2
    · rw [husesAdef] at hk
      simpa only [if_neg hcase] using hk
  have husesA_pair : ∀ k ∈ Kc, (usesA k ↔ ¬ usesA (pi k)) := by
    intro k hk
    have hpp : pi (pi k) = k := hpiinv k hk
    have hne : pi k ≠ k := hpine k hk
    have hs := hpir k hk
    have hus : usesA k = if (r (f k) (g (pi k)) ∧ r (f (pi k)) (g k))
        then WellOrderingRel k (pi k) else r (f (pi k)) (g k) := by rw [husesAdef]
    have hus' : usesA (pi k) = if (r (f (pi k)) (g k) ∧ r (f k) (g (pi k)))
        then WellOrderingRel (pi k) k else r (f k) (g (pi k)) := by
      rw [husesAdef]
      simp only [hpp]
    by_cases hcase : r (f k) (g (pi k)) ∧ r (f (pi k)) (g k)
    · have hcase' : r (f (pi k)) (g k) ∧ r (f k) (g (pi k)) := ⟨hcase.2, hcase.1⟩
      rw [hus, hus', if_pos hcase, if_pos hcase']
      constructor
      · intro h1 h2
        exact asymm h1 h2
      · intro h1
        rcases trichotomous_of WellOrderingRel k (pi k) with h | h | h
        · exact h
        · exact absurd h.symm hne
        · exact absurd h h1
    · rw [hus, hus', if_neg hcase, if_neg (fun hcon => hcase ⟨hcon.2, hcon.1⟩)]
      tauto
  -- the two halves of the corner
  set KA : Finset V := Kc.filter (fun k => usesA k) with hKAdef
  set KB : Finset V := Kc.filter (fun k => ¬ usesA k) with hKBdef
  have hKAsub : KA ⊆ Kc := Finset.filter_subset _ _
  have hKBsub : KB ⊆ Kc := Finset.filter_subset _ _
  have hKAKBdisj : Disjoint KA KB := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact (Finset.mem_filter.1 hz').2 (Finset.mem_filter.1 hz).2
  have hKAKBunion : KA ∪ KB = Kc := by
    ext z
    simp only [hKAdef, hKBdef, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hu : usesA z
      · exact Or.inl ⟨h, hu⟩
      · exact Or.inr ⟨h, hu⟩
  have hpiKA : ∀ k ∈ KA, pi k ∈ KB := by
    intro k hk
    obtain ⟨hkK, hku⟩ := Finset.mem_filter.1 hk
    exact Finset.mem_filter.2 ⟨hpimem k hkK, (husesA_pair k hkK).1 hku⟩
  have hpiKB : ∀ k ∈ KB, pi k ∈ KA := by
    intro k hk
    obtain ⟨hkK, hku⟩ := Finset.mem_filter.1 hk
    refine Finset.mem_filter.2 ⟨hpimem k hkK, ?_⟩
    by_contra hcon
    exact hku ((husesA_pair k hkK).2 hcon)
  have hcardKAKB : KA.card = KB.card := by
    refine Finset.card_bij (fun k _ => pi k) (fun k hk => hpiKA k hk) ?_ ?_
    · intro k₁ h₁ k₂ h₂ heq
      have heq' : pi k₁ = pi k₂ := heq
      have e1 := hpiinv k₁ (hKAsub h₁)
      have e2 := hpiinv k₂ (hKAsub h₂)
      rw [← e1, ← e2, heq']
    · intro b hb
      exact ⟨pi b, hpiKB b hb, hpiinv b (hKBsub hb)⟩
  have hcardKA : 2 * KA.card = Kc.card := by
    have h1 : (KA ∪ KB).card = KA.card + KB.card := Finset.card_union_of_disjoint hKAKBdisj
    rw [hKAKBunion] at h1
    omega
  -- the three blocks of the cycle
  set FA : Finset V := KA.image f with hFAdef
  set FB : Finset V := KB.image f with hFBdef
  set GA : Finset V := KA.image g with hGAdef
  set GB : Finset V := KB.image g with hGBdef
  set hmap : V → V := fun w => f (pi (ginv w)) with hmapdef
  have hFAsub : FA ⊆ A := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    exact hfmem k (hKAsub hk)
  have hFBsub : FB ⊆ A := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    exact hfmem k (hKBsub hk)
  have hGAsub : GA ⊆ B := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    exact hgmem k (hKAsub hk)
  have hGBsub : GB ⊆ B := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    exact hgmem k (hKBsub hk)
  have hFAFB : Disjoint FA FB := by
    rw [Finset.disjoint_left]
    rintro z hz hz'
    obtain ⟨k₁, hk₁, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨k₂, hk₂, hk⟩ := Finset.mem_image.1 hz'
    have : k₂ = k₁ := hfinj' _ (hKBsub hk₂) _ (hKAsub hk₁) hk
    exact (Finset.disjoint_left.1 hKAKBdisj) hk₁ (this ▸ hk₂)
  have hGAGB : Disjoint GA GB := by
    rw [Finset.disjoint_left]
    rintro z hz hz'
    obtain ⟨k₁, hk₁, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨k₂, hk₂, hk⟩ := Finset.mem_image.1 hz'
    have : k₂ = k₁ := hginj' _ (hKBsub hk₂) _ (hKAsub hk₁) hk
    exact (Finset.disjoint_left.1 hKAKBdisj) hk₁ (this ▸ hk₂)
  have hFAFBunion : FA ∪ FB = A := by
    rw [hFAdef, hFBdef, ← Finset.image_union, hKAKBunion, hfimg]
  have hGAGBunion : GA ∪ GB = B := by
    rw [hGAdef, hGBdef, ← Finset.image_union, hKAKBunion, hgimg]
  -- block 0 : the half `KA` of the corner with its partners in `A`
  obtain ⟨p0, hp0eq, hp0mem, hp0inv, hp0ne, hp0r⟩ :=
    exists_swap_involution (A := KA) (B := FA)
      (Finset.disjoint_of_subset_left hKAsub (Finset.disjoint_of_subset_right hFAsub hKA))
      (f := f) (fun a ha => Finset.mem_image_of_mem f ha)
      (fun a ha b hb hab => hfinj' a (hKAsub (by exact_mod_cast ha)) b
        (hKAsub (by exact_mod_cast hb)) hab)
      (by rw [hFAdef, Finset.card_image_of_injOn
        (fun a ha b hb hab => hfinj' a (hKAsub (by exact_mod_cast ha)) b
          (hKAsub (by exact_mod_cast hb)) hab)])
      r hsymm (fun a ha => hfr a (hKAsub ha))
  -- block 1 : the half `KB` of the corner with its partners in `B`
  obtain ⟨p1, hp1eq, hp1mem, hp1inv, hp1ne, hp1r⟩ :=
    exists_swap_involution (A := KB) (B := GB)
      (Finset.disjoint_of_subset_left hKBsub (Finset.disjoint_of_subset_right hGBsub hKB))
      (f := g) (fun a ha => Finset.mem_image_of_mem g ha)
      (fun a ha b hb hab => hginj' a (hKBsub (by exact_mod_cast ha)) b
        (hKBsub (by exact_mod_cast hb)) hab)
      (by rw [hGBdef, Finset.card_image_of_injOn
        (fun a ha b hb hab => hginj' a (hKBsub (by exact_mod_cast ha)) b
          (hKBsub (by exact_mod_cast hb)) hab)])
      r hsymm (fun a ha => hgr a (hKBsub ha))
  -- block 2 : the leftovers, `GA` with `FB`
  have hmapmem : ∀ w ∈ GA, hmap w ∈ FB := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
    rw [hmapdef]
    simp only [hginveq k (hKAsub hk)]
    exact Finset.mem_image_of_mem f (hpiKA k hk)
  have hmapinj : Set.InjOn hmap ↑GA := by
    intro w hw w' hw' hww
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (by exact_mod_cast hw : w ∈ GA)
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 (by exact_mod_cast hw' : w' ∈ GA)
    rw [hmapdef] at hww
    simp only [hginveq k (hKAsub hk), hginveq k' (hKAsub hk')] at hww
    have h1 : pi k = pi k' :=
      hfinj' _ (hpimem k (hKAsub hk)) _ (hpimem k' (hKAsub hk')) hww
    have h2 := hpiinv k (hKAsub hk)
    have h3 := hpiinv k' (hKAsub hk')
    rw [← h2, ← h3, h1]
  have hmapcard : GA.card = FB.card := by
    rw [hGAdef, hFBdef, Finset.card_image_of_injOn
      (fun a ha b hb hab => hginj' a (hKAsub (by exact_mod_cast ha)) b
        (hKAsub (by exact_mod_cast hb)) hab),
      Finset.card_image_of_injOn
      (fun a ha b hb hab => hfinj' a (hKBsub (by exact_mod_cast ha)) b
        (hKBsub (by exact_mod_cast hb)) hab)]
    exact hcardKAKB
  have hmapr : ∀ w ∈ GA, r w (hmap w) := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
    rw [hmapdef]
    simp only [hginveq k (hKAsub hk)]
    exact hsymm _ _ (husesA_r k (Finset.mem_filter.1 hk).2)
  obtain ⟨p2, hp2eq, hp2mem, hp2inv, hp2ne, hp2r⟩ :=
    exists_swap_involution (A := GA) (B := FB)
      (Finset.disjoint_of_subset_left hGAsub (Finset.disjoint_of_subset_right hFBsub hAB.symm))
      (f := hmap) hmapmem hmapinj hmapcard r hsymm hmapr
  -- glue the three blocks
  set I : Finset ℕ := {0, 1, 2} with hIdef
  set T : ℕ → Finset V := fun i => if i = 0 then KA ∪ FA else if i = 1 then KB ∪ GB else GA ∪ FB
    with hTdef
  set pb : ℕ → V → V := fun i => if i = 0 then p0 else if i = 1 then p1 else p2 with hpbdef
  have hT0 : T 0 = KA ∪ FA := by rw [hTdef]; norm_num
  have hT1 : T 1 = KB ∪ GB := by rw [hTdef]; norm_num
  have hT2 : T 2 = GA ∪ FB := by rw [hTdef]; norm_num
  have hpb0 : pb 0 = p0 := by rw [hpbdef]; norm_num
  have hpb1 : pb 1 = p1 := by rw [hpbdef]; norm_num
  have hpb2 : pb 2 = p2 := by rw [hpbdef]; norm_num
  have hImem : ∀ i ∈ I, i = 0 ∨ i = 1 ∨ i = 2 := by
    intro i hi
    rw [hIdef] at hi
    simpa using hi
  have h0I : (0 : ℕ) ∈ I := by rw [hIdef]; simp
  have h1I : (1 : ℕ) ∈ I := by rw [hIdef]; simp
  have h2I : (2 : ℕ) ∈ I := by rw [hIdef]; simp
  -- the blocks are pairwise disjoint
  have hd01 : Disjoint (KA ∪ FA) (KB ∪ GB) := by
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨hKAKBdisj, ?_⟩,
      Finset.disjoint_union_right.2 ⟨?_, ?_⟩⟩
    · exact Finset.disjoint_of_subset_left hKAsub (Finset.disjoint_of_subset_right hGBsub hKB)
    · exact Finset.disjoint_of_subset_left hFAsub
        (Finset.disjoint_of_subset_right hKBsub hKA.symm)
    · exact Finset.disjoint_of_subset_left hFAsub (Finset.disjoint_of_subset_right hGBsub hAB)
  have hd02 : Disjoint (KA ∪ FA) (GA ∪ FB) := by
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩,
      Finset.disjoint_union_right.2 ⟨?_, hFAFB⟩⟩
    · exact Finset.disjoint_of_subset_left hKAsub (Finset.disjoint_of_subset_right hGAsub hKB)
    · exact Finset.disjoint_of_subset_left hKAsub (Finset.disjoint_of_subset_right hFBsub hKA)
    · exact Finset.disjoint_of_subset_left hFAsub (Finset.disjoint_of_subset_right hGAsub hAB)
  have hd12 : Disjoint (KB ∪ GB) (GA ∪ FB) := by
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩,
      Finset.disjoint_union_right.2 ⟨hGAGB.symm, ?_⟩⟩
    · exact Finset.disjoint_of_subset_left hKBsub (Finset.disjoint_of_subset_right hGAsub hKB)
    · exact Finset.disjoint_of_subset_left hKBsub (Finset.disjoint_of_subset_right hFBsub hKA)
    · exact Finset.disjoint_of_subset_left hGBsub (Finset.disjoint_of_subset_right hFBsub hAB.symm)
  have hdisjT : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (T i) (T j) := by
    intro i hi j hj hij
    rcases hImem i hi with rfl | rfl | rfl <;> rcases hImem j hj with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hij
        | (rw [hT0, hT1]; exact hd01)
        | (rw [hT1, hT0]; exact hd01.symm)
        | (rw [hT0, hT2]; exact hd02)
        | (rw [hT2, hT0]; exact hd02.symm)
        | (rw [hT1, hT2]; exact hd12)
        | (rw [hT2, hT1]; exact hd12.symm)
  have hmapsT : ∀ i ∈ I, ∀ z ∈ T i, pb i z ∈ T i := by
    intro i hi z hz
    rcases hImem i hi with rfl | rfl | rfl
    · rw [hpb0, hT0] at *; exact hp0mem z hz
    · rw [hpb1, hT1] at *; exact hp1mem z hz
    · rw [hpb2, hT2] at *; exact hp2mem z hz
  have hinvT : ∀ i ∈ I, ∀ z ∈ T i, pb i (pb i z) = z := by
    intro i hi z hz
    rcases hImem i hi with rfl | rfl | rfl
    · rw [hpb0, hT0] at *; exact hp0inv z hz
    · rw [hpb1, hT1] at *; exact hp1inv z hz
    · rw [hpb2, hT2] at *; exact hp2inv z hz
  have hneT : ∀ i ∈ I, ∀ z ∈ T i, pb i z ≠ z := by
    intro i hi z hz
    rcases hImem i hi with rfl | rfl | rfl
    · rw [hpb0, hT0] at *; exact hp0ne z hz
    · rw [hpb1, hT1] at *; exact hp1ne z hz
    · rw [hpb2, hT2] at *; exact hp2ne z hz
  have hrT : ∀ i ∈ I, ∀ z ∈ T i, r z (pb i z) := by
    intro i hi z hz
    rcases hImem i hi with rfl | rfl | rfl
    · rw [hpb0, hT0] at *; exact hp0r z hz
    · rw [hpb1, hT1] at *; exact hp1r z hz
    · rw [hpb2, hT2] at *; exact hp2r z hz
  obtain ⟨P, hPeq, hPmem, hPinv, hPne, hPr⟩ :=
    exists_involution_biUnion I T pb r hdisjT hmapsT hinvT hneT hrT
  -- the union of the three blocks is the whole triple
  have hbi : I.biUnion T = Kc ∪ A ∪ B := by
    have hstep : I.biUnion T = T 0 ∪ (T 1 ∪ T 2) := by
      rw [hIdef, Finset.biUnion_insert, Finset.biUnion_insert, Finset.singleton_biUnion]
    rw [hstep, hT0, hT1, hT2]
    ext z
    simp only [Finset.mem_union]
    constructor
    · rintro ((h | h) | ((h | h) | (h | h)))
      · exact Or.inl (Or.inl (hKAsub h))
      · exact Or.inl (Or.inr (hFAsub h))
      · exact Or.inl (Or.inl (hKBsub h))
      · exact Or.inr (hGBsub h)
      · exact Or.inr (hGAsub h)
      · exact Or.inl (Or.inr (hFBsub h))
    · rintro ((h | h) | h)
      · rw [← hKAKBunion] at h
        rcases Finset.mem_union.1 h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl (Or.inl h'))
      · rw [← hFAFBunion] at h
        rcases Finset.mem_union.1 h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr (Or.inr h'))
      · rw [← hGAGBunion] at h
        rcases Finset.mem_union.1 h with h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inl (Or.inr h'))
  rw [hbi] at hPmem hPinv hPne hPr
  -- the values of the involution on the six parts
  have hPKA : ∀ k ∈ KA, P k = f k := by
    intro k hk
    rw [hPeq 0 h0I k (by rw [hT0]; exact Finset.mem_union_left _ hk), hpb0]
    exact hp0eq k hk
  have hPKB : ∀ k ∈ KB, P k = g k := by
    intro k hk
    rw [hPeq 1 h1I k (by rw [hT1]; exact Finset.mem_union_left _ hk), hpb1]
    exact hp1eq k hk
  have hPGA : ∀ w ∈ GA, P w = hmap w := by
    intro w hw
    rw [hPeq 2 h2I w (by rw [hT2]; exact Finset.mem_union_left _ hw), hpb2]
    exact hp2eq w hw
  have hmemKc : ∀ k ∈ Kc, k ∈ Kc ∪ A ∪ B := fun k hk => Finset.mem_union_left _
    (Finset.mem_union_left _ hk)
  have hmemA : ∀ z ∈ A, z ∈ Kc ∪ A ∪ B := fun z hz => Finset.mem_union_left _
    (Finset.mem_union_right _ hz)
  have hmemB : ∀ z ∈ B, z ∈ Kc ∪ A ∪ B := fun z hz => Finset.mem_union_right _ hz
  refine ⟨P, FB, GA, hFBsub, hGAsub, ?_, ?_, hPmem, hPinv, hPne, hPr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFBdef, Finset.card_image_of_injOn
      (fun a ha b hb hab => hfinj' a (hKBsub (by exact_mod_cast ha)) b
        (hKBsub (by exact_mod_cast hb)) hab)]
    omega
  · rw [hGAdef, Finset.card_image_of_injOn
      (fun a ha b hb hab => hginj' a (hKAsub (by exact_mod_cast ha)) b
        (hKAsub (by exact_mod_cast hb)) hab)]
    omega
  · -- every place of the corner goes across
    intro z hz
    rw [← hKAKBunion] at hz
    rcases Finset.mem_union.1 hz with h | h
    · rw [hPKA z h]
      exact Finset.mem_union_left _ (hfmem z (hKAsub h))
    · rw [hPKB z h]
      exact Finset.mem_union_right _ (hgmem z (hKBsub h))
  · -- the non-leftover half of `A` is paired with the corner
    intro z hzA hzL
    rw [← hFAFBunion] at hzA
    rcases Finset.mem_union.1 hzA with h | h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
      have h1 : P k = f k := hPKA k hk
      have h2 : P (f k) = k := by
        have := hPinv k (hmemKc k (hKAsub hk))
        rw [h1] at this
        exact this
      rw [h2]
      exact hKAsub hk
    · exact absurd h hzL
  · -- the non-leftover half of `B` is paired with the corner
    intro z hzB hzL
    rw [← hGAGBunion] at hzB
    rcases Finset.mem_union.1 hzB with h | h
    · exact absurd h hzL
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
      have h1 : P k = g k := hPKB k hk
      have h2 : P (g k) = k := by
        have := hPinv k (hmemKc k (hKBsub hk))
        rw [h1] at this
        exact this
      rw [h2]
      exact hKBsub hk
  · -- the leftover half of `A` is paired with the leftover half of `B`
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    have hpik : pi k ∈ KA := hpiKB k hk
    have hw : g (pi k) ∈ GA := Finset.mem_image_of_mem g hpik
    have h1 : P (g (pi k)) = hmap (g (pi k)) := hPGA _ hw
    have h2 : hmap (g (pi k)) = f k := by
      rw [hmapdef]
      simp only [hginveq (pi k) (hKAsub hpik), hpiinv k (hKBsub hk)]
    have h3 : P (g (pi k)) = f k := by rw [h1, h2]
    have h4 : P (f k) = g (pi k) := by
      have := hPinv (g (pi k)) (hmemB _ (hGAsub hw))
      rw [h3] at this
      exact this
    rw [h4]
    exact hw
  · -- and conversely
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
    rw [hPGA _ (Finset.mem_image_of_mem g hk), hmapdef]
    simp only [hginveq k (hKAsub hk)]
    exact Finset.mem_image_of_mem f (hpiKA k hk)

/-! ### The three classes of a link -/

/-- **The threshold of the three-class cycle is the threshold of a two-class block.**  The design's
bound on the unusable partners inside a class (`BKLO.card_bad_partners_in_class_le`,
`4 · bad ≤ q + 4 m + 4`) gives what `BKLO.exists_three_class_cycle_involution` asks as soon as
`q + 4 m + 8 ≤ 2 c`, and the design's own `3 q ≤ 4 c` gives that whenever the class is large against
the used degree, `8 m + 16 ≤ q`. -/
theorem three_class_cycle_threshold {q c m : ℕ} (hqc : 3 * q ≤ 4 * c) (hm : 8 * m + 16 ≤ q) :
    q + 4 * m + 8 ≤ 2 * c := by omega

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **The three-class cycle of a link.**  Three distinct classes of the design whose traces on the
link `Xu` all have the same even size `c`, with `q + 4 m + 8 ≤ 2 c`: the union of the three traces
carries a fixed-point-free involution by edges of `F` outside `U` in which

* every place of the trace of `C i` — the **corner** class of the link — is paired into the trace
  of `C j` or of `C l`;
* exactly half of the trace of `C j`, the set `LA`, and exactly half of the trace of `C l`, the set
  `LB`, are paired with each other, and the other halves are paired with the corner.

With `i` the corner class of the link, `j` the column class `C (ρ (y u) h + y u)` and `l` the row
class `C (x u h + σ (x u))`, the pairs into the corner obey the cross-side rule of
`BKLO.IsClassMatchedSweep` on both sides, and `LA ∪ LB` are the leftovers of the cycle — the ones
`BKLO.excLoad_le_of_cycleRouted` charges at almost nothing. -/
theorem exists_three_class_cycle_block
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {i j l : ℕ} (hi : i < gridSize ε K * gridSize ε K) (hj : j < gridSize ε K * gridSize ε K)
    (hl : l < gridSize ε K * gridSize ε K) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {Xu : Finset V} (hXW' : Xu ⊆ W') {U : Finset (Sym2 V)} {m q c : ℕ}
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    (hU : ∀ a ∈ Xu, ∀ k < gridSize ε K * gridSize ε K,
      ((C k ∩ Xu).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (hci : (C i ∩ Xu).card = c) (hcj : (C j ∩ Xu).card = c) (hcl : (C l ∩ Xu).card = c)
    (heven : Even c) (hsize : q + 4 * m + 8 ≤ 2 * c) :
    ∃ (p : V → V) (LA LB : Finset V),
      LA ⊆ C j ∩ Xu ∧ LB ⊆ C l ∩ Xu ∧ 2 * LA.card = c ∧ 2 * LB.card = c ∧
      (∀ z ∈ (C i ∩ Xu) ∪ (C j ∩ Xu) ∪ (C l ∩ Xu), p z ∈ (C i ∩ Xu) ∪ (C j ∩ Xu) ∪ (C l ∩ Xu)) ∧
      (∀ z ∈ (C i ∩ Xu) ∪ (C j ∩ Xu) ∪ (C l ∩ Xu), p (p z) = z) ∧
      (∀ z ∈ (C i ∩ Xu) ∪ (C j ∩ Xu) ∪ (C l ∩ Xu), p z ≠ z) ∧
      (∀ z ∈ (C i ∩ Xu) ∪ (C j ∩ Xu) ∪ (C l ∩ Xu), s(z, p z) ∈ F ∧ s(z, p z) ∉ U) ∧
      (∀ z ∈ C i ∩ Xu, p z ∈ (C j ∩ Xu) ∪ (C l ∩ Xu)) ∧
      (∀ z ∈ C j ∩ Xu, z ∉ LA → p z ∈ C i ∩ Xu) ∧
      (∀ z ∈ C l ∩ Xu, z ∉ LB → p z ∈ C i ∩ Xu) ∧
      (∀ z ∈ LA, p z ∈ LB) ∧ (∀ z ∈ LB, p z ∈ LA) := by
  classical
  set Kc : Finset V := C i ∩ Xu with hKcdef
  set A : Finset V := C j ∩ Xu with hAdef
  set B : Finset V := C l ∩ Xu with hBdef
  have hsubC : ∀ k : ℕ, (C k ∩ Xu) ⊆ C k := fun k z hz => (Finset.mem_inter.1 hz).1
  have hsubW' : ∀ k : ℕ, (C k ∩ Xu) ⊆ W' := fun k z hz => hXW' (Finset.mem_inter.1 hz).2
  have hsubXu : ∀ k : ℕ, ∀ z ∈ (C k ∩ Xu), z ∈ Xu := fun k z hz => (Finset.mem_inter.1 hz).2
  have hdisj : ∀ k₁ k₂ : ℕ, k₁ < gridSize ε K * gridSize ε K →
      k₂ < gridSize ε K * gridSize ε K → k₁ ≠ k₂ → Disjoint (C k₁ ∩ Xu) (C k₂ ∩ Xu) := by
    intro k₁ k₂ h₁ h₂ hne
    exact Finset.disjoint_of_subset_left (hsubC k₁)
      (Finset.disjoint_of_subset_right (hsubC k₂) (hgrid.classDisjoint k₁ h₁ k₂ h₂ hne))
  set r : V → V → Prop := fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U with hrdef
  have hsymm : ∀ a b : V, r a b → r b a := by
    intro a b hab
    rw [hrdef]
    simp only []
    rw [Sym2.eq_swap]
    exact hab
  -- the design's bound on the unusable partners inside a class
  have hbad : ∀ k : ℕ, k < gridSize ε K * gridSize ε K → ∀ a ∈ Xu,
      4 * (((C k ∩ Xu).filter (fun b => ¬ (b ≠ a ∧ r a b))).card) ≤ q + 4 * m + 4 :=
    fun k hk a ha => card_bad_partners_in_class_le hgrid hW'W hk (hsubC k) (hsubW' k)
      (hXW' ha) hq (hU a ha k hk)
  -- a half-degree bound between two of the three traces
  have hhalf : ∀ k₁ k₂ : ℕ, k₁ < gridSize ε K * gridSize ε K →
      k₂ < gridSize ε K * gridSize ε K → (C k₂ ∩ Xu).card = c →
      ∀ z ∈ (C k₁ ∩ Xu), (C k₂ ∩ Xu).card < 2 * (((C k₂ ∩ Xu).filter (fun b => r z b)).card) := by
    intro k₁ k₂ h₁ h₂ hc₂ z hz
    have h1 := hbad k₂ h₂ z (hsubXu k₁ z hz)
    have h2 : ((C k₂ ∩ Xu).filter (fun b => b ≠ z ∧ r z b)).card
        + ((C k₂ ∩ Xu).filter (fun b => ¬ (b ≠ z ∧ r z b))).card = (C k₂ ∩ Xu).card :=
      Finset.card_filter_add_card_filter_not _
    have h3 : ((C k₂ ∩ Xu).filter (fun b => b ≠ z ∧ r z b)).card
        ≤ ((C k₂ ∩ Xu).filter (fun b => r z b)).card := by
      refine Finset.card_le_card fun w hw => ?_
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨hw1, hw2.2⟩
    omega
  -- the same, with the argument of the relation on the other side
  have hhalf' : ∀ k₁ k₂ : ℕ, k₁ < gridSize ε K * gridSize ε K →
      k₂ < gridSize ε K * gridSize ε K → (C k₂ ∩ Xu).card = c →
      ∀ b ∈ (C k₁ ∩ Xu), (C k₂ ∩ Xu).card < 2 * (((C k₂ ∩ Xu).filter (fun z => r z b)).card) := by
    intro k₁ k₂ h₁ h₂ hc₂ b hb
    have hset : (C k₂ ∩ Xu).filter (fun z => r b z) = (C k₂ ∩ Xu).filter (fun z => r z b) := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1, hsymm _ _ h.2⟩, fun h => ⟨h.1, hsymm _ _ h.2⟩⟩
    have h := hhalf k₁ k₂ h₁ h₂ hc₂ b hb
    rwa [hset] at h
  -- and the bound on the unusable partners of a place of `A` inside `B`
  have hKcc : Kc.card = c := hci
  have hABbad : ∀ a ∈ A, 2 * (B.filter (fun b => ¬ r a b)).card + 2 ≤ Kc.card := by
    intro a ha
    have h1 : 4 * ((B.filter (fun b => ¬ (b ≠ a ∧ r a b))).card) ≤ q + 4 * m + 4 :=
      hbad l hl a (hsubXu j a ha)
    have h2 : (B.filter (fun b => ¬ r a b)).card
        ≤ (B.filter (fun b => ¬ (b ≠ a ∧ r a b))).card := by
      refine Finset.card_le_card fun w hw => ?_
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨hw1, fun hcon => hw2 hcon.2⟩
    omega
  obtain ⟨p, LA, LB, hLA, hLB, hcardLA, hcardLB, hmem, hinv, hne, hr, hKcout, hAin, hBin,
      hLAB, hLBA⟩ :=
    exists_three_class_cycle_involution (Kc := Kc) (A := A) (B := B)
      (hdisj i j hi hj hij) (hdisj i l hi hl hil) (hdisj j l hj hl hjl) r hsymm
      (by rw [hAdef, hKcdef, hci, hcj]) (by rw [hBdef, hKcdef, hci, hcl])
      (by rw [hKcdef, hci]; exact heven)
      (fun z hz => hhalf i j hi hj hcj z hz) (fun b hb => hhalf' j i hj hi hci b hb)
      (fun z hz => hhalf i l hi hl hcl z hz) (fun b hb => hhalf' l i hl hi hci b hb)
      hABbad
  refine ⟨p, LA, LB, hLA, hLB, by rw [← hci]; exact hcardLA, by rw [← hci]; exact hcardLB,
    hmem, hinv, hne, hr, hKcout, hAin, hBin, hLAB, hLBA⟩

end BKLO
