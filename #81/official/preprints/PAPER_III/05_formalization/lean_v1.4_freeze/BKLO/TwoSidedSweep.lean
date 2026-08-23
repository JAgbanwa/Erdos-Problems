/-
# The sweep: from one link at a time to the whole paired system.

The pairing demand of AX2 §10 (`BKLO.IsPairedLinkCore`) is a *global* statement: the pairs of
different outer vertices must be different edges, and no vertex of `W'` may be paired into the
protected level too often.  This file reduces it to a **local** one — a single step of a sweep over
the outer vertices.

`BKLO.exists_pairedLinkCore_of_step` takes an oracle which, given the set `S` of outer vertices
already processed and the pairings `g₀` chosen for them, pairs up the link of one more outer vertex
`u` so that

* the pairs are edges of `F`, none of them inside the protected level, and
* none of them is an edge already used by `S` (`BKLO.usedPairs`), and
* the protected-level load of every vertex stays under the budget,

and returns the whole system.  The induction is over the processed set, and the three global fields
`distinct`, `avoid`, `loadInner` are exactly the three invariants it maintains.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirPairingStructured

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The edges already used by the pairings of a processed set of outer vertices. -/
def usedPairs (X : V → Finset V) (g : V → V → V) (S : Finset V) : Finset (Sym2 V) :=
  S.biUnion (fun v => (X v).image (fun b => s(b, g v b)))

theorem mem_usedPairs {X : V → Finset V} {g : V → V → V} {S : Finset V} {e : Sym2 V} :
    e ∈ usedPairs X g S ↔ ∃ v ∈ S, ∃ b ∈ X v, e = s(b, g v b) := by
  simp only [usedPairs, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, b, hb, rfl⟩; exact ⟨v, hv, b, hb, rfl⟩
  · rintro ⟨v, hv, b, hb, rfl⟩; exact ⟨v, hv, b, hb, rfl⟩

theorem usedPairs_mem {X : V → Finset V} {g : V → V → V} {S : Finset V} {v b : V}
    (hv : v ∈ S) (hb : b ∈ X v) : s(b, g v b) ∈ usedPairs X g S :=
  mem_usedPairs.2 ⟨v, hv, b, hb, rfl⟩

/-- **The sweep.**  A rule that pairs up one more link, avoiding the edges already used and keeping
the protected-level load under budget, assembles into a whole paired link system. -/
theorem exists_pairedLinkCore_of_step
    {F : Finset (Sym2 V)} {W' W'' D : Finset V} {X : V → Finset V} {γ : ℝ} (hγ : 0 ≤ γ)
    (hstep : ∀ S : Finset V, S ⊆ D → ∀ g₀ : V → V → V, ∀ u ∈ D, u ∉ S →
      ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
        (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
        (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
        (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
        (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
          ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
            ≤ γ * (W''.card : ℝ))) :
    ∃ g : V → V → V, IsPairedLinkCore F W' W'' D X γ g := by
  classical
  -- the invariant, carried along the sweep
  suffices h : ∀ S : Finset V, S ⊆ D → ∃ g : V → V → V,
      (∀ u ∈ S, ∀ a ∈ X u, g u a ∈ X u) ∧
      (∀ u ∈ S, ∀ a ∈ X u, g u (g u a) = a) ∧
      (∀ u ∈ S, ∀ a ∈ X u, g u a ≠ a) ∧
      (∀ u ∈ S, ∀ a ∈ X u, s(a, g u a) ∈ F) ∧
      (∀ u ∈ S, ∀ a ∈ X u, a ∉ W'' ∨ g u a ∉ W'') ∧
      (∀ u ∈ S, ∀ a ∈ X u, ∀ v ∈ S, ∀ b ∈ X v, s(a, g u a) = s(b, g v b) → u = v) ∧
      (∀ v ∈ W', ((S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')).card : ℝ)
        ≤ γ * (W''.card : ℝ)) by
    obtain ⟨g, h1, h2, h3, h4, h5, h6, h7⟩ := h D (Finset.Subset.refl D)
    exact ⟨g, ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨fun _ a => a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro v _
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hγ (Nat.cast_nonneg _)
  | insert u S huS ih =>
    intro hsub
    have huD : u ∈ D := hsub (Finset.mem_insert_self u S)
    have hSD : S ⊆ D := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    obtain ⟨g₀, h1, h2, h3, h4, h5, h6, h7⟩ := ih hSD
    obtain ⟨p, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hstep S hSD g₀ u huD huS
    set g : V → V → V := Function.update g₀ u p with hgdef
    have hgu : g u = p := by rw [hgdef, Function.update_self]
    have hgv : ∀ v : V, v ≠ u → g v = g₀ v := by
      intro v hv
      rw [hgdef, Function.update_of_ne hv]
    have hgS : ∀ v ∈ S, g v = g₀ v := by
      intro v hv
      exact hgv v (fun hcon => huS (hcon ▸ hv))
    refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp1 a ha
      · rw [hgS w hwS]; exact h1 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp2 a ha
      · rw [hgS w hwS]; exact h2 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp3 a ha
      · rw [hgS w hwS]; exact h3 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp4 a ha
      · rw [hgS w hwS]; exact h4 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp5 a ha
      · rw [hgS w hwS]; exact h5 w hwS a ha
    · -- the pairs of different outer vertices are different edges
      intro w hw a ha v hv b hb heq
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rcases Finset.mem_insert.1 hv with rfl | hvS
        · rfl
        · exfalso
          rw [hgu] at heq
          rw [hgS v hvS] at heq
          exact hp6 a ha (heq ▸ usedPairs_mem hvS hb)
      · rcases Finset.mem_insert.1 hv with rfl | hvS
        · exfalso
          rw [hgu] at heq
          rw [hgS w hwS] at heq
          exact hp6 b hb (heq.symm ▸ usedPairs_mem hwS ha)
        · rw [hgS w hwS, hgS v hvS] at heq
          exact h6 w hwS a ha v hvS b hb heq
    · -- the protected-level load
      intro v hv
      have hfilterS : S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')
          = S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'') := by
        refine Finset.filter_congr ?_
        intro w hw
        rw [hgS w hw]
      by_cases hcase : v ∈ X u ∧ g u v ∈ W''
      · have hins : (insert u S).filter (fun w => v ∈ X w ∧ g w v ∈ W'')
            = insert u (S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')) := by
          rw [Finset.filter_insert, if_pos hcase]
        have hnot : u ∉ S.filter (fun w => v ∈ X w ∧ g w v ∈ W'') :=
          fun hcon => huS (Finset.mem_of_mem_filter u hcon)
        rw [hins, Finset.card_insert_of_notMem hnot, hfilterS]
        have hstepload := hp7 v hv hcase.1 (by rw [← hgu]; exact hcase.2)
        push_cast
        linarith
      · have hins : (insert u S).filter (fun w => v ∈ X w ∧ g w v ∈ W'')
            = S.filter (fun w => v ∈ X w ∧ g w v ∈ W'') := by
          rw [Finset.filter_insert, if_neg hcase]
        rw [hins, hfilterS]
        exact h7 v hv

/-- **The sweep, with its invariants handed to the rule.**  Same as
`BKLO.exists_pairedLinkCore_of_step`, except that the rule pairing up one more link may use the
fact that the pairings already chosen are involutions of their own links.  This is a genuinely
weaker demand on the rule, and it is what a ledger argument needs: it identifies the edge already
used at a vertex `a` by an earlier outer vertex `w` as the single edge `s(a, g₀ w a)`. -/
theorem exists_pairedLinkCore_of_step_inv
    {F : Finset (Sym2 V)} {W' W'' D : Finset V} {X : V → Finset V} {γ : ℝ} (hγ : 0 ≤ γ)
    (hstep : ∀ S : Finset V, S ⊆ D → ∀ g₀ : V → V → V,
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
      ∀ u ∈ D, u ∉ S →
      ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
        (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
        (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
        (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
        (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
          ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
            ≤ γ * (W''.card : ℝ))) :
    ∃ g : V → V → V, IsPairedLinkCore F W' W'' D X γ g := by
  classical
  -- the invariant, carried along the sweep
  suffices h : ∀ S : Finset V, S ⊆ D → ∃ g : V → V → V,
      (∀ u ∈ S, ∀ a ∈ X u, g u a ∈ X u) ∧
      (∀ u ∈ S, ∀ a ∈ X u, g u (g u a) = a) ∧
      (∀ u ∈ S, ∀ a ∈ X u, g u a ≠ a) ∧
      (∀ u ∈ S, ∀ a ∈ X u, s(a, g u a) ∈ F) ∧
      (∀ u ∈ S, ∀ a ∈ X u, a ∉ W'' ∨ g u a ∉ W'') ∧
      (∀ u ∈ S, ∀ a ∈ X u, ∀ v ∈ S, ∀ b ∈ X v, s(a, g u a) = s(b, g v b) → u = v) ∧
      (∀ v ∈ W', ((S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')).card : ℝ)
        ≤ γ * (W''.card : ℝ)) by
    obtain ⟨g, h1, h2, h3, h4, h5, h6, h7⟩ := h D (Finset.Subset.refl D)
    exact ⟨g, ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨fun _ a => a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro v _
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hγ (Nat.cast_nonneg _)
  | insert u S huS ih =>
    intro hsub
    have huD : u ∈ D := hsub (Finset.mem_insert_self u S)
    have hSD : S ⊆ D := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    obtain ⟨g₀, h1, h2, h3, h4, h5, h6, h7⟩ := ih hSD
    obtain ⟨p, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hstep S hSD g₀ h1 h2 u huD huS
    set g : V → V → V := Function.update g₀ u p with hgdef
    have hgu : g u = p := by rw [hgdef, Function.update_self]
    have hgv : ∀ v : V, v ≠ u → g v = g₀ v := by
      intro v hv
      rw [hgdef, Function.update_of_ne hv]
    have hgS : ∀ v ∈ S, g v = g₀ v := by
      intro v hv
      exact hgv v (fun hcon => huS (hcon ▸ hv))
    refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp1 a ha
      · rw [hgS w hwS]; exact h1 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp2 a ha
      · rw [hgS w hwS]; exact h2 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp3 a ha
      · rw [hgS w hwS]; exact h3 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp4 a ha
      · rw [hgS w hwS]; exact h4 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp5 a ha
      · rw [hgS w hwS]; exact h5 w hwS a ha
    · -- the pairs of different outer vertices are different edges
      intro w hw a ha v hv b hb heq
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rcases Finset.mem_insert.1 hv with rfl | hvS
        · rfl
        · exfalso
          rw [hgu] at heq
          rw [hgS v hvS] at heq
          exact hp6 a ha (heq ▸ usedPairs_mem hvS hb)
      · rcases Finset.mem_insert.1 hv with rfl | hvS
        · exfalso
          rw [hgu] at heq
          rw [hgS w hwS] at heq
          exact hp6 b hb (heq.symm ▸ usedPairs_mem hwS ha)
        · rw [hgS w hwS, hgS v hvS] at heq
          exact h6 w hwS a ha v hvS b hb heq
    · -- the protected-level load
      intro v hv
      have hfilterS : S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')
          = S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'') := by
        refine Finset.filter_congr ?_
        intro w hw
        rw [hgS w hw]
      by_cases hcase : v ∈ X u ∧ g u v ∈ W''
      · have hins : (insert u S).filter (fun w => v ∈ X w ∧ g w v ∈ W'')
            = insert u (S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')) := by
          rw [Finset.filter_insert, if_pos hcase]
        have hnot : u ∉ S.filter (fun w => v ∈ X w ∧ g w v ∈ W'') :=
          fun hcon => huS (Finset.mem_of_mem_filter u hcon)
        rw [hins, Finset.card_insert_of_notMem hnot, hfilterS]
        have hstepload := hp7 v hv hcase.1 (by rw [← hgu]; exact hcase.2)
        push_cast
        linarith
      · have hins : (insert u S).filter (fun w => v ∈ X w ∧ g w v ∈ W'')
            = S.filter (fun w => v ∈ X w ∧ g w v ∈ W'') := by
          rw [Finset.filter_insert, if_neg hcase]
        rw [hins, hfilterS]
        exact h7 v hv

/-- **The sweep, carrying an arbitrary invariant.**  Same as
`BKLO.exists_pairedLinkCore_of_step_inv`, except that the rule may also assume an arbitrary
invariant `J` of the pairings already chosen, provided it maintains it.  This is the weakest local
demand of the sweep: the rule is free to *arrange* the past, not only to react to it — which is
what a spread invariant, controlling where the earlier links have already paired a vertex, needs.
-/
theorem exists_pairedLinkCore_of_step_invariant
    {F : Finset (Sym2 V)} {W' W'' D : Finset V} {X : V → Finset V} {γ : ℝ} (hγ : 0 ≤ γ)
    (J : Finset V → (V → V → V) → Prop) (hJ0 : J (∅ : Finset V) (fun _ a => a))
    (hstep : ∀ S : Finset V, S ⊆ D → ∀ g₀ : V → V → V,
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
      J S g₀ → ∀ u ∈ D, u ∉ S →
      ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
        (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
        (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
        (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
        (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
          ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
            ≤ γ * (W''.card : ℝ)) ∧
        J (insert u S) (Function.update g₀ u p)) :
    ∃ g : V → V → V, IsPairedLinkCore F W' W'' D X γ g := by
  classical
  -- the invariant, carried along the sweep
  suffices h : ∀ S : Finset V, S ⊆ D → ∃ g : V → V → V,
      (∀ u ∈ S, ∀ a ∈ X u, g u a ∈ X u) ∧
      (∀ u ∈ S, ∀ a ∈ X u, g u (g u a) = a) ∧
      (∀ u ∈ S, ∀ a ∈ X u, g u a ≠ a) ∧
      (∀ u ∈ S, ∀ a ∈ X u, s(a, g u a) ∈ F) ∧
      (∀ u ∈ S, ∀ a ∈ X u, a ∉ W'' ∨ g u a ∉ W'') ∧
      (∀ u ∈ S, ∀ a ∈ X u, ∀ v ∈ S, ∀ b ∈ X v, s(a, g u a) = s(b, g v b) → u = v) ∧
      (∀ v ∈ W', ((S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')).card : ℝ)
        ≤ γ * (W''.card : ℝ)) ∧ J S g by
    obtain ⟨g, h1, h2, h3, h4, h5, h6, h7, -⟩ := h D (Finset.Subset.refl D)
    exact ⟨g, ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨fun _ a => a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro u hu; exact absurd hu (Finset.notMem_empty u)
    · intro v _
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hγ (Nat.cast_nonneg _)
    · exact hJ0
  | insert u S huS ih =>
    intro hsub
    have huD : u ∈ D := hsub (Finset.mem_insert_self u S)
    have hSD : S ⊆ D := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    obtain ⟨g₀, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih hSD
    obtain ⟨p, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := hstep S hSD g₀ h1 h2 h8 u huD huS
    set g : V → V → V := Function.update g₀ u p with hgdef
    have hgu : g u = p := by rw [hgdef, Function.update_self]
    have hgv : ∀ v : V, v ≠ u → g v = g₀ v := by
      intro v hv
      rw [hgdef, Function.update_of_ne hv]
    have hgS : ∀ v ∈ S, g v = g₀ v := by
      intro v hv
      exact hgv v (fun hcon => huS (hcon ▸ hv))
    refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp1 a ha
      · rw [hgS w hwS]; exact h1 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp2 a ha
      · rw [hgS w hwS]; exact h2 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp3 a ha
      · rw [hgS w hwS]; exact h3 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp4 a ha
      · rw [hgS w hwS]; exact h4 w hwS a ha
    · intro w hw a ha
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [hgu]; exact hp5 a ha
      · rw [hgS w hwS]; exact h5 w hwS a ha
    · -- the pairs of different outer vertices are different edges
      intro w hw a ha v hv b hb heq
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rcases Finset.mem_insert.1 hv with rfl | hvS
        · rfl
        · exfalso
          rw [hgu] at heq
          rw [hgS v hvS] at heq
          exact hp6 a ha (heq ▸ usedPairs_mem hvS hb)
      · rcases Finset.mem_insert.1 hv with rfl | hvS
        · exfalso
          rw [hgu] at heq
          rw [hgS w hwS] at heq
          exact hp6 b hb (heq.symm ▸ usedPairs_mem hwS ha)
        · rw [hgS w hwS, hgS v hvS] at heq
          exact h6 w hwS a ha v hvS b hb heq
    · -- the protected-level load
      intro v hv
      have hfilterS : S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')
          = S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'') := by
        refine Finset.filter_congr ?_
        intro w hw
        rw [hgS w hw]
      by_cases hcase : v ∈ X u ∧ g u v ∈ W''
      · have hins : (insert u S).filter (fun w => v ∈ X w ∧ g w v ∈ W'')
            = insert u (S.filter (fun w => v ∈ X w ∧ g w v ∈ W'')) := by
          rw [Finset.filter_insert, if_pos hcase]
        have hnot : u ∉ S.filter (fun w => v ∈ X w ∧ g w v ∈ W'') :=
          fun hcon => huS (Finset.mem_of_mem_filter u hcon)
        rw [hins, Finset.card_insert_of_notMem hnot, hfilterS]
        have hstepload := hp7 v hv hcase.1 (by rw [← hgu]; exact hcase.2)
        push_cast
        linarith
      · have hins : (insert u S).filter (fun w => v ∈ X w ∧ g w v ∈ W'')
            = S.filter (fun w => v ∈ X w ∧ g w v ∈ W'') := by
          rw [Finset.filter_insert, if_neg hcase]
        rw [hins, hfilterS]
        exact h7 v hv
    · exact hp8

end BKLO
