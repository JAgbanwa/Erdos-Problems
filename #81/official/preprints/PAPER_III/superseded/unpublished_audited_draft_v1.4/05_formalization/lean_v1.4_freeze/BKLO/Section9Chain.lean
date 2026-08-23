/-
# BKLO §9 for `r = 2`, `F = K₃`: the chain of column pairs inside one part

Fix two distinct parts `U` and `W`.  For `u, y ∈ U` write `pair(u, y; W)` for the parity vector
`uvec u W + uvec y W`.  A single triangle `{u, y, w}` with `w ∈ W` realises `pair(u, y; W)`, but
using one triangle per pair would create vertices of huge degree.  Instead we link the vertices of
`U` in a *chain*

  `r = v₁ — z₁ — v₂ — z₂ — v₃ — ⋯`

whose links are realised by triangles `{v, z, w}` with apex `w ∈ W`; the intermediate vertices `z`
and the apexes `w` are chosen greedily among vertices of small current degree, so that all degrees
stay bounded by an absolute constant.  Since `pair(r, v; W)` telescopes along the chain, every
`pair(u, y; W)` becomes reachable.

`BKLO.chain_exists` is the resulting statement.  Everything here is `sorry`-free.
-/
import BKLO.Section9Greedy
import BKLO.Section9Assembly

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

theorem card_pair_le_six (a b : V) : ({a, b} : Finset V).card ≤ 6 := by
  refine le_trans (Finset.card_insert_le _ _) ?_
  simp

theorem card_triple_le_six (a b c : V) : ({a, b, c} : Finset V).card ≤ 6 := by
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
  simp

theorem card_quad_le_six (a b c e : V) : ({a, b, c, e} : Finset V).card ≤ 6 := by
  refine le_trans (Finset.card_insert_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1) ?_
  simp

private theorem zmod2_pair_trans : ∀ p q s : ZMod 2, (p + q) + (q + s) = p + s := by decide +kernel

/-- The three edges of the triangle `{a, b, c}` lie in `G`. -/
theorem cliqueEdges_subset_of_edges {G : Finset (Sym2 V)} {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e1 : s(a, b) ∈ G) (e2 : s(b, c) ∈ G) (e3 : s(a, c) ∈ G) :
    cliqueEdges ({a, b, c} : Finset V) ⊆ G := by
  rw [cliqueEdges_triple' hab hac hbc]
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> assumption

/-- Disjointness of a triangle's edges from an edge set, checked edge by edge. -/
theorem cliqueEdges_disjoint_of_notMem {F : Finset (Sym2 V)} {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e1 : s(a, b) ∉ F) (e2 : s(b, c) ∉ F) (e3 : s(a, c) ∉ F) :
    Disjoint (cliqueEdges ({a, b, c} : Finset V)) F := by
  rw [cliqueEdges_triple' hab hac hbc]
  refine Finset.disjoint_left.2 fun e he heF => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact e1 heF
  · exact e2 heF
  · exact e3 heF

theorem card_triple_eq_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_insert_of_notMem (by simp [hbc]),
    Finset.card_singleton]

section Chain

variable {G : Finset (Sym2 V)} {S : Finset V} {P : Finset (Finset V)} {idx : Finset V → ℕ}
  {γ : ℝ} {D₀ Mtop Ecap : ℕ}

/-- **The chain construction.**  Along a list `L` of vertices of the part `U`, starting from the
root `r ∈ U`, the family is extended by two triangles per list entry so that `pair(r, u; W)` becomes
reachable for every `u ∈ L`, keeping all degrees below `m + 4`. -/
theorem chain_exists
    (hdisj : ∀ X ∈ P, ∀ X' ∈ P, X ≠ X' → Disjoint X X')
    (hsubS : ∀ X ∈ P, X ⊆ S)
    (hdegG : ∀ x ∈ S, ∀ X ∈ P, (1 / 2 + γ) * (X.card : ℝ) ≤ (degTo G x X : ℝ))
    (hnum : ∀ X ∈ P, ((6 + 2 * Mtop + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ) < 2 * γ * (X.card : ℝ))
    {U W : Finset V} (hU : U ∈ P) (hW : W ∈ P) (hUW : U ≠ W)
    (m : ℕ) (hm4 : D₀ + 4 ≤ m) (hmtop : m + 6 ≤ Mtop) :
    ∀ (L : List V) (r : V) (𝒯 : Finset (Finset V)),
      r ∈ U → (∀ v ∈ L, v ∈ U) → L.Nodup → r ∉ L →
      IsTriFamily 𝒯 → famEdges 𝒯 ⊆ G → (∀ T ∈ 𝒯, T ⊆ S) →
      3 * (𝒯.card + 2 * L.length) ≤ Ecap →
      (∀ v, edeg (famEdges 𝒯) v ≤ m + 4) →
      (∀ v ∈ L, edeg (famEdges 𝒯) v ≤ m) →
      edeg (famEdges 𝒯) r ≤ m + 2 →
      ∃ 𝒯' : Finset (Finset V), 𝒯 ⊆ 𝒯' ∧ IsTriFamily 𝒯' ∧ famEdges 𝒯' ⊆ G ∧
        (∀ T ∈ 𝒯', T ⊆ S) ∧ 𝒯'.card ≤ 𝒯.card + 2 * L.length ∧
        (∀ v, edeg (famEdges 𝒯') v ≤ m + 4) ∧
        ∀ u ∈ L, Reach P idx 𝒯' (fun x W' => uvec r W x W' + uvec u W x W') := by
  classical
  intro L
  induction L with
  | nil =>
    intro r 𝒯 _ _ _ _ hfam hGsub hSsub _ hdeg _ _
    exact ⟨𝒯, Finset.Subset.refl _, hfam, hGsub, hSsub, by simp, hdeg, by simp⟩
  | cons u L' ih =>
    intro r 𝒯 hr hLU hnodup hrL hfam hGsub hSsub hbudget hdeg hdegL hdegr
    -- basic facts
    have huU : u ∈ U := hLU u (by simp)
    have hru : r ≠ u := fun h => hrL (by simp [h])
    have huL' : u ∉ L' := (List.nodup_cons.1 hnodup).1
    have hrS : r ∈ S := hsubS U hU hr
    have huS : u ∈ S := hsubS U hU huU
    set F := famEdges 𝒯 with hF
    have hFcard : F.card ≤ Ecap := by
      have h1 : F.card ≤ 3 * 𝒯.card := by rw [hF]; exact famEdges_card_le hfam.card_three
      have hlen : 0 < (u :: L').length := by simp
      omega
    have hMtop : ∀ v : V, edeg F v ≤ Mtop := fun v => le_trans (hdeg v) (by omega)
    -- choose the intermediate vertex `z ∈ U`
    obtain ⟨z, hzU, hzAv, hrz, huz, hrzF, huzF, hzdeg⟩ :=
      exists_common_nbr hdegG hrS huS hU F hMtop hFcard ({r, u} : Finset V)
        (card_pair_le_six r u) (hnum U hU)
    have hzr : z ≠ r := fun h => hzAv (by simp [h])
    have hzu : z ≠ u := fun h => hzAv (by simp [h])
    have hzS : z ∈ S := hsubS U hU hzU
    -- choose the first apex `a ∈ W`
    obtain ⟨a, haW, haAv, hra, hza, hraF, hzaF, hadeg⟩ :=
      exists_common_nbr hdegG hrS hzS hW F hMtop hFcard ({r, u, z} : Finset V)
        (card_triple_le_six r u z) (hnum W hW)
    have har : a ≠ r := fun h => haAv (by simp [h])
    have hau : a ≠ u := fun h => haAv (by simp [h])
    have haz : a ≠ z := fun h => haAv (by simp [h])
    have haS : a ∈ S := hsubS W hW haW
    -- the first triangle
    set T₁ : Finset V := {r, z, a} with hT₁
    have hT₁card : T₁.card = 3 := card_triple_eq_three (Ne.symm hzr) (Ne.symm har) (Ne.symm haz)
    have hT₁S : T₁ ⊆ S := by
      intro v hv
      simp only [hT₁, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hT₁G : cliqueEdges T₁ ⊆ G :=
      cliqueEdges_subset_of_edges (Ne.symm hzr) (Ne.symm har) (Ne.symm haz) hrz hza hra
    have hT₁F : Disjoint (cliqueEdges T₁) F :=
      cliqueEdges_disjoint_of_notMem (Ne.symm hzr) (Ne.symm har) (Ne.symm haz) hrzF hzaF hraF
    set 𝒯₁ : Finset (Finset V) := insert T₁ 𝒯 with h𝒯₁
    have hfam₁ : IsTriFamily 𝒯₁ := isTriFamily_insert hfam hT₁card hT₁F
    have hF₁ : famEdges 𝒯₁ = F ∪ cliqueEdges T₁ := by
      rw [h𝒯₁, famEdges_insert, Finset.union_comm]
    have hdeg₁ : ∀ v : V, edeg (famEdges 𝒯₁) v ≤ edeg F v + 2 := by
      intro v; rw [hF₁]; exact edeg_union_triangle_le hT₁card F v
    have hdeg₁' : ∀ v : V, v ∉ T₁ → edeg (famEdges 𝒯₁) v = edeg F v := by
      intro v hv; rw [hF₁]; exact edeg_union_triangle_eq hT₁card F hv
    have hF₁card : (famEdges 𝒯₁).card ≤ Ecap := by
      have h1 := famEdges_card_le hfam₁.card_three
      have h2 : 𝒯₁.card ≤ 𝒯.card + 1 := by
        rw [h𝒯₁]; exact Finset.card_insert_le _ _
      have hlen : 0 < (u :: L').length := by simp
      omega
    have hMtop₁ : ∀ v : V, edeg (famEdges 𝒯₁) v ≤ Mtop := by
      intro v
      have := hdeg₁ v
      have := hdeg v
      omega
    -- choose the second apex `b ∈ W`
    obtain ⟨b, hbW, hbAv, hzb, hub, hzbF, hubF, hbdeg⟩ :=
      exists_common_nbr hdegG hzS huS hW (famEdges 𝒯₁) hMtop₁ hF₁card ({r, u, z, a} : Finset V)
        (card_quad_le_six r u z a) (hnum W hW)
    have hbr : b ≠ r := fun h => hbAv (by simp [h])
    have hbu : b ≠ u := fun h => hbAv (by simp [h])
    have hbz : b ≠ z := fun h => hbAv (by simp [h])
    have hba : b ≠ a := fun h => hbAv (by simp [h])
    have hbS : b ∈ S := hsubS W hW hbW
    -- the second triangle
    set T₂ : Finset V := {z, u, b} with hT₂
    have hT₂card : T₂.card = 3 := card_triple_eq_three hzu (Ne.symm hbz) (Ne.symm hbu)
    have hT₂S : T₂ ⊆ S := by
      intro v hv
      simp only [hT₂, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hT₂G : cliqueEdges T₂ ⊆ G :=
      cliqueEdges_subset_of_edges hzu (Ne.symm hbz) (Ne.symm hbu)
        (by rw [Sym2.eq_swap]; exact huz) hub hzb
    have hzuT₁ : s(z, u) ∉ cliqueEdges T₁ := by
      intro hc
      rw [hT₁, mem_cliqueEdgesV] at hc
      have hu' : u ∈ ({r, z, a} : Finset V) := hc.1 u (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
      rcases hu' with h | h | h
      · exact hru h.symm
      · exact hzu h.symm
      · exact hau h.symm
    have hT₂F : Disjoint (cliqueEdges T₂) (famEdges 𝒯₁) := by
      refine cliqueEdges_disjoint_of_notMem hzu (Ne.symm hbz) (Ne.symm hbu) ?_ ?_ ?_
      · rw [hF₁]
        simp only [Finset.mem_union, not_or]
        exact ⟨by rw [Sym2.eq_swap]; exact huzF, hzuT₁⟩
      · exact hubF
      · exact hzbF
    set 𝒯₂ : Finset (Finset V) := insert T₂ 𝒯₁ with h𝒯₂
    have hfam₂ : IsTriFamily 𝒯₂ := isTriFamily_insert hfam₁ hT₂card hT₂F
    have hF₂ : famEdges 𝒯₂ = famEdges 𝒯₁ ∪ cliqueEdges T₂ := by
      rw [h𝒯₂, famEdges_insert, Finset.union_comm]
    have hdeg₂ : ∀ v : V, edeg (famEdges 𝒯₂) v ≤ edeg (famEdges 𝒯₁) v + 2 := by
      intro v; rw [hF₂]; exact edeg_union_triangle_le hT₂card _ v
    have hdeg₂' : ∀ v : V, v ∉ T₂ → edeg (famEdges 𝒯₂) v = edeg (famEdges 𝒯₁) v := by
      intro v hv; rw [hF₂]; exact edeg_union_triangle_eq hT₂card _ hv
    -- membership facts for the degree bookkeeping
    have hrT₂ : r ∉ T₂ := by simp [hT₂, Ne.symm hzr, hru, Ne.symm hbr]
    have huT₁ : u ∉ T₁ := by simp [hT₁, Ne.symm hru, Ne.symm hzu, Ne.symm hau]
    have haT₂ : a ∉ T₂ := by simp [hT₂, haz, hau, Ne.symm hba]
    have hzT₁ : z ∈ T₁ := by simp [hT₁]
    have hzT₂ : z ∈ T₂ := by simp [hT₂]
    -- the global degree bound after the two triangles
    have hdegall : ∀ v : V, edeg (famEdges 𝒯₂) v ≤ m + 4 := by
      intro v
      by_cases hvr : v = r
      · subst hvr
        rw [hdeg₂' v hrT₂]
        have := hdeg₁ v
        omega
      · by_cases hvu : v = u
        · subst hvu
          have h1 := hdeg₂ v
          have h2 := hdeg₁' v huT₁
          have h3 := hdegL v (by simp)
          omega
        · by_cases hvz : v = z
          · subst hvz
            have h1 := hdeg₂ v
            have h2 := hdeg₁ v
            omega
          · by_cases hva : v = a
            · subst hva
              rw [hdeg₂' v haT₂]
              have := hdeg₁ v
              omega
            · by_cases hvb : v = b
              · subst hvb
                have := hdeg₂ v
                omega
              · have hvT₁ : v ∉ T₁ := by simp [hT₁, hvr, hvz, hva]
                have hvT₂ : v ∉ T₂ := by simp [hT₂, hvz, hvu, hvb]
                rw [hdeg₂' v hvT₂, hdeg₁' v hvT₁]
                exact hdeg v
    -- the hypotheses for the recursive call
    have hdegL' : ∀ v ∈ L', edeg (famEdges 𝒯₂) v ≤ m := by
      intro v hv
      have hvU : v ∈ U := hLU v (by simp [hv])
      have hvr : v ≠ r := fun h => hrL (by simp [h ▸ hv])
      have hvu : v ≠ u := fun h => huL' (h ▸ hv)
      have hvW : v ∉ W := fun hc => (Finset.disjoint_left.1 (hdisj U hU W hW hUW) hvU) hc
      have hva : v ≠ a := fun h => hvW (h ▸ haW)
      have hvb : v ≠ b := fun h => hvW (h ▸ hbW)
      by_cases hvz : v = z
      · subst hvz
        have h1 := hdeg₂ v
        have h2 := hdeg₁ v
        omega
      · have hvT₁ : v ∉ T₁ := by simp [hT₁, hvr, hvz, hva]
        have hvT₂ : v ∉ T₂ := by simp [hT₂, hvz, hvu, hvb]
        rw [hdeg₂' v hvT₂, hdeg₁' v hvT₁]
        exact hdegL v (by simp [hv])
    have hdegu : edeg (famEdges 𝒯₂) u ≤ m + 2 := by
      have h1 := hdeg₂ u
      have h2 := hdeg₁' u huT₁
      have h3 := hdegL u (by simp)
      omega
    have h𝒯₂card : 𝒯₂.card ≤ 𝒯.card + 2 := by
      have h1 : 𝒯₂.card ≤ 𝒯₁.card + 1 := by rw [h𝒯₂]; exact Finset.card_insert_le _ _
      have h2 : 𝒯₁.card ≤ 𝒯.card + 1 := by rw [h𝒯₁]; exact Finset.card_insert_le _ _
      omega
    have hbudget' : 3 * (𝒯₂.card + 2 * L'.length) ≤ Ecap := by
      have hlen : (u :: L').length = L'.length + 1 := by simp
      omega
    have hGsub₂ : famEdges 𝒯₂ ⊆ G := by
      rw [hF₂, hF₁]
      exact Finset.union_subset (Finset.union_subset hGsub hT₁G) hT₂G
    have hSsub₂ : ∀ T ∈ 𝒯₂, T ⊆ S := by
      intro T hT
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact hT₂S
      · rcases Finset.mem_insert.1 hT with rfl | hT
        · exact hT₁S
        · exact hSsub T hT
    -- recurse
    obtain ⟨𝒯', hsub', hfam', hG', hS', hcard', hdeg', hreal'⟩ :=
      ih u 𝒯₂ huU (fun v hv => hLU v (by simp [hv])) (List.nodup_cons.1 hnodup).2 huL'
        hfam₂ hGsub₂ hSsub₂ hbudget' hdegall hdegL' hdegu
    have hT₁' : T₁ ∈ 𝒯' := hsub' (by simp [h𝒯₂, h𝒯₁])
    have hT₂' : T₂ ∈ 𝒯' := hsub' (by simp [h𝒯₂])
    -- the pair `(r, u)` is realised by the two new triangles
    have hpairu : Reach P idx 𝒯' (fun x W' => uvec r W x W' + uvec u W x W') := by
      refine ((Reach.of_mem (idx := idx) hT₁').add hfam' (Reach.of_mem (idx := idx) hT₂')).congr ?_
      intro W' hW' x hx
      have e1 : vecOf T₁ x W' = uvec r W x W' + uvec z W x W' := by
        rw [hT₁, triple_swap₂ r z a]
        exact vecOf_two_in_part hdisj hW hU haW hr hzU har haz (Ne.symm hzr)
          hW' hx
      have e2 : vecOf T₂ x W' = uvec z W x W' + uvec u W x W' := by
        rw [hT₂, triple_swap₂ z u b]
        exact vecOf_two_in_part hdisj hW hU hbW hzU huU hbz hbu hzu hW' hx
      rw [e1, e2]
      exact zmod2_pair_trans _ _ _
    refine ⟨𝒯', (Finset.Subset.trans (Finset.Subset.trans (Finset.subset_insert T₁ 𝒯) (Finset.subset_insert T₂ 𝒯₁)) hsub'), hfam', hG', hS',
      by simp only [List.length_cons]; omega, hdeg', ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hpairu
    · refine (hpairu.add hfam' (hreal' y hy)).congr ?_
      intro W' hW' x hx
      exact zmod2_pair_trans _ _ _

end Chain

end BKLO
