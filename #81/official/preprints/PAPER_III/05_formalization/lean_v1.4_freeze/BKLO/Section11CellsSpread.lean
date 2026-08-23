/-
# The cells absorber is sparse: reserving the per-cell absorbers in a spread way

`BKLO.exists_cellsAbsorbers` (`BKLO/Section11CellsBuild.lean`) reserves one bounded absorber per
cell, edge-disjointly, but pays for it with the crude bound `Δ(A*) ≤ |A*| ≤ |Q| · M`, which for the
`Θ(|S|/m)` cells of the vortex is a positive fraction of `|S|` — far too much for `A*` to be
reserved out of a dense host.

This file removes that defect.  The reservation is run *spread*: before reserving the absorber of
the next cell, the vertices that already carry many reserved edges are deleted from the host.
There are few such vertices — the whole reservation has `O(|S|)` edges — so the host stays dense,
and the resulting absorber has

```
Δ(A*) ≤ B,     B = B(C, γ, ρ) a constant,
```

whenever the number of cells is at most `ρ|S|` (for the vortex, `ρ ≈ 2/m`).  In particular `A*` is
sparse in the sense §11 needs: `Δ(A*) ≤ γ|S|` for `|S|` large.

The main statement is `BKLO.exists_cellsAbsorbers_spread`.  Everything here is `sorry`-free.
-/
import BKLO.Section11CellsBuild
import BKLO.VortexPartition
import BKLO.ParityTools
import BKLO.Section9Greedy

open Finset

set_option maxHeartbeats 1000000

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Degree facts about restricting the host to a subset of the vertices -/

/-- A graph spanned by `T` has no edges at a vertex outside `T`. -/
theorem edeg_eq_zero_outside {F : Finset (Sym2 V)} {T : Finset V} {v : V}
    (hF : F ⊆ cliqueEdges T) (hv : v ∉ T) : edeg F v = 0 := by
  classical
  unfold edeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun e he hve => hv ((mem_cliqueEdgesV.1 (hF he)).1 v hve)

/-- **Restricting the host costs each vertex at most the number of deleted vertices.**  If `E` is
spanned by `S` and `T ⊆ S`, then a vertex of `T` keeps all but `|S \ T|` of its degree inside
`T`. -/
theorem edeg_inter_cliqueEdges_ge {E : Finset (Sym2 V)} {S T : Finset V} {v : V}
    (hES : E ⊆ cliqueEdges S) (hv : v ∈ T) :
    edeg E v ≤ edeg (E ∩ cliqueEdges T) v + (S \ T).card := by
  classical
  have hloop : ∀ e ∈ E, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hES he)).2
  have hsupp : ∀ e ∈ E, ∀ x ∈ e, x ∈ S := fun e he x hx => (mem_cliqueEdgesV.1 (hES he)).1 x hx
  have h1 : edeg E v = degTo E v S := edeg_eq_degTo_of_supp hsupp v
  have h2 : nbhdIn E v S ⊆ nbhdIn E v T ∪ (S \ T) := by
    intro y hy
    rw [mem_nbhdIn] at hy
    by_cases hyT : y ∈ T
    · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hyT, hy.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hy.1, hyT⟩)
  have h3 : degTo E v S ≤ degTo E v T + (S \ T).card :=
    le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)
  have h4 : degTo E v T ≤ edeg (E ∩ cliqueEdges T) v :=
    degTo_le_edeg_inter_cliqueEdges hv hloop
  omega

/-! ### The spread reservation -/

/-- **The cells absorber, reserved spread — hence sparse.**

For every core size `C`, every `γ ∈ (0, 1/10]` and every cell density `ρ > 0` there are constants
`B` and `n₀` such that: inside a host `E ⊆ cliqueEdges S` on at least `n₀` vertices with minimum
degree `(9/10 + 2γ)|S|`, and for every family `Q` of at most `ρ|S|` pairwise disjoint cells of size
at most `C`, one can reserve pairwise edge-disjoint bounded absorbers `R P ⊆ E`, one per cell `P`,
whose union has maximum degree at most the **constant** `B`.

This is BKLO §8 in the cells form, with the reservation spread over the host: at each step the
vertices already carrying more than a constant number of reserved edges are removed from the host
before the next absorber is placed, and there are few of them because the whole reservation has
`O(|S|)` edges. -/
theorem exists_cellsAbsorbers_spread (C : ℕ) (γ ρ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 10) :
    ∃ B n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (Q : Finset (Finset V)),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + 2 * γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      (∀ P ∈ Q, P ⊆ S) → (∀ P ∈ Q, P.card ≤ C) →
      (∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint P P') →
      ((Q.card : ℝ) ≤ ρ * (S.card : ℝ)) →
      ∃ R : Finset V → Finset (Sym2 V),
        (∀ P ∈ Q, R P ⊆ E) ∧ (∀ P ∈ Q, CoreAbsorbers P (R P)) ∧
        (∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint (R P) (R P')) ∧
        (∀ v : V, edeg (Q.biUnion R) v ≤ B) := by
  classical
  obtain ⟨M, n₁, hbase⟩ := coreAbsorberExistence_bounded C γ
  -- the degree threshold above which a vertex is deleted from the host
  set D : ℕ := ⌈2 * ρ * (M : ℝ) / γ⌉₊ with hDdef
  have hD : 2 * ρ * (M : ℝ) / γ ≤ (D : ℝ) := Nat.le_ceil _
  refine ⟨D + 2 * M, max (2 * n₁) (⌈4 * ((D : ℝ) + 2 * M) / γ⌉₊ + 1), ?_⟩
  intro V _ E S Q hn hES hdeg hQS hQC hQdisj hQcard
  have hn2n₁ : 2 * n₁ ≤ S.card := le_trans (le_max_left _ _) hn
  have hnbig : ⌈4 * ((D : ℝ) + 2 * M) / γ⌉₊ + 1 ≤ S.card := le_trans (le_max_right _ _) hn
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := by omega
    exact_mod_cast this
  have hSlarge : 4 * ((D : ℝ) + 2 * M) / γ ≤ (S.card : ℝ) := by
    have h1 : 4 * ((D : ℝ) + 2 * M) / γ ≤ (⌈4 * ((D : ℝ) + 2 * M) / γ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈4 * ((D : ℝ) + 2 * M) / γ⌉₊ : ℕ) : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast le_trans (Nat.le_succ _) hnbig
    linarith
  have hDM : (D : ℝ) + 2 * M ≤ γ * (S.card : ℝ) / 4 := by
    rw [div_le_iff₀ hγ0] at hSlarge
    linarith
  -- the induction over the cells
  have key : ∀ Q : Finset (Finset V), (∀ P ∈ Q, P ⊆ S) → (∀ P ∈ Q, P.card ≤ C) →
      (∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint P P') → ((Q.card : ℝ) ≤ ρ * (S.card : ℝ)) →
      ∃ R : Finset V → Finset (Sym2 V),
        (∀ P ∈ Q, R P ⊆ E) ∧ (∀ P ∈ Q, CoreAbsorbers P (R P)) ∧
        (∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint (R P) (R P')) ∧
        (Q.biUnion R).card ≤ Q.card * M ∧
        (∀ v : V, v ∉ Q.biUnion id → edeg (Q.biUnion R) v ≤ D + M) ∧
        (∀ v : V, edeg (Q.biUnion R) v ≤ D + 2 * M) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty => exact fun _ _ _ _ => ⟨fun _ => ∅, by simp, by simp, by simp, by simp, by simp,
        by simp⟩
    | @insert P Q hPQ ih =>
      intro hQS hQC hQdisj hQcard
      have hQS' : ∀ X ∈ Q, X ⊆ S := fun X hX => hQS X (Finset.mem_insert_of_mem hX)
      have hQC' : ∀ X ∈ Q, X.card ≤ C := fun X hX => hQC X (Finset.mem_insert_of_mem hX)
      have hQdisj' : ∀ X ∈ Q, ∀ Y ∈ Q, X ≠ Y → Disjoint X Y := fun X hX Y hY =>
        hQdisj X (Finset.mem_insert_of_mem hX) Y (Finset.mem_insert_of_mem hY)
      have hcardle : (Q.card : ℝ) ≤ ((insert P Q).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.subset_insert _ _)
      obtain ⟨R, hRE, hRabs, hRdisj, hRcard, hRlow, hRhigh⟩ :=
        ih hQS' hQC' hQdisj' (le_trans hcardle hQcard)
      set A : Finset (Sym2 V) := Q.biUnion R with hAdef
      have hAE : A ⊆ E := Finset.biUnion_subset.2 hRE
      have hAS : A ⊆ cliqueEdges S := hAE.trans hES
      -- the vertices already carrying many reserved edges
      set Z : Finset V := S.filter (fun v => ¬ edeg A v ≤ D) with hZdef
      have hZcard : Z.card ≤ 2 * A.card / (D + 1) := card_high_deg_le A S D
      have hAcardR : (A.card : ℝ) ≤ ρ * (S.card : ℝ) * M := by
        have h1 : (A.card : ℝ) ≤ ((Q.card * M : ℕ) : ℝ) := by exact_mod_cast hRcard
        have h2 : ((Q.card * M : ℕ) : ℝ) = (Q.card : ℝ) * (M : ℝ) := by push_cast; ring
        have h3 : (Q.card : ℝ) * (M : ℝ) ≤ ρ * (S.card : ℝ) * (M : ℝ) := by
          have := le_trans hcardle hQcard
          exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
        linarith [h1, h2 ▸ h1]
      have hZsmall : (Z.card : ℝ) ≤ γ * (S.card : ℝ) := by
        have h1 : ((Z.card : ℕ) : ℝ) ≤ ((2 * A.card / (D + 1) : ℕ) : ℝ) := by exact_mod_cast hZcard
        have h2 : ((2 * A.card / (D + 1) : ℕ) : ℝ) ≤ (2 * A.card : ℝ) / ((D : ℝ) + 1) := by
          have := Nat.cast_div_le (α := ℝ) (m := 2 * A.card) (n := D + 1)
          push_cast at this ⊢
          linarith
        have hD1 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
        have h3 : (2 * A.card : ℝ) / ((D : ℝ) + 1) ≤ γ * (S.card : ℝ) := by
          rw [div_le_iff₀ hD1]
          have hDγ : 2 * ρ * (M : ℝ) ≤ γ * (D : ℝ) := by
            rw [div_le_iff₀ hγ0] at hD
            linarith
          have h5 : (S.card : ℝ) * (2 * ρ * (M : ℝ)) ≤ (S.card : ℝ) * (γ * (D : ℝ)) :=
            mul_le_mul_of_nonneg_left hDγ hSpos.le
          have h6 : (0 : ℝ) ≤ γ * (S.card : ℝ) := mul_nonneg hγ0.le hSpos.le
          nlinarith [hAcardR]
        linarith
      -- the restricted host
      set SP : Finset V := (S \ Z) ∪ P with hSPdef
      have hPS : P ⊆ S := hQS P (Finset.mem_insert_self _ _)
      have hSPS : SP ⊆ S := Finset.union_subset Finset.sdiff_subset hPS
      have hPSP : P ⊆ SP := Finset.subset_union_right
      have hSsubSP : S \ SP ⊆ Z := by
        intro v hv
        obtain ⟨hvS, hvSP⟩ := Finset.mem_sdiff.1 hv
        by_contra hvZ
        exact hvSP (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hvS, hvZ⟩))
      have hSPcardR : (S.card : ℝ) - γ * (S.card : ℝ) ≤ (SP.card : ℝ) := by
        have h1 : S.card ≤ SP.card + (S \ SP).card := by
          have := Finset.card_sdiff_add_card_eq_card hSPS
          omega
        have h2 : ((S \ SP).card : ℝ) ≤ (Z.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hSsubSP
        have h3 : (S.card : ℝ) ≤ (SP.card : ℝ) + ((S \ SP).card : ℝ) := by exact_mod_cast h1
        linarith
      have hSPhalf : (S.card : ℝ) / 2 ≤ (SP.card : ℝ) := by nlinarith
      have hSPn₁ : n₁ ≤ SP.card := by
        have h1 : (n₁ : ℝ) ≤ (S.card : ℝ) / 2 := by
          have : ((2 * n₁ : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hn2n₁
          push_cast at this; linarith
        have : (n₁ : ℝ) ≤ (SP.card : ℝ) := le_trans h1 hSPhalf
        exact_mod_cast this
      set EP : Finset (Sym2 V) := E ∩ cliqueEdges SP with hEPdef
      have hEPS : EP ⊆ cliqueEdges SP := Finset.inter_subset_right
      have hEPE : EP ⊆ E := Finset.inter_subset_left
      have hEPdeg : ∀ v ∈ SP, (9 / 10 + γ) * (SP.card : ℝ) ≤ (edeg EP v : ℝ) := by
        intro v hv
        have hvS : v ∈ S := hSPS hv
        have h1 : edeg E v ≤ edeg EP v + (S \ SP).card :=
          edeg_inter_cliqueEdges_ge hES hv
        have h2 : ((S \ SP).card : ℝ) ≤ (Z.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hSsubSP
        have h3 : (edeg E v : ℝ) ≤ (edeg EP v : ℝ) + ((S \ SP).card : ℝ) := by exact_mod_cast h1
        have h4 := hdeg v hvS
        have h5 : (SP.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hSPS
        nlinarith [hZsmall]
      set R₁ : Finset (Sym2 V) := A ∩ cliqueEdges SP with hR₁def
      have hR₁EP : R₁ ⊆ EP := by
        intro e he
        obtain ⟨heA, hecl⟩ := Finset.mem_inter.1 he
        exact Finset.mem_inter.2 ⟨hAE heA, hecl⟩
      have hR₁deg : ∀ v : V, (edeg R₁ v : ℝ) ≤ γ * (SP.card : ℝ) / 2 := by
        intro v
        have h1 : edeg R₁ v ≤ edeg A v := edeg_mono Finset.inter_subset_left v
        have h2 : (edeg A v : ℝ) ≤ (D : ℝ) + 2 * M := by
          have := hRhigh v
          have : (edeg A v : ℝ) ≤ ((D + 2 * M : ℕ) : ℝ) := by exact_mod_cast this
          push_cast at this; linarith
        have h3 : (edeg R₁ v : ℝ) ≤ (D : ℝ) + 2 * M := by
          have : (edeg R₁ v : ℝ) ≤ (edeg A v : ℝ) := by exact_mod_cast h1
          linarith
        have h4 : γ * ((S.card : ℝ) / 2) ≤ γ * (SP.card : ℝ) :=
          mul_le_mul_of_nonneg_left hSPhalf hγ0.le
        linarith [hDM]
      obtain ⟨RP, hRPsub, hRPcard, hRPabs⟩ :=
        hbase EP R₁ SP P hSPn₁ hEPS hPSP (hQC P (Finset.mem_insert_self _ _)) hEPdeg hR₁EP hR₁deg
      have hRPEP : RP ⊆ EP := fun e he => (Finset.mem_sdiff.1 (hRPsub he)).1
      have hRPE : RP ⊆ E := fun e he => hEPE (hRPEP he)
      have hRPcl : RP ⊆ cliqueEdges SP := fun e he => hEPS (hRPEP he)
      have hRPdisjA : Disjoint RP A := by
        refine Finset.disjoint_left.2 fun e he he' => ?_
        exact (Finset.mem_sdiff.1 (hRPsub he)).2
          (Finset.mem_inter.2 ⟨he', hRPcl he⟩)
      -- the updated family
      refine ⟨Function.update R P RP, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro X hX
        rcases Finset.mem_insert.1 hX with rfl | hX'
        · rw [Function.update_self]; exact hRPE
        · rw [Function.update_of_ne (by rintro rfl; exact hPQ hX')]; exact hRE X hX'
      · intro X hX
        rcases Finset.mem_insert.1 hX with rfl | hX'
        · rw [Function.update_self]; exact hRPabs
        · rw [Function.update_of_ne (by rintro rfl; exact hPQ hX')]; exact hRabs X hX'
      · have key2 : ∀ X ∈ Q, Disjoint RP (R X) := fun X hX =>
          Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem R hX) hRPdisjA
        intro X hX Y hY hne
        rcases Finset.mem_insert.1 hX with rfl | hX' <;>
          rcases Finset.mem_insert.1 hY with rfl | hY'
        · exact absurd rfl hne
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact hPQ hY')]
          exact key2 Y hY'
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact hPQ hX')]
          exact (key2 X hX').symm
        · rw [Function.update_of_ne (by rintro rfl; exact hPQ hX'),
            Function.update_of_ne (by rintro rfl; exact hPQ hY')]
          exact hRdisj X hX' Y hY' hne
      -- the union of the updated family
      all_goals
        have hunion : (insert P Q).biUnion (Function.update R P RP) = RP ∪ A := by
          rw [Finset.biUnion_insert, Function.update_self]
          congr 1
          refine Finset.biUnion_congr rfl fun X hX => ?_
          rw [Function.update_of_ne (by rintro rfl; exact hPQ hX)]
      · rw [hunion]
        have h1 : (RP ∪ A).card ≤ RP.card + A.card := Finset.card_union_le _ _
        have h2 : (insert P Q).card = Q.card + 1 := Finset.card_insert_of_notMem hPQ
        have h3 : RP.card + A.card ≤ M + Q.card * M := Nat.add_le_add hRPcard hRcard
        rw [h2]
        calc (RP ∪ A).card ≤ RP.card + A.card := h1
          _ ≤ M + Q.card * M := h3
          _ = (Q.card + 1) * M := by ring
      · intro v hv
        rw [hunion]
        have hvP : v ∉ P := fun hvP => hv (Finset.mem_biUnion.2 ⟨P, Finset.mem_insert_self _ _,
          hvP⟩)
        have hvQ : v ∉ Q.biUnion id := fun hvQ => by
          obtain ⟨X, hX, hvX⟩ := Finset.mem_biUnion.1 hvQ
          exact hv (Finset.mem_biUnion.2 ⟨X, Finset.mem_insert_of_mem hX, hvX⟩)
        have hAv : edeg A v ≤ D + M := hRlow v hvQ
        by_cases hvZ : v ∈ Z
        · have hvSP : v ∉ SP := by
            intro hvSP
            rcases Finset.mem_union.1 hvSP with h | h
            · exact (Finset.mem_sdiff.1 h).2 hvZ
            · exact hvP h
          have : edeg RP v = 0 := edeg_eq_zero_outside hRPcl hvSP
          have hle := edeg_union_le RP A v
          omega
        · have hvD : edeg A v ≤ D := by
            by_cases hvS : v ∈ S
            · by_contra hcon
              exact hvZ (Finset.mem_filter.2 ⟨hvS, hcon⟩)
            · have : edeg A v = 0 := edeg_eq_zero_outside hAS hvS
              omega
          have h1 : edeg RP v ≤ M := le_trans (Finset.card_filter_le _ _) hRPcard
          have hle := edeg_union_le RP A v
          omega
      · intro v
        rw [hunion]
        have hle := edeg_union_le RP A v
        have h1 : edeg RP v ≤ M := le_trans (Finset.card_filter_le _ _) hRPcard
        by_cases hvP : v ∈ P
        · have hvQ : v ∉ Q.biUnion id := by
            intro hvQ
            obtain ⟨X, hX, hvX⟩ := Finset.mem_biUnion.1 hvQ
            have hne : P ≠ X := by rintro rfl; exact hPQ hX
            exact (Finset.disjoint_left.1 (hQdisj P (Finset.mem_insert_self _ _) X
              (Finset.mem_insert_of_mem hX) hne) hvP) hvX
          have := hRlow v hvQ
          omega
        · by_cases hvZ : v ∈ Z
          · have hvSP : v ∉ SP := by
              intro hvSP
              rcases Finset.mem_union.1 hvSP with h | h
              · exact (Finset.mem_sdiff.1 h).2 hvZ
              · exact hvP h
            have h0 : edeg RP v = 0 := edeg_eq_zero_outside hRPcl hvSP
            have := hRhigh v
            omega
          · have hvD : edeg A v ≤ D := by
              by_cases hvS : v ∈ S
              · by_contra hcon
                exact hvZ (Finset.mem_filter.2 ⟨hvS, hcon⟩)
              · have : edeg A v = 0 := edeg_eq_zero_outside hAS hvS
                omega
            omega
  obtain ⟨R, h1, h2, h3, -, -, h6⟩ := key Q hQS hQC hQdisj hQcard
  exact ⟨R, h1, h2, h3, h6⟩

end BKLO
