import BoundedCliqueGap.JRelative
import BoundedCliqueGap.Transport

/-
`BoundedCliqueGap.LInterface` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung L0 — the interface Prop `ShellGapFull`, and transport of gap bounds
along an injection

A parallel lane of this project is attacking the last open local lemma, the
unconditional shell bound.  This lane **assumes** it, as a named `Prop` with an
explicit constant — never as an axiom:

```
ShellGapFull C  :=  ∀ κ t m (S₀ : Finset (Fin κ)) terr S (F : FracPacking (shell S₀ terr S)),
                      F.value ≤ ν₃(shell S₀ terr S) + C · ((κ − |S₀|) + t)
```

Everything downstream takes `ShellGapFull C` as a hypothesis.

This file also builds the transport tool that the assembly needs.  A shell
occurring inside a big graph `G` lives on a *subset* of `G`'s vertices, so the
isomorphism transport of `BoundedCliqueGap/Transport.lean` (which needs a bijection of
the whole vertex types) is not enough.  `gap_transfer_embed` transports a gap
bound along an **injection** `f : V → W` under which `H` is exactly the
`f`-image of `G` and all edges of `H` live in the image; the technical device
is `FracPacking.pull`, the pullback of a fractional packing along `f`, whose
value is unchanged (`FracPacking.value_pull`).

Finally, `shell_gap_rel_full` is the conditional relative form asked for by the
rung: with a prescribed set `R` of reserved edge slots, the cross-mass residual
of `shell_gap_rel` is replaced by the `ShellGapFull` term, the reservation
still being charged at exactly `1` per reserved edge.
-/

namespace BoundedCliqueGap

open Finset

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## Two small tools -/

/-! ## Pulling a fractional packing back along an injection -/

section Pullback

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- **Pullback of a fractional packing along an injection.**  If `f : V → W` is
injective and `G` is exactly the `f`-preimage of `H`, then every fractional
packing of `H` restricts to one of `G`. -/
noncomputable def FracPacking.pull (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ a b, H.Adj (f a) (f b) ↔ G.Adj a b) (F : FracPacking H) :
    FracPacking G where
  x := fun T => F.x (T.image f)
  nonneg := fun _ => F.nonneg _
  supp := by
    intro T hT
    have h := F.supp _ hT
    refine ⟨?_, ?_⟩
    · have hc := h.1
      rwa [Finset.card_image_of_injective _ hf] at hc
    · intro u hu v hv huv
      exact (hadj u v).1 (h.2 (f u) (Finset.mem_image_of_mem f hu) (f v)
        (Finset.mem_image_of_mem f hv) (fun hc => huv (hf hc)))
  edge_le_one := by
    classical
    intro e he
    induction e with
    | _ a b =>
      have hne : a ≠ b := by
        simpa [Sym2.isDiag_iff_proj_eq] using he
      have hfne : ¬ (s(f a, f b) : Sym2 W).IsDiag := by
        simp only [Sym2.isDiag_iff_proj_eq]
        exact fun hc => hne (hf hc)
      have hbase := F.edge_le_one _ hfne
      set A : Finset (Finset V) :=
        Finset.univ.filter (fun T => s(a, b) ∈ triEdges T ∧ F.x (T.image f) ≠ 0) with hA
      have hinj : ∀ T ∈ A, ∀ T' ∈ A, T.image f = T'.image f → T = T' :=
        fun T _ T' _ h => Finset.image_injective hf h
      show ∑ T ∈ A, F.x (T.image f) ≤ 1
      rw [← Finset.sum_image hinj]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => F.nonneg i)) hbase
      intro U hU
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hU
      rw [hA] at hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      obtain ⟨haT, hbT, -⟩ := mk_mem_triEdges_iff.1 hT.1
      exact ⟨mk_mem_triEdges_iff.2 ⟨Finset.mem_image_of_mem f haT,
        Finset.mem_image_of_mem f hbT, fun hc => hne (hf hc)⟩, hT.2⟩

omit [Fintype W] in
/-- Every vertex of a triangle of `H` is an endpoint of an edge of `H`. -/
lemma exists_adj_of_mem_triangle {T : Finset W} (hT : IsTriangle H T) {u : W} (hu : u ∈ T) :
    ∃ v ∈ T, H.Adj u v := by
  have h1 : 1 < T.card := by rw [hT.1]; norm_num
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 h1
  by_cases hup : u = p
  · exact ⟨q, hq, hT.2 u hu q hq (by rw [hup]; exact hpq)⟩
  · exact ⟨p, hp, hT.2 u hu p hp hup⟩

/-- **The pullback has the same value**, provided every edge of `H` lives in
the image of `f`. -/
lemma FracPacking.value_pull (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ a b, H.Adj (f a) (f b) ↔ G.Adj a b)
    (hsupp : ∀ u v, H.Adj u v → ∃ a, f a = u) (F : FracPacking H) :
    (F.pull f hf hadj).value = F.value := by
  classical
  -- every triangle of `H` is the image of a (unique) finset of `V`
  have himg : ∀ U : Finset W, IsTriangle H U →
      (Finset.univ.filter (fun a : V => f a ∈ U)).image f = U := by
    intro U hU
    ext u
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hu
      obtain ⟨v, -, hadjuv⟩ := exists_adj_of_mem_triangle hU hu
      obtain ⟨a, rfl⟩ := hsupp _ _ hadjuv
      exact ⟨a, hu, rfl⟩
  refine Finset.sum_nbij (i := fun T : Finset V => T.image f) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    exact hT
  · intro T _ T' _ h
    exact Finset.image_injective hf h
  · intro U hU
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
      Set.mem_image] at hU ⊢
    refine ⟨Finset.univ.filter (fun a : V => f a ∈ U), ?_, ?_⟩
    · show (F.pull f hf hadj).x _ ≠ 0
      show F.x _ ≠ 0
      rw [himg U (F.supp U hU)]
      exact hU
    · exact himg U (F.supp U hU)
  · intro T _
    rfl

/-- **Transport of a gap bound along an injection.**  If `G` embeds into `H` as
its full `f`-image, and every edge of `H` lies inside that image, then a gap
bound for `G` gives the same gap bound for `H`. -/
theorem gap_transfer_embed (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ a b, H.Adj (f a) (f b) ↔ G.Adj a b)
    (hsupp : ∀ u v, H.Adj u v → ∃ a, f a = u) (c : ℚ)
    (h : ∀ F : FracPacking G, F.value ≤ (nu3 G : ℚ) + c) (F : FracPacking H) :
    F.value ≤ (nu3 H : ℚ) + c := by
  have hpull := h (F.pull f hf hadj)
  rw [FracPacking.value_pull f hf hadj hsupp] at hpull
  have hnu : (nu3 G : ℚ) ≤ (nu3 H : ℚ) := by
    exact_mod_cast nu3_le_of_embedding ⟨f, hf⟩ (fun u v huv => (hadj u v).2 huv)
  linarith

end Pullback

/-! ## The interface Prop -/

namespace LIface

/-- **The interface Prop of the L-ladder.**  `ShellGapFull C` says that every
shell — any hub size `κ`, any hole `S₀`, any territory structure `terr` with
any separators `S`, any number `t` of ports — has integrality gap at most
`C · ((κ − |S₀|) + t)`, i.e. linear in the shell's *own* charge: the hub
vertices introduced at the shell plus its ports.

This is the statement the parallel lane is proving.  Here it is only ever a
named hypothesis.

It lives in the auxiliary namespace `LIface` and is `export`ed back under its
plain name, so that every L-lane file keeps using it unqualified while a file
that also imports the K-lane's homonymous (sum-form) `ShellGapFull` can still
disambiguate it as `LIface.ShellGapFull`. -/
def ShellGapFull (C : ℚ) : Prop :=
  ∀ (kappa t m : ℕ) (S0 : Finset (Fin kappa)) (terr : Fin t → Fin m)
    (S : Fin m → Finset (Fin kappa)) (F : FracPacking (shell S0 terr S)),
    F.value ≤ (nu3 (shell S0 terr S) : ℚ) + C * (((kappa - S0.card : ℕ) : ℚ) + (t : ℚ))

/-- **The relative form, conditionally.**  With a prescribed set `R` of
reserved edge slots the integral packing on the right avoids `R`, at a cost of
exactly `1` per reserved edge, and the cross-mass residual of `shell_gap_rel`
is replaced by the `ShellGapFull` term. -/
theorem shell_gap_rel_full {C : ℚ} (hC : ShellGapFull C) {kappa t m : ℕ}
    (S0 : Finset (Fin kappa)) (terr : Fin t → Fin m) (S : Fin m → Finset (Fin kappa))
    (R : Finset (Sym2 (Fin kappa ⊕ Fin t))) (F : FracPacking (shell S0 terr S)) :
    F.value ≤ (nu3 ((shell S0 terr S).deleteEdges ↑R) : ℚ) + (R.card : ℚ)
      + C * (((kappa - S0.card : ℕ) : ℚ) + (t : ℚ)) := by
  have h := hC kappa t m S0 terr S F
  have hdel : (nu3 (shell S0 terr S) : ℚ)
      ≤ (nu3 ((shell S0 terr S).deleteEdges ↑R) : ℚ) + (R.card : ℚ) := by
    exact_mod_cast nu3_le_nu3_deleteEdges_add_card (shell S0 terr S) R
  linarith

end LIface

export LIface (ShellGapFull shell_gap_rel_full)

/-! ## Axiom audit -/

end BoundedCliqueGap
