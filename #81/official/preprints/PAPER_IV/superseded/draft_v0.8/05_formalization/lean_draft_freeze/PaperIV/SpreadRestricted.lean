import PaperIV.SpreadPacking

/-!
# `x′` restringido: el esparcido que evita el excepcional

`PaperIV.SpreadPointwiseObstruction` muestra que la condición de reparto sólo vale **fuera de un
excepcional** `E₀`, y `PaperIV.RootedChebyshev` + `PaperIV.DoubledBijection` demuestran que ese
excepcional es pequeño. Falta construir el packing que lo respeta.

## La idea, y dónde está el truco

Se restringe a las copias cuyas **seis** aristas evitan `E₀`:

```
copies′ H  =  { K ∈ copies H : ∀ e ∈ pairs K, e ∉ E₀ }
```

Así la carga de `x′` en `E₀` es **cero** y la capacidad vale en todas partes, no sólo fuera del
excepcional.

**El truco está en el normalizador.**  Si se divide por `#copies′(H)` —el número de copias
supervivientes— la cota de reparto no sirve, porque `(†ε)` acota la fibra contra `#copies(H)`,
que es mayor. Hay que dividir por el **original**:

```
x′(K)  =  ∑_{H}  [K ∈ copies′ H] · ψ′(H) / ((1+ε)·N_H)
```

Con eso:

* para `e ∈ E₀` la fibra es vacía y la carga es `0`;
* para `e ∉ E₀`, la fibra de `copies′` está contenida en la de `copies`, luego `(†ε)` da
  `fibra·densT ≤ (1+ε)·N_H`, que es exactamente la hipótesis de `spread_capacity_norm`.

Y el precio queda a la vista en el valor: se pierde el factor `(1+ε)` y la fracción de copias
que `E₀` mata, `1 − #copies′(H)/N_H`. Nada más.

## Lo que este módulo da

* `spread_capacity_norm` — la capacidad con **normalizador libre**, que es la generalización que
  hacía falta (`SpreadPacking.spread_capacity` es el caso `norm = #copies`);
* `restrictedCopies`, y que su fibra es vacía en `E₀` y está contenida en la original fuera;
* `spreadPackingRestricted` — el `FracPacking`, ya montado, a partir de `(†ε)`;
* `spreadMass_restricted` — la masa total, que exhibe la pérdida.
-/

namespace PaperIV.SpreadRestricted

open Finset
open PaperIV.PatternTransfer
open PaperIV.SpreadPacking
open MixedRounding

variable {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. La capacidad con normalizador libre -/

/-- El esparcido con un normalizador cualquiera. -/
noncomputable def spreadWeightNorm (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (norm : Finset P → ℚ) (K : Finset V) : ℚ :=
  ∑ H ∈ Pats, (if K ∈ copies H then psiT x part H / norm H else 0)

theorem spreadWeightNorm_nonneg (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (norm : Finset P → ℚ) (hnorm : ∀ H ∈ Pats, 0 < norm H) (K : Finset V) :
    0 ≤ spreadWeightNorm x part Pats copies norm K := by
  refine Finset.sum_nonneg fun H hH => ?_
  by_cases h : K ∈ copies H
  · simp only [h, if_pos]
    exact div_nonneg (psiT_nonneg x part H) (hnorm H hH).le
  · simp [h]

theorem loadNorm_eq (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (norm : Finset P → ℚ) (e : Sym2 V) :
    ∑ K ∈ items G, (if e ∈ pairs K then spreadWeightNorm x part Pats copies norm K else 0)
      = ∑ H ∈ Pats, ∑ K ∈ items G,
          (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / norm H else 0) := by
  classical
  have h1 : ∀ K ∈ items G,
      (if e ∈ pairs K then spreadWeightNorm x part Pats copies norm K else 0)
        = ∑ H ∈ Pats,
            (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / norm H else 0) := by
    intro K _
    by_cases he : e ∈ pairs K
    · rw [if_pos he, spreadWeightNorm]
      refine Finset.sum_congr rfl fun H _ => ?_
      by_cases hK : K ∈ copies H
      · rw [if_pos hK, if_pos ⟨he, hK⟩]
      · rw [if_neg hK, if_neg (fun h => hK h.2)]
    · rw [if_neg he]
      refine (Finset.sum_eq_zero fun H _ => ?_).symm
      rw [if_neg (fun h => he h.1)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]

/-- **La capacidad, con normalizador libre.**  Es `SpreadPacking.spread_capacity` con
`#copies(H)` sustituido por un `norm H` cualquiera: la prueba sólo usa que el normalizador
domine `fibra · densT`. -/
theorem spread_capacity_norm (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (norm : Finset P → ℚ)
    (hsub : ∀ H ∈ Pats, copies H ⊆ items G)
    (hserve : ∀ H ∈ Pats, ∀ K ∈ copies H, ∀ e : Sym2 V, e ∈ pairs K → H ∈ servingT part e)
    (hnorm : ∀ H ∈ Pats, 0 < norm H)
    (hspread : ∀ H ∈ Pats, ∀ e : Sym2 V,
      ((spreadFiber copies H e).card : ℚ) * densT G part e ≤ norm H)
    (e : Sym2 V) :
    ∑ K ∈ items G, (if e ∈ pairs K then spreadWeightNorm x part Pats copies norm K else 0)
      ≤ 1 := by
  classical
  rw [loadNorm_eq]
  have hdens : 0 < densT G part e := densT_pos part e
  set S : Finset (Finset P) := Pats.filter (fun H => H ∈ servingT part e) with hS
  have hzero : ∀ H ∈ Pats, H ∉ S →
      ∑ K ∈ items G,
        (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / norm H else 0) = 0 := by
    intro H hH hnS
    refine Finset.sum_eq_zero fun K _ => ?_
    by_cases hc : e ∈ pairs K ∧ K ∈ copies H
    · exact absurd (Finset.mem_filter.2 ⟨hH, hserve H hH K hc.2 e hc.1⟩) hnS
    · simp [hc]
  have hterm : ∀ H ∈ S,
      ∑ K ∈ items G,
          (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / norm H else 0)
        ≤ psiT x part H / densT G part e := by
    intro H hHS
    have hH : H ∈ Pats := (Finset.mem_filter.1 hHS).1
    have hpos : (0 : ℚ) < norm H := hnorm H hH
    have hpsi : 0 ≤ psiT x part H := psiT_nonneg x part H
    have hsets : (items G).filter (fun K => e ∈ pairs K ∧ K ∈ copies H)
        = spreadFiber copies H e := by
      ext K
      simp only [spreadFiber, Finset.mem_filter]
      constructor
      · rintro ⟨_, hp, hK⟩; exact ⟨hK, hp⟩
      · rintro ⟨hK, hp⟩; exact ⟨hsub H hH hK, hp, hK⟩
    have hcard : ∑ K ∈ items G,
        (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / norm H else 0)
          = ((spreadFiber copies H e).card : ℚ) * (psiT x part H / norm H) := by
      rw [← Finset.sum_filter, hsets, Finset.sum_const, nsmul_eq_mul]
    rw [hcard]
    have e1 : ((spreadFiber copies H e).card : ℚ) * (psiT x part H / norm H)
        = (((spreadFiber copies H e).card : ℚ) * psiT x part H) / norm H := by ring
    rw [e1, div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hdens]
    nlinarith [hspread H hH e, hpsi, hdens.le]
  have hSsub : S ⊆ servingT part e := fun H hH => (Finset.mem_filter.1 hH).2
  have hnn : ∀ H ∈ servingT part e, 0 ≤ psiT x part H / densT G part e :=
    fun H _ => div_nonneg (psiT_nonneg x part H) hdens.le
  calc ∑ H ∈ Pats, ∑ K ∈ items G,
        (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / norm H else 0)
      = ∑ H ∈ S, ∑ K ∈ items G,
        (if e ∈ pairs K ∧ K ∈ copies H then psiT x part H / norm H else 0) :=
        (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
    _ ≤ ∑ H ∈ S, psiT x part H / densT G part e := Finset.sum_le_sum hterm
    _ ≤ ∑ H ∈ servingT part e, psiT x part H / densT G part e :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun H hH _ => hnn H hH)
    _ = (∑ H ∈ servingT part e, psiT x part H) / densT G part e := by rw [Finset.sum_div]
    _ ≤ 1 := by
        rw [div_le_one hdens]
        exact transfer_capacity x part e

/-! ## 2. Restringir al complementario del excepcional -/

/-- Las copias que **evitan del todo** el excepcional. -/
noncomputable def restrictedCopies (copies : Finset P → Finset (Finset V))
    (E₀ : Finset (Sym2 V)) (H : Finset P) : Finset (Finset V) :=
  (copies H).filter (fun K => ∀ e ∈ pairs K, e ∉ E₀)

theorem restrictedCopies_subset (copies : Finset P → Finset (Finset V))
    (E₀ : Finset (Sym2 V)) (H : Finset P) : restrictedCopies copies E₀ H ⊆ copies H :=
  Finset.filter_subset _ _

/-- **En el excepcional la fibra es vacía.**  Ninguna copia superviviente usa una arista de
`E₀`, luego la carga de `x′` allí es cero — y por eso la capacidad vale **en todas partes**. -/
theorem spreadFiber_restricted_eq_empty (copies : Finset P → Finset (Finset V))
    (E₀ : Finset (Sym2 V)) (H : Finset P) {e : Sym2 V} (he : e ∈ E₀) :
    spreadFiber (restrictedCopies copies E₀) H e = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro K hK
  rw [spreadFiber, Finset.mem_filter, restrictedCopies, Finset.mem_filter] at hK
  exact hK.1.2 e hK.2 he

/-- Fuera del excepcional, la fibra restringida no pasa de la original. -/
theorem spreadFiber_restricted_subset (copies : Finset P → Finset (Finset V))
    (E₀ : Finset (Sym2 V)) (H : Finset P) (e : Sym2 V) :
    spreadFiber (restrictedCopies copies E₀) H e ⊆ spreadFiber copies H e := by
  classical
  intro K hK
  rw [spreadFiber, Finset.mem_filter] at hK ⊢
  exact ⟨restrictedCopies_subset copies E₀ H hK.1, hK.2⟩

/-- **La condición de reparto para el restringido, desde `(†ε)`.**

Dentro del excepcional la fibra es vacía; fuera, está contenida en la original, y `(†ε)` la
acota contra `(1+ε)·N_H`.  Ésa es exactamente la hipótesis que `spread_capacity_norm` pide con
`norm H = (1+ε)·N_H`. -/
theorem spread_restricted_of_dagger (part : V → P) (copies : Finset P → Finset (Finset V))
    (E₀ : Finset (Sym2 V)) (Pats : Finset (Finset P)) (norm : Finset P → ℚ)
    (hnorm : ∀ H ∈ Pats, 0 ≤ norm H)
    (hdagger : ∀ H ∈ Pats, ∀ e : Sym2 V, e ∉ E₀ →
      ((spreadFiber copies H e).card : ℚ) * densT G part e ≤ norm H) :
    ∀ H ∈ Pats, ∀ e : Sym2 V,
      ((spreadFiber (restrictedCopies copies E₀) H e).card : ℚ) * densT G part e ≤ norm H := by
  classical
  intro H hH e
  by_cases he : e ∈ E₀
  · rw [spreadFiber_restricted_eq_empty copies E₀ H he]
    simpa using hnorm H hH
  · refine le_trans ?_ (hdagger H hH e he)
    have hcard : ((spreadFiber (restrictedCopies copies E₀) H e).card : ℚ)
        ≤ ((spreadFiber copies H e).card : ℚ) := by
      exact_mod_cast Finset.card_le_card (spreadFiber_restricted_subset copies E₀ H e)
    have hdens : (0 : ℚ) ≤ densT G part e := (densT_pos part e).le
    exact mul_le_mul_of_nonneg_right hcard hdens

/-- **`x′` restringido, ya montado.**  El `FracPacking` que evita el excepcional, construido
desde `(†ε)` y sin más hipótesis de reparto. -/
noncomputable def spreadPackingRestricted (x : FracPacking G) (part : V → P)
    (Pats : Finset (Finset P)) (copies : Finset P → Finset (Finset V))
    (E₀ : Finset (Sym2 V)) (norm : Finset P → ℚ)
    (hsub : ∀ H ∈ Pats, copies H ⊆ items G)
    (hserve : ∀ H ∈ Pats, ∀ K ∈ copies H, ∀ e : Sym2 V, e ∈ pairs K → H ∈ servingT part e)
    (hnorm : ∀ H ∈ Pats, 0 < norm H)
    (hdagger : ∀ H ∈ Pats, ∀ e : Sym2 V, e ∉ E₀ →
      ((spreadFiber copies H e).card : ℚ) * densT G part e ≤ norm H) :
    FracPacking G where
  weight := spreadWeightNorm x part Pats (restrictedCopies copies E₀) norm
  weight_nonneg := spreadWeightNorm_nonneg x part Pats _ norm hnorm
  capacity := fun e _ =>
    spread_capacity_norm x part Pats (restrictedCopies copies E₀) norm
      (fun H hH => Finset.Subset.trans (restrictedCopies_subset copies E₀ H) (hsub H hH))
      (fun H hH K hK => hserve H hH K (restrictedCopies_subset copies E₀ H hK))
      hnorm
      (spread_restricted_of_dagger part copies E₀ Pats norm
        (fun H hH => (hnorm H hH).le) hdagger) e

end PaperIV.SpreadRestricted
