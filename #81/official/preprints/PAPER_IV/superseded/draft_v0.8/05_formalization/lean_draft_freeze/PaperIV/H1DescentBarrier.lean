import PaperIV.PathDescentBarrier
import PaperIV.GraphFamilyDistance
import PaperIV.SymmetrizationMetricStep

/-!
# Sustituto de descenso para la primera entrada de la ruta H1

La ruta H1 —la rama cercana, que es la que sigue abierta— **sí usa primera entrada**. Su cadena
es, según `docs/H1_FIRST_ENTRY_ROUTE_AUDIT_20260918.md`:

```text
constructor local físico → contracción local en la vecindad split crítica
→ camino fino cordal con F4 no decreciente → terminal split cercano
→ PRIMERA ENTRADA: el grafo original ya estaba en la vecindad
→ aplicar el constructor una sola vez al grafo original
```

Ese paso está hoy en Lean como `SymmetrizationBarrier.barrier_of_symmetrizationPath_invariant` y su
empaquetado `graphFamDistNorm_barrier_of_terminal_symmetrizationPath`. Es exactamente el mecanismo que la
demostración publicada usa, y por tanto el punto donde nuestra cadena dejaría de ser independiente
de ella en cuanto la rama cercana cierre.

Este módulo entrega el **sustituto de descenso** para esos tres teoremas: mismos enunciados, misma
forma de consumo, propagación por descenso sobre el camino en vez de por índice mínimo.

## Qué cambia exactamente

| | primera entrada | descenso |
|---|---|---|
| dónde contrae | en el **sucesor** | en el **punto actual** |
| relación radios | `barrier ≤ outer` | `barrier + stepBudget ≤ outer` |
| hueco | `contracted + stepBudget < barrier` | `contracted ≤ barrier` |
| cordalidad del origen | no hace falta | **hace falta** (se contrae también en `G`) |

Los dos juegos de hipótesis escalares son incomparables
(`PathDescentBarrier.hypotheses_incomparable`). `canonical_radii` cierra la brecha para la ruta:
con los radios anidados `(ρ, ρ/2, ρ/4)` y un paso `< ρ/4` **se cumplen los dos**, así que H1 puede
elegir mecanismo sin tocar sus números. La cordalidad del origen H1 la tiene de entrada.

## Lo que esto no es

No cierra la rama cercana. El constructor local físico y S01–S03 siguen abiertos, y sin ellos no
hay contracción local que alimentar a ningún mecanismo. Lo que este módulo garantiza es que,
cuando se cierren, el ensamblaje final **no está obligado** a pasar por primera entrada.
-/

namespace PaperIV.H1DescentBarrier

open PaperIV.VertexCopyGate
open PaperIV.EditMetric
open PaperIV.GraphFamilyDistance
open PaperIV.PathDescentBarrier
open PaperIV.SymmetrizationMetricStep

/-! ## 1. Los radios anidados sirven para los dos mecanismos -/

/-- **Con radios anidados, los dos juegos de hipótesis se cumplen a la vez.**

`(outer, barrier, contracted) = (ρ, ρ/2, ρ/4)` y `stepBudget < ρ/4`. A la izquierda lo que pide
la primera entrada, a la derecha lo que pide el descenso. Es la condición bajo la cual el cambio
de mecanismo en H1 es literal: no hay que recalcular ninguna constante. -/
theorem canonical_radii {rho step : ℚ} (hrho : 0 < rho) (_hstep : 0 ≤ step)
    (hsmall : step < rho / 4) :
    (rho / 2 ≤ rho ∧ rho / 4 + step < rho / 2) ∧
      (rho / 2 + step ≤ rho ∧ rho / 4 ≤ rho / 2) := by
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **La misma condición, en la escala de H1.** El presupuesto de paso de la distancia de
edición normalizada es `1/n`, así que basta `4/ρ < n`. -/
theorem canonical_radii_of_card {rho n : ℚ} (hrho : 0 < rho) (hn : 0 < n)
    (hlarge : 4 / rho < n) :
    (rho / 2 ≤ rho ∧ rho / 4 + 1 / n < rho / 2) ∧
      (rho / 2 + 1 / n ≤ rho ∧ rho / 4 ≤ rho / 2) := by
  have h4 : (4 : ℚ) < n * rho := by
    have h := mul_lt_mul_of_pos_right hlarge hrho
    have e : 4 / rho * rho = 4 := by field_simp
    linarith
  have hx : (0 : ℚ) < 1 / n := by positivity
  have hmul := mul_lt_mul_of_pos_left h4 hx
  have heq : 1 / n * (n * rho) = rho := by field_simp
  rw [heq] at hmul
  have hsmall : 1 / n < rho / 4 := by linarith
  exact canonical_radii hrho (by positivity) hsmall

/-! ## 2. Cadena monótona sobre un índice natural -/

/-- Monotonía puntual implica monotonía en la cadena: lo que convierte el campo `hF4` de cada
paso guardado en el invariante de dos lados que H1 consume. -/
theorem mono_chain {α : Type*} [Preorder α] {f : ℕ → α} {L : ℕ} (h : ∀ i : ℕ, i < L → f i ≤ f (i + 1)) :
    ∀ i j : ℕ, i ≤ j → j ≤ L → f i ≤ f j := by
  intro i j hij hjL
  induction j with
  | zero =>
      have : i = 0 := Nat.le_zero.1 hij
      subst this
      exact le_rfl
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hij' : i ≤ j := Nat.lt_succ_iff.1 hlt
        exact (ih hij' (by omega)).trans (h j (by omega))
      · have : i = j + 1 := le_antisymm hij hge
        subst this
        exact le_rfl

/-! ## 3. El puente completo -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Todo testigo de `SymmetrizationPath` es un camino con sus tres datos.**

Extrae de la relación inductiva la sucesión, la cordalidad en cada índice, la monotonía de `F4'`
paso a paso y el testigo de copia fina de cada paso. Con `mono_chain`, la tercera componente da
el invariante `F4' G ≤ F4' (seq i) ≤ F4' H` que la contracción local de H1 puede asumir.

Es el único punto de esta ruta que induce sobre `SymmetrizationPath`. -/
theorem symmetrizationPath_toSeqFull {G H : SimpleGraph V} (h : SymmetrizationPath G H) :
    PaperIV.IsChordal G →
    ∃ (L : ℕ) (seq : ℕ → SimpleGraph V),
      seq 0 = G ∧ seq L = H ∧
      (∀ i : ℕ, i ≤ L → PaperIV.IsChordal (seq i)) ∧
      (∀ i : ℕ, i < L → F4' (seq i) ≤ F4' (seq (i + 1))) ∧
      ∀ i : ℕ, i < L → ∃ t s : V, t ≠ s ∧ ¬ (seq i).Adj t s ∧
        seq (i + 1) = PaperIV.VertexCopy.graph (seq i) t s := by
  induction h with
  | refl G =>
      intro hG
      exact ⟨0, fun _ => G, rfl, rfl, fun _ _ => hG, fun i hi => absurd hi (by omega),
        fun i hi => absurd hi (by omega)⟩
  | @step G H t s hne hnadj _ hchord hF4 _ htail ih =>
      intro hG
      obtain ⟨L, seq, h0, hL, hchordseq, hmono, hstep⟩ := ih hchord
      refine ⟨L + 1, fun i => if i = 0 then G else seq (i - 1), rfl, ?_, ?_, ?_, ?_⟩
      · simp only [if_neg (Nat.succ_ne_zero L)]
        simpa using hL
      · intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simpa using hG
        · have hi0 : i ≠ 0 := Nat.pos_iff_ne_zero.1 hpos
          simp only [if_neg hi0]
          exact hchordseq (i - 1) (by omega)
      · intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simp only [if_pos rfl, if_neg one_ne_zero]
          have hrw : (1 : ℕ) - 1 = 0 := rfl
          rw [hrw, h0]
          exact hF4
        · have hi0 : i ≠ 0 := Nat.pos_iff_ne_zero.1 hpos
          have hi1 : i + 1 ≠ 0 := Nat.succ_ne_zero i
          simp only [if_neg hi0, if_neg hi1]
          have hshift : i + 1 - 1 = (i - 1) + 1 := by omega
          rw [hshift]
          exact hmono (i - 1) (by omega)
      · intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · refine ⟨t, s, hne, hnadj, ?_⟩
          simp only [if_pos rfl, if_neg one_ne_zero]
          simpa using h0
        · have hi0 : i ≠ 0 := Nat.pos_iff_ne_zero.1 hpos
          have hi1 : i + 1 ≠ 0 := Nat.succ_ne_zero i
          obtain ⟨t', s', hne', hnadj', heq'⟩ := hstep (i - 1) (by omega)
          refine ⟨t', s', hne', ?_, ?_⟩
          · simpa only [if_neg hi0] using hnadj'
          · simp only [if_neg hi0, if_neg hi1]
            have hshift : i + 1 - 1 = (i - 1) + 1 := by omega
            rw [hshift]
            exact heq'

/-! ## 4. El sustituto: la barrera con invariante, por descenso -/

/-- **Sustituto de descenso para `barrier_of_symmetrizationPath_invariant`.**

Mismo enunciado y mismo invariante `F4' G ≤ F4' X ≤ F4' H` disponible en la contracción local.
Dos diferencias, ambas explícitas: las hipótesis escalares son las del descenso, y hace falta
`IsChordal G` porque el mecanismo contrae también en el origen.

En la ruta H1 las dos se cumplen: `G` es cordal por hipótesis y `canonical_radii` cubre los
radios. -/
theorem barrier_of_symmetrizationPath_invariant_descent
    (distance : SimpleGraph V → ℚ)
    {outer barrier contracted stepBudget : ℚ}
    (houter : barrier + stepBudget ≤ outer)
    (hcb : contracted ≤ barrier)
    (hstep : ∀ (X : SimpleGraph V) {target source : V},
      target ≠ source → ¬ X.Adj target source →
      distance X - distance (PaperIV.VertexCopy.graph X target source) ≤ stepBudget)
    {G H : SimpleGraph V}
    (hG : PaperIV.IsChordal G)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      distance X < outer → distance X < contracted)
    (hreach : SymmetrizationPath G H)
    (hend : distance H < barrier) :
    distance G < barrier := by
  obtain ⟨L, seq, h0, hL, hchordseq, hmono, hsteps⟩ := symmetrizationPath_toSeqFull hreach hG
  have hchain := mono_chain (f := fun i => F4' (seq i)) hmono
  have hmove : ∀ i : ℕ, i < L →
      distance (seq i) - stepBudget ≤ distance (seq (i + 1)) := by
    intro i hi
    obtain ⟨t, s, hne, hnadj, heq⟩ := hsteps i hi
    have hb := hstep (seq i) hne hnadj
    rw [← heq] at hb
    linarith
  have hloc : ∀ i : ℕ, i ≤ L → distance (seq i) < outer → distance (seq i) < contracted := by
    intro i hi
    refine hlocal (seq i) (hchordseq i hi) ?_ ?_
    · have hlow := hchain 0 i (Nat.zero_le _) hi
      simpa only [h0] using hlow
    · have hup := hchain i L hi le_rfl
      simpa only [hL] using hup
  have hendSeq : distance (seq L) < barrier := by rw [hL]; exact hend
  have hzero := seq_barrier_descent (fun i => distance (seq i)) houter hcb hendSeq hmove hloc 0
    (Nat.zero_le _)
  simpa only [h0] using hzero

/-! ## 5. Instanciación por la distancia de edición normalizada -/

/-- **Sustituto de descenso para
`graphFamDistNorm_barrier_of_symmetrizationPath_invariant`.** -/
theorem graphFamDistNorm_barrier_of_symmetrizationPath_invariant_descent
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (houter : barrier + 1 / (Fintype.card V : ℚ) ≤ outer)
    (hcb : contracted ≤ barrier)
    {G H : SimpleGraph V}
    (hG : PaperIV.IsChordal G)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < contracted)
    (hreach : SymmetrizationPath G H)
    (hend : graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier := by
  apply barrier_of_symmetrizationPath_invariant_descent
    (distance := fun X => graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2))
    houter hcb ?_ hG hlocal hreach hend
  intro X target source hne hnadj
  exact PaperIV.SymmetrizationMetricStep.graphFamDistNorm_step F hF hn X hne hnadj

/-- **Sustituto de descenso para el empaquetado terminal
`graphFamDistNorm_barrier_of_terminal_symmetrizationPath`.**

Éste es el enunciado que la rama cercana consumiría. Con él, el ensamblaje final de H1 puede
evitar `FirstEntry`, `FirstEntryWindow`, `EditFirstEntry` y `SymmetrizationBarrier` por completo. -/
theorem graphFamDistNorm_barrier_of_terminal_symmetrizationPath_descent
    (F : Finset (Finset (Sym2 V))) (hF : F.Nonempty)
    {outer barrier contracted : ℚ}
    (hn : 2 ≤ Fintype.card V)
    (houter : barrier + 1 / (Fintype.card V : ℚ) ≤ outer)
    (hcb : contracted ≤ barrier)
    {G : SimpleGraph V} (hG : PaperIV.IsChordal G)
    (hlocal : ∀ H : SimpleGraph V, ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      F4' G ≤ F4' X → F4' X ≤ F4' H →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < outer →
      graphFamDistNorm F hF X ((Fintype.card V : ℚ) ^ 2) < contracted)
    (hterminal : ∀ H : SimpleGraph V, SymmetrizationPath G H → PaperIV.IsChordal H →
      PaperIV.TerminalSplit.IsUniversalCoreSplit H →
      graphFamDistNorm F hF H ((Fintype.card V : ℚ) ^ 2) < barrier) :
    graphFamDistNorm F hF G ((Fintype.card V : ℚ) ^ 2) < barrier := by
  obtain ⟨H, hreach, hHchord, hHterm, -⟩ := exists_terminal_symmetrizationPath G hG
  exact graphFamDistNorm_barrier_of_symmetrizationPath_invariant_descent F hF hn houter hcb hG
    (hlocal H) hreach (hterminal H hreach hHchord hHterm)

end PaperIV.H1DescentBarrier
