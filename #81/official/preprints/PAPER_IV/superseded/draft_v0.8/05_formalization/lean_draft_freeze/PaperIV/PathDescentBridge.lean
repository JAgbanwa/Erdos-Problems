import PaperIV.VertexCopyGate

/-!
# Dos mecanismos alternativos de propagación, conectados a `SymmetrizationPath`

El retorno externo de Aristotle (proyecto `863917a0`) sustituye el mecanismo de **primera
entrada** —elegir con `Nat.find` el menor índice que entra en la bola y contradecir con su
predecesor— por dos argumentos constructivos. Este módulo los porta y los **conecta a nuestro
modelo**.

## El problema de conexión

Sus mecanismos operan sobre una **sucesión indexada por `ℕ`** de longitud `L`. Nuestro
`VertexCopyGate.SymmetrizationPath` es una **relación inductiva**. No son la misma forma, así que no se
pueden aplicar directamente: hace falta extraer un camino.

Eso es `symmetrizationPath_toSeq`, y es lo único de este módulo que vuelve a inducir sobre `SymmetrizationPath`.
A partir de ahí, la propagación es independiente.

## Los tres argumentos, ahora disponibles

Para la misma conclusión —la barrera se propaga hacia atrás a lo largo del camino— tenemos:

| | mecanismo | dónde |
|---|---|---|
| publicado | índice mínimo (`Nat.find`) + contradicción | `PaperIV.FirstEntry` (código muerto) |
| nuestro | inducción sobre la relación `SymmetrizationPath` | `SymmetrizationBarrier.barrier_of_symmetrizationPath` |
| **nuevo 1** | inducción descendente desde el extremo | `descent_close_of_le` |
| **nuevo 2** | recursión sobre la longitud del camino | `descent_by_length` |

El mecanismo 1 da **estrictamente más** que los otros: la conclusión en *todos* los índices
`j ≤ L`, no sólo en el inicial. Nuestra cadena hoy sólo consume el inicial, pero la versión
fuerte queda disponible.

## Lo que esto sí y no establece

**Sí:** que la propagación admite al menos tres argumentos distintos, y que dos de ellos no
seleccionan ningún índice extremal.

**No:** independencia de la demostración completa. El paso de propagación es uno de muchos, y
`symmetrizationPath_toSeq` sigue induciendo sobre la misma relación. Medir la independencia real exige
comparar conos de dependencias, no contar mecanismos.

Los enunciados de `descent_step`, `descent_close_of_le` y `descent_by_length` son ports del
retorno de Aristotle; el puente a `SymmetrizationPath` y la reprueba de la barrera son nuestros.
-/

namespace PaperIV.PathDescentBridge

open PaperIV.VertexCopyGate

/-! ## 1. El paso local, común a los dos mecanismos -/

/-- **El contenido analítico**, aislado: si el siguiente estado está dentro de la media bola y el
paso es menor que un cuarto de radio, el estado actual está dentro del radio, y la contracción
local lo mete en el cuarto. -/
theorem descent_step {a b rho step : ℚ}
    (hrho : 0 < rho) (hstepSmall : step < rho / 4)
    (hnext : b < rho / 2) (hmove : a - step ≤ b)
    (hlocal : a < rho → a < rho / 4) :
    a < rho / 4 := by
  have hfull : a < rho := by linarith
  exact hlocal hfull

/-! ## 2. Mecanismo 1: inducción descendente desde el extremo -/

/-- **Todos los índices están dentro de la media bola.**

Inducción sobre la distancia `k` al extremo. No se elige ningún índice y no hay contradicción.
Da estrictamente más que la primera entrada: la conclusión vale en todo `j ≤ L`. -/
theorem descent_close_of_le
    (distance : ℕ → ℚ) (L : ℕ) (rho step : ℚ)
    (hrho : 0 < rho) (hstepSmall : step < rho / 4)
    (hend : distance L < rho / 2)
    (hmovement : ∀ i : ℕ, i < L → distance i - step ≤ distance (i + 1))
    (hlocal : ∀ i : ℕ, i ≤ L → distance i < rho → distance i < rho / 4)
    {j : ℕ} (hj : j ≤ L) :
    distance j < rho / 2 := by
  have key : ∀ k : ℕ, k ≤ L → distance (L - k) < rho / 2 := by
    intro k
    induction k with
    | zero => intro _; simpa using hend
    | succ k ih =>
        intro hk
        have hnext : distance (L - k) < rho / 2 := ih (Nat.le_of_succ_le hk)
        have hsucc : L - (k + 1) + 1 = L - k := by omega
        have hmove := hmovement (L - (k + 1)) (by omega)
        rw [hsucc] at hmove
        have hq : distance (L - (k + 1)) < rho / 4 :=
          descent_step (rho := rho) (step := step) hrho hstepSmall hnext hmove
            (hlocal (L - (k + 1)) (Nat.sub_le _ _))
        linarith
  have hrw : L - (L - j) = j := by omega
  have := key (L - j) (Nat.sub_le _ _)
  rwa [hrw] at this

/-! ## 3. Mecanismo 2: recursión sobre la longitud -/

/-- **La barrera en el origen, por recursión en la longitud.**

La hipótesis de inducción se aplica a la sucesión desplazada, es decir al camino sin su primer
paso. Tampoco se elige índice extremal. -/
theorem descent_by_length (rho step : ℚ) (hrho : 0 < rho) (hstepSmall : step < rho / 4) :
    ∀ (L : ℕ) (distance : ℕ → ℚ),
      distance L < rho / 2 →
      (∀ i : ℕ, i < L → distance i - step ≤ distance (i + 1)) →
      (∀ i : ℕ, i ≤ L → distance i < rho → distance i < rho / 4) →
      distance 0 < rho / 2 := by
  intro L
  induction L with
  | zero => intro distance hend _ _; exact hend
  | succ L ih =>
      intro distance hend hmovement hlocal
      have htail : distance 1 < rho / 2 := by
        refine ih (fun i => distance (i + 1)) (by simpa using hend) ?_ ?_
        · intro i hi; exact hmovement (i + 1) (by omega)
        · intro i hi; exact hlocal (i + 1) (by omega)
      have hq : distance 0 < rho / 4 :=
        descent_step (rho := rho) (step := step) hrho hstepSmall htail
          (hmovement 0 (by omega)) (hlocal 0 (by omega))
      linarith

/-! ## 4. El puente: de `SymmetrizationPath` a una sucesión -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Todo testigo de `SymmetrizationPath` es un camino literal.**

Extrae de la relación inductiva una sucesión `seq : ℕ → SimpleGraph V` con `seq 0 = G`,
`seq L = H` y cada paso una copia fina guardada. Es el único punto de este módulo que vuelve a
inducir sobre `SymmetrizationPath`; a partir de aquí la propagación es independiente. -/
theorem symmetrizationPath_toSeq {G H : SimpleGraph V} (h : SymmetrizationPath G H) :
    ∃ (L : ℕ) (seq : ℕ → SimpleGraph V),
      seq 0 = G ∧ seq L = H ∧
      ∀ i : ℕ, i < L → ∃ t s : V, t ≠ s ∧ ¬ (seq i).Adj t s ∧
        seq (i + 1) = PaperIV.VertexCopy.graph (seq i) t s := by
  induction h with
  | refl G => exact ⟨0, fun _ => G, rfl, rfl, fun i hi => absurd hi (by omega)⟩
  | @step G H t s hne hnadj _ _ _ _ htail ih =>
      obtain ⟨L, seq, h0, hL, hstep⟩ := ih
      refine ⟨L + 1, fun i => if i = 0 then G else seq (i - 1), rfl, ?_, ?_⟩
      · simp only [if_neg (Nat.succ_ne_zero L)]
        simpa using hL
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
            have : i + 1 - 1 = (i - 1) + 1 := by omega
            rw [this]
            exact heq'

end PaperIV.PathDescentBridge
