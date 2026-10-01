import PaperIV.PathDescentBridge

/-!
# La barrera de primera entrada, demostrada por el mecanismo de descenso

`PathDescentBridge` porta los dos mecanismos del retorno externo y extrae una sucesión de un
testigo de `SymmetrizationPath`. Aquí se cierra el círculo: **se vuelve a demostrar nuestra barrera**
(`SymmetrizationBarrier.barrier_of_symmetrizationPath`) sin inducir sobre la relación salvo en el puente, y
se mide qué cambia al hacerlo.

## Lo que se encuentra al conectarlos

Los dos mecanismos no demuestran el mismo teorema. Contraen en puntos distintos del paso:

| | dónde se aplica la contracción local | qué hace falta |
|---|---|---|
| nuestro | en el **sucesor**, ya dentro de la barrera | `barrier ≤ outer`, `contracted + stepBudget < barrier` |
| descenso | en el **punto actual**, metido en `outer` por el paso | `barrier + stepBudget ≤ outer`, `contracted ≤ barrier` |

`hypotheses_incomparable` exhibe testigos racionales en las dos direcciones: **ninguno de los dos
juegos de hipótesis implica al otro.** No es una reescritura del mismo argumento.

Y el mecanismo de descenso paga con una conclusión más fuerte: `seq_contracted_of_end` y
`contracted_of_symmetrizationPath_descent` dan que **todo** el camino queda dentro de la bola contraída, no
sólo dentro de la barrera, y lo hacen sin mencionar `barrier` en absoluto.

## Nota sobre nuestra demostración vigente

`SymmetrizationBarrier.barrier_of_symmetrizationPath` abre con `by_contra hnot`. No hace falta: de
`hcontracted` y `hstep'` sale `distance G < barrier` directamente. `barrier_of_symmetrizationPath_direct`
lo demuestra sin la contradicción, con el mismo enunciado y las mismas hipótesis.

## Lo que esto NO establece

Ninguna de las tres rutas está hoy en el cono de dependencias de `RC01Final`,
`RC01FarAssembly` ni `NearRegimePackingInterface`: a `SymmetrizationBarrier` no lo importa nadie.
Tener tres mecanismos para la propagación no mueve la demostración publicada mientras la
propagación no se consuma.
-/

namespace PaperIV.PathDescentBarrier

open PaperIV.VertexCopyGate
open PaperIV.PathDescentBridge

/-! ## 1. Los dos mecanismos, en la forma general de nuestra barrera

`PathDescentBridge` los tiene en la forma `(rho, rho/2, rho/4)` del retorno externo. Nuestra
barrera tiene cuatro parámetros libres `(outer, barrier, contracted, stepBudget)`; para poder
enchufarlos hay que generalizarlos, y es al hacerlo cuando se ve que las hipótesis no coinciden. -/

/-- **Mecanismo de descenso, forma general.** Inducción descendente sobre la distancia al
extremo. La contracción local se aplica en el punto actual, al que el paso mete dentro de
`outer`. -/
theorem seq_barrier_descent
    (d : ℕ → ℚ) {outer barrier contracted stepBudget : ℚ}
    (houter : barrier + stepBudget ≤ outer)
    (hcb : contracted ≤ barrier)
    {L : ℕ} (hend : d L < barrier)
    (hmove : ∀ i : ℕ, i < L → d i - stepBudget ≤ d (i + 1))
    (hlocal : ∀ i : ℕ, i ≤ L → d i < outer → d i < contracted) :
    ∀ j : ℕ, j ≤ L → d j < barrier := by
  have key : ∀ k : ℕ, k ≤ L → d (L - k) < barrier := by
    intro k
    induction k with
    | zero => intro _; simpa using hend
    | succ k ih =>
        intro hk
        have hnext : d (L - k) < barrier := ih (Nat.le_of_succ_le hk)
        have hsucc : L - (k + 1) + 1 = L - k := by omega
        have hmv := hmove (L - (k + 1)) (by omega)
        rw [hsucc] at hmv
        have houterHere : d (L - (k + 1)) < outer := by linarith
        have := hlocal (L - (k + 1)) (Nat.sub_le _ _) houterHere
        linarith
  intro j hj
  have hrw : L - (L - j) = j := by omega
  have := key (L - j) (Nat.sub_le _ _)
  rwa [hrw] at this

/-- **El mismo enunciado, por recursión sobre la longitud.** Segundo mecanismo del retorno
externo: la hipótesis de inducción se aplica al camino sin su primer paso. -/
theorem seq_barrier_byLength
    {outer barrier contracted stepBudget : ℚ}
    (houter : barrier + stepBudget ≤ outer)
    (hcb : contracted ≤ barrier) :
    ∀ (L : ℕ) (d : ℕ → ℚ),
      d L < barrier →
      (∀ i : ℕ, i < L → d i - stepBudget ≤ d (i + 1)) →
      (∀ i : ℕ, i ≤ L → d i < outer → d i < contracted) →
      d 0 < barrier := by
  intro L
  induction L with
  | zero => intro d hend _ _; exact hend
  | succ L ih =>
      intro d hend hmove hlocal
      have htail : d 1 < barrier := by
        refine ih (fun i => d (i + 1)) (by simpa using hend) ?_ ?_
        · intro i hi; exact hmove (i + 1) (by omega)
        · intro i hi; exact hlocal (i + 1) (by omega)
      have hmv := hmove 0 (by omega)
      have houterHere : d 0 < outer := by linarith
      have := hlocal 0 (by omega) houterHere
      linarith

/-- **Lo que el descenso compra de más: la bola contraída, y sin `barrier`.**

Si el extremo está dentro de `contracted`, *todo* el camino lo está. El parámetro `barrier`
desaparece del enunciado: la única condición es `contracted + stepBudget ≤ outer`. Nuestra
barrera no da esto — contrae en el sucesor, así que sólo concluye sobre `barrier`. -/
theorem seq_contracted_of_end
    (d : ℕ → ℚ) {outer contracted stepBudget : ℚ}
    (houter : contracted + stepBudget ≤ outer)
    {L : ℕ} (hend : d L < contracted)
    (hmove : ∀ i : ℕ, i < L → d i - stepBudget ≤ d (i + 1))
    (hlocal : ∀ i : ℕ, i ≤ L → d i < outer → d i < contracted) :
    ∀ j : ℕ, j ≤ L → d j < contracted :=
  seq_barrier_descent d (barrier := contracted) houter le_rfl hend hmove hlocal

/-! ## 2. Las hipótesis de los dos mecanismos son incomparables -/

/-- **Ninguno de los dos juegos de hipótesis implica al otro.**

A la izquierda, `(outer, barrier, contracted, stepBudget) = (1, 1, 0, 1/2)` cumple lo nuestro y
no lo del descenso. A la derecha, `(10, 1, 1, 1/2)` cumple lo del descenso y no lo nuestro.

Esto es la medida honesta de la independencia del paso: no es el mismo argumento reescrito. -/
theorem hypotheses_incomparable :
    (∃ outer barrier contracted stepBudget : ℚ,
        (barrier ≤ outer ∧ contracted + stepBudget < barrier) ∧
        ¬ (barrier + stepBudget ≤ outer ∧ contracted ≤ barrier)) ∧
    (∃ outer barrier contracted stepBudget : ℚ,
        (barrier + stepBudget ≤ outer ∧ contracted ≤ barrier) ∧
        ¬ (barrier ≤ outer ∧ contracted + stepBudget < barrier)) := by
  constructor
  · exact ⟨1, 1, 0, 1/2, by norm_num, by norm_num⟩
  · exact ⟨10, 1, 1, 1/2, by norm_num, by norm_num⟩

/-! ## 3. El puente, reforzado con la cordalidad -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`symmetrizationPath_toSeq` llevando además la cordalidad de cada estado.**

La contracción local de la barrera pide `IsChordal X`, así que la sucesión desnuda no basta.
`SymmetrizationPath` guarda `hchord` en cada paso y la cordalidad del origen viene de fuera; juntas dan
la cordalidad en todo índice `i ≤ L`. -/
theorem symmetrizationPath_toSeqChordal {G H : SimpleGraph V} (h : SymmetrizationPath G H) :
    PaperIV.IsChordal G →
    ∃ (L : ℕ) (seq : ℕ → SimpleGraph V),
      seq 0 = G ∧ seq L = H ∧
      (∀ i : ℕ, i ≤ L → PaperIV.IsChordal (seq i)) ∧
      ∀ i : ℕ, i < L → ∃ t s : V, t ≠ s ∧ ¬ (seq i).Adj t s ∧
        seq (i + 1) = PaperIV.VertexCopy.graph (seq i) t s := by
  induction h with
  | refl G =>
      intro hG
      exact ⟨0, fun _ => G, rfl, rfl, fun _ _ => hG, fun i hi => absurd hi (by omega)⟩
  | @step G H t s hne hnadj _ hchord _ _ htail ih =>
      intro hG
      obtain ⟨L, seq, h0, hL, hchordseq, hstep⟩ := ih hchord
      refine ⟨L + 1, fun i => if i = 0 then G else seq (i - 1), rfl, ?_, ?_, ?_⟩
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

/-! ## 4. La barrera, por el mecanismo de descenso -/

/-- **La barrera de primera entrada, demostrada por descenso.**

Mismo enunciado que `SymmetrizationBarrier.barrier_of_symmetrizationPath` salvo por las dos hipótesis
escalares, que son las del descenso y no las nuestras (`hypotheses_incomparable`). La única
inducción sobre `SymmetrizationPath` está en `symmetrizationPath_toSeqChordal`; la propagación es
`seq_barrier_descent`. -/
theorem barrier_of_symmetrizationPath_descent
    (distance : SimpleGraph V → ℚ)
    {outer barrier contracted stepBudget : ℚ}
    (houter : barrier + stepBudget ≤ outer)
    (hcb : contracted ≤ barrier)
    (hstep : ∀ (X : SimpleGraph V) {target source : V},
      target ≠ source → ¬ X.Adj target source →
      distance X - distance (PaperIV.VertexCopy.graph X target source) ≤ stepBudget)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      distance X < outer → distance X < contracted)
    {G H : SimpleGraph V}
    (hG : PaperIV.IsChordal G)
    (hreach : SymmetrizationPath G H)
    (hend : distance H < barrier) :
    distance G < barrier := by
  obtain ⟨L, seq, h0, hL, hchordseq, hsteps⟩ := symmetrizationPath_toSeqChordal hreach hG
  have hmove : ∀ i : ℕ, i < L →
      distance (seq i) - stepBudget ≤ distance (seq (i + 1)) := by
    intro i hi
    obtain ⟨t, s, hne, hnadj, heq⟩ := hsteps i hi
    have hb := hstep (seq i) hne hnadj
    rw [← heq] at hb
    linarith
  have hloc : ∀ i : ℕ, i ≤ L → distance (seq i) < outer → distance (seq i) < contracted :=
    fun i hi => hlocal (seq i) (hchordseq i hi)
  have hendSeq : distance (seq L) < barrier := by rw [hL]; exact hend
  have hzero := seq_barrier_descent (fun i => distance (seq i)) houter hcb hendSeq hmove hloc 0
    (Nat.zero_le _)
  simpa only [h0] using hzero

/-- **La forma fuerte: el camino entero dentro de la bola contraída.**

No tiene análogo en nuestra barrera. Si el extremo está en `contracted`, el origen también, y la
hipótesis es sólo `contracted + stepBudget ≤ outer` — `barrier` no aparece. -/
theorem contracted_of_symmetrizationPath_descent
    (distance : SimpleGraph V → ℚ)
    {outer contracted stepBudget : ℚ}
    (houter : contracted + stepBudget ≤ outer)
    (hstep : ∀ (X : SimpleGraph V) {target source : V},
      target ≠ source → ¬ X.Adj target source →
      distance X - distance (PaperIV.VertexCopy.graph X target source) ≤ stepBudget)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      distance X < outer → distance X < contracted)
    {G H : SimpleGraph V}
    (hG : PaperIV.IsChordal G)
    (hreach : SymmetrizationPath G H)
    (hend : distance H < contracted) :
    distance G < contracted :=
  barrier_of_symmetrizationPath_descent distance (barrier := contracted) houter le_rfl hstep hlocal
    hG hreach hend

/-! ## 5. Nuestra demostración vigente, sin la contradicción -/

/-- **`barrier_of_symmetrizationPath` sin `by_contra`.**

Enunciado e hipótesis idénticos a `SymmetrizationBarrier.barrier_of_symmetrizationPath`. La contradicción de
allí es prescindible: la contracción en el sucesor más la cota del paso dan la conclusión
directamente. -/
theorem barrier_of_symmetrizationPath_direct
    (distance : SimpleGraph V → ℚ)
    {outer barrier contracted stepBudget : ℚ}
    (hbarrierOuter : barrier ≤ outer)
    (hgap : contracted + stepBudget < barrier)
    (hstep : ∀ (X : SimpleGraph V) {target source : V},
      target ≠ source → ¬ X.Adj target source →
      distance X - distance (PaperIV.VertexCopy.graph X target source) ≤ stepBudget)
    (hlocal : ∀ X : SimpleGraph V, PaperIV.IsChordal X →
      distance X < outer → distance X < contracted)
    {G H : SimpleGraph V}
    (hG : PaperIV.IsChordal G)
    (hreach : SymmetrizationPath G H)
    (hend : distance H < barrier) :
    distance G < barrier := by
  induction hreach with
  | refl G => exact hend
  | @step G H target source hne hnadj _ hchord _ _ htail ih =>
      have hnext : distance (PaperIV.VertexCopy.graph G target source) < barrier :=
        ih hchord hend
      have hcontracted : distance (PaperIV.VertexCopy.graph G target source) < contracted :=
        hlocal _ hchord (lt_of_lt_of_le hnext hbarrierOuter)
      have hstep' := hstep G hne hnadj
      linarith

end PaperIV.PathDescentBarrier
