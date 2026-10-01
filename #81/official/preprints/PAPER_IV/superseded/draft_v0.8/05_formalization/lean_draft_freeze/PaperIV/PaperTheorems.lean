import PaperIV.Erdos81Unconditional
import PaperIV.HybridRoute
import PaperIV.SplitCompleteSharpValue
import PaperIV.CliqueTree

/-!
# Los enunciados del paper que no viven en ningún módulo técnico

Tres cosas que el manuscrito necesita y que hasta ahora estaban repartidas o sólo enunciadas
en prosa:

1. **`erdos81_hybrid_linear_form`** — el cierre híbrido en la forma lineal `n²/6 + n/6`.
   Se demuestra sobre nuestra cadena, no sobre la del árbol de trabajo: aquélla arrastra el motor
   de regularización de raíz que este árbol ya no contiene.

2. **`splitGraph_isChordal`** — el testigo extremal **es cordal**.  Sin esto la cota inferior de
   `SplitCompleteSharpValue` no dice nada sobre el máximo en la clase de los cordales, que es
   donde vive el problema.  La demostración no toca ciclos: exhibe un **orden de eliminación
   perfecta** y aplica `IsPEO.isChordal` de la biblioteca de árboles de cliques.

3. **`erdos81_max_eq`** — el máximo eventual sobre todos los cordales.  Junta la cota superior
   universal con el testigo cordal que la alcanza; es el empaquetado que el ledger pedía, y no
   matemática nueva.

## Sobre el punto 2, que es el que costaba

En un grafo completo-split `Core ∨ Hosts`, ordenar **primero los anfitriones y después el
núcleo** es un orden de eliminación perfecta: los vecinos posteriores de cualquier vértice están
siempre contenidos en `Core`, que es una clique.  Para un anfitrión porque todos sus vecinos
están en `Core`; para un vértice del núcleo porque los índices posteriores son justamente los del
núcleo.  Eso evita por completo la combinatoria de ciclos.
-/

open scoped BigOperators

namespace PaperIV.PaperTheorems

open PaperIV.FarRounding PaperIV.SplitUniformIncidence

/-! ## 1. El cierre híbrido en forma lineal -/

/-- **Forma lineal del cierre híbrido.**  Mismo contenido que el teorema principal, escrito como
`n²/6 + n/6`, que es la forma en que el problema se enuncia históricamente. -/
theorem erdos81_hybrid_linear_form :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
          (Q.size : ℚ) ≤ (n : ℚ) ^ 2 / 6 + (n : ℚ) / 6 := by
  obtain ⟨N, hN⟩ := PaperIV.HybridDichotomy.erdos81_of_structuralDichotomy
  refine ⟨N, ?_⟩
  intro n hn G _ hG
  obtain ⟨Q, hQ4, hQsize⟩ := hN n hn G hG
  refine ⟨Q, hQ4, ?_⟩
  have h1 : (Q.size : ℚ) ≤ ((PaperIV.targetSize n : ℕ) : ℚ) := by exact_mod_cast hQsize
  have h2 : ((PaperIV.targetSize n : ℕ) : ℚ) ≤ (n : ℚ) * ((n : ℚ) + 1) / 6 :=
    PaperIV.targetSize_cast_le_continuous n
  have h3 : (n : ℚ) * ((n : ℚ) + 1) / 6 = (n : ℚ) ^ 2 / 6 + (n : ℚ) / 6 := by ring
  linarith

/-! ## 2. El testigo extremal es cordal -/

section Chordal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- En un completo-split, todo vecino de un vértice de fuera del núcleo está en el núcleo. -/
private theorem mem_core_of_adj_of_notMem {Core Hosts : Finset V} {x y : V}
    (hx : x ∉ Core) (h : (splitGraph Core Hosts).Adj x y) : y ∈ Core := by
  rcases splitGraph_adj_iff.1 h with ⟨-, hc | hc | hc⟩
  · exact absurd hc.1 hx
  · exact absurd hc.1 hx
  · exact hc.2

/-- El núcleo es una clique del completo-split. -/
private theorem core_isClique (Core Hosts : Finset V) :
    (splitGraph Core Hosts).IsClique (Core : Set V) := by
  intro x hx y hy hne
  exact splitGraph_adj_iff.2 ⟨hne, Or.inl ⟨hx, hy⟩⟩

/-- **El grafo completo-split es cordal.**

Se exhibe un orden de eliminación perfecta —anfitriones primero, núcleo después— y se aplica la
caracterización `SimpleGraph.IsPEO.isChordal`.  El punto es que, con ese orden, los vecinos
posteriores de **cualquier** vértice caen dentro de `Core`. -/
theorem splitGraph_isChordal (Core Hosts : Finset V) :
    SimpleGraph.IsChordal (splitGraph Core Hosts) := by
  classical
  -- Un orden que manda el núcleo por encima de todo lo demás.
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let ord : V → ℕ := fun x => if x ∈ Core then Fintype.card V + (e x : ℕ) else (e x : ℕ)
  have hinj : Function.Injective ord := by
    intro x y hxy
    by_cases hx : x ∈ Core <;> by_cases hy : y ∈ Core <;>
      simp only [ord, hx, hy, if_pos, if_neg, not_false_iff] at hxy
    · exact e.injective (Fin.ext (by omega))
    · exact absurd (e y).isLt (by omega)
    · exact absurd (e x).isLt (by omega)
    · exact e.injective (Fin.ext hxy)
  have hlater : ∀ v : V, {u | ord v < ord u ∧ (splitGraph Core Hosts).Adj v u} ⊆ (Core : Set V) := by
    intro v u hu
    obtain ⟨hlt, hadj⟩ := hu
    by_cases hv : v ∈ Core
    · -- `v` está en el núcleo, luego todo índice mayor también lo está
      by_contra huC
      have h1 : ord v = Fintype.card V + (e v : ℕ) := if_pos hv
      have h2 : ord u = (e u : ℕ) := if_neg huC
      have h3 := (e u).isLt
      rw [h1, h2] at hlt
      omega
    · -- `v` está fuera: todos sus vecinos están en el núcleo
      exact mem_core_of_adj_of_notMem hv hadj
  have hpeo : SimpleGraph.IsPEO (splitGraph Core Hosts) ord :=
    { injective := hinj
      isClique_later := fun v =>
        ((core_isClique Core Hosts).subset (hlater v)) }
  exact hpeo.isChordal

end Chordal

/-! ## 3. El máximo eventual sobre todos los cordales -/

section Witness

variable {n : ℕ}

/-- El núcleo crítico dentro de `Fin n`: los `(n+1)/3` primeros índices. -/
private def criticalCore (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => (x : ℕ) < (n + 1) / 3

private theorem card_criticalCore (hn : 2 ≤ n) :
    (criticalCore n).card = (n + 1) / 3 := by
  classical
  have hk : (n + 1) / 3 ≤ n := by omega
  have himg : (criticalCore n).image Fin.val = Finset.range ((n + 1) / 3) := by
    ext m
    simp only [criticalCore, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
  calc (criticalCore n).card
      = ((criticalCore n).image Fin.val).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = ((n + 1) / 3 : ℕ) := by rw [himg, Finset.card_range]

private theorem card_compl_criticalCore (hn : 2 ≤ n) :
    ((criticalCore n)ᶜ).card = n - (n + 1) / 3 := by
  classical
  rw [Finset.card_compl, card_criticalCore hn, Fintype.card_fin]

/-- **Un cordal que alcanza `targetSize n`.**  El completo-split crítico: núcleo de tamaño
`(n+1)/3` y el resto de anfitriones.  Es cordal, su partición óptima tiene orden a lo sumo cuatro,
y **ninguna** partición en cliques —ni siquiera permitiendo piezas mayores— usa menos piezas. -/
theorem exists_chordal_extremal_witness (hn : 6 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      SimpleGraph.IsChordal G ∧
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        Q.size = PaperIV.targetSize n ∧ ∀ R : CliquePartition G, Q.size ≤ R.size := by
  classical
  set k := (n + 1) / 3 with hk
  set Core : Finset (Fin n) := criticalCore n with hCore
  set Hosts : Finset (Fin n) := Coreᶜ with hHosts
  have hcard : Core.card = k := card_criticalCore (by omega)
  have hhcard : Hosts.card = n - k := by
    rw [hHosts, hCore]; exact card_compl_criticalCore (by omega)
  have hd : Disjoint Core Hosts := by rw [hHosts]; exact disjoint_compl_right
  have hcore : 2 ≤ Core.card := by rw [hcard, hk]; omega
  have hhosts : Core.card ≤ Hosts.card := by rw [hcard, hhcard, hk]; omega
  obtain ⟨Q, hQ4, hQsize, hQopt⟩ :=
    PaperIV.SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities hd hcore hhosts
  refine ⟨splitGraph Core Hosts, inferInstance,
    splitGraph_isChordal Core Hosts, Q, hQ4, ?_, hQopt⟩
  rw [hQsize, hcard, hhcard]
  have := PaperIV.SplitCompleteSharpLower.critical_baseline_eq_targetSize n (by omega)
  simpa [hk] using this

end Witness

/-- **El máximo eventual es exactamente `M(n)`.**

Dos mitades.  La cota superior vale para **todo** cordal suficientemente grande.  La inferior la
da un cordal concreto —el completo-split crítico— en el que **ninguna** partición en cliques baja
de `targetSize n`.  Juntas dicen que `M(n)` es el máximo y que se alcanza. -/
theorem erdos81_max_eq :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], SimpleGraph.IsChordal G →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n)
        ∧ (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
            SimpleGraph.IsChordal G ∧
            ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
              Q.size = PaperIV.targetSize n ∧ ∀ R : CliquePartition G, Q.size ≤ R.size) := by
  obtain ⟨N, hN⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨max N 6, ?_⟩
  intro n hn
  refine ⟨?_, exists_chordal_extremal_witness (le_trans (le_max_right N 6) hn)⟩
  intro G _ hG
  exact hN n (le_trans (le_max_left N 6) hn) G hG

end PaperIV.PaperTheorems
