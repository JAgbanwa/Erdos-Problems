import ExactReduction.Deletion
import ExactReduction.Arithmetic

/-!
# El núcleo de contraejemplo mínimo para `c₄(G) ≤ M(n)`

Objetivo: `b = 0` para **todo** `n`, es decir `c₄(G) ≤ M(n) = ⌊n(n+1)/6⌋` sin umbral.
Este módulo formaliza el primer paso de la ruta integral exacta: qué aspecto tiene,
necesariamente, un contraejemplo de orden mínimo.

* `TargetOn n` — el enunciado objetivo para cordales con soporte de a lo sumo `n` vértices.
  El soporte es un `Finset` del tipo de vértices (y no el cardinal del tipo) precisamente
  para que borrar un vértice —que en `ExactReduction.deleteAt` lo deja aislado, sin cambiar
  el tipo— haga descender el parámetro de la inducción.
* `targetOn_zero`, `targetOn_one` — casos base.
* `target_of_small_degree` — **el paso**: si vale `TargetOn (n−1)` y `G` tiene un vértice de
  grado `≤ ⌊(n+1)/3⌋`, entonces `G` cumple el objetivo en `n`.  El coste es exactamente
  `M(n) − M(n−1) = ⌊(n+1)/3⌋` (`ExactReduction.targetSize_sub_one`).
* `minDegree_of_minimal_counterexample` — **grado mínimo crítico**:
  `δ(G) ≥ ⌊(n+1)/3⌋ + 1`.
* `exists_large_clique_of_minimal_counterexample` — con el vértice simplicial de Dirac,
  `ω(G) ≥ ⌊(n+1)/3⌋ + 2`.
* `kernel_of_minimal_counterexample` — las dos conclusiones juntas.
-/

namespace ExactReduction

open PaperIV PaperIV.FarRounding Finset

/-- El objetivo exacto `c₄ ≤ M(n)` para grafos cordales cuyo soporte tiene a lo sumo `n`
vértices. -/
def TargetOn (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V), (∀ a b : V, G.Adj a b → a ∈ s) → s.card ≤ n → G.IsChordal →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n

/-! ## 1. Casos base -/

/-- Un grafo sin aristas tiene la partición vacía. -/
theorem exists_empty_cliquePartition {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : ∀ a b : V, ¬ G.Adj a b) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = 0 := by
  refine ⟨⟨∅, by simp, by simp, by simp, ?_⟩, by simp [CliquePartition.OrderAtMost], rfl⟩
  ext e
  induction e using Sym2.ind with
  | _ a b => simp [h a b]

theorem targetOn_zero : TargetOn 0 := by
  intro V _ _ G _ s hsupp hcard _
  have hs : s = ∅ := Finset.card_eq_zero.1 (Nat.le_antisymm hcard (Nat.zero_le _))
  obtain ⟨Q, hQ4, hQ0⟩ := exists_empty_cliquePartition G (by
    intro a b hab
    have := hsupp a b hab
    rw [hs] at this
    simp at this)
  exact ⟨Q, hQ4, by simp [hQ0]⟩

theorem targetOn_one : TargetOn 1 := by
  intro V _ _ G _ s hsupp hcard _
  obtain ⟨Q, hQ4, hQ0⟩ := exists_empty_cliquePartition G (by
    intro a b hab
    have ha : a ∈ s := hsupp a b hab
    have hb : b ∈ s := hsupp b a hab.symm
    have : a = b := Finset.card_le_one.1 hcard a ha b hb
    exact hab.ne this)
  exact ⟨Q, hQ4, by simp [hQ0]⟩

/-! ## 2. El paso de borrado -/

/-- **El paso de la reducción por borrado de un vértice.**  Si el objetivo vale para
soportes de `n−1` vértices y `G` tiene un vértice de grado a lo sumo `⌊(n+1)/3⌋`, el
objetivo vale para `G`: se borra el vértice y sus aristas se restauran como `K₂`, pagando
exactamente `M(n) − M(n−1)`. -/
theorem target_of_small_degree {n : ℕ} (hn : 1 ≤ n) (hIH : TargetOn (n - 1))
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hsupp : ∀ a b : V, G.Adj a b → a ∈ s) (hcard : s.card ≤ n)
    (hchord : G.IsChordal) {v : V} (hv : v ∈ s) (hdeg : G.degree v ≤ (n + 1) / 3) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n := by
  classical
  have hsupp' : ∀ a b : V, (deleteAt G v).Adj a b → a ∈ s.erase v := by
    rintro a b ⟨hab, ha, -⟩
    exact Finset.mem_erase.2 ⟨ha, hsupp a b hab⟩
  have hcard' : (s.erase v).card ≤ n - 1 := by
    have := Finset.card_erase_of_mem hv
    have hpos : 1 ≤ s.card := Finset.card_pos.2 ⟨v, hv⟩
    omega
  obtain ⟨Q', hQ'4, hQ'size⟩ :=
    hIH V (deleteAt G v) (s.erase v) hsupp' hcard' (deleteAt_isChordal hchord v)
  obtain ⟨Q, hQ4, hQsize⟩ :=
    exists_cliquePartition_of_deleteAt (G := G) (v := v) Q' (by norm_num) hQ'4
  refine ⟨Q, hQ4, ?_⟩
  have hstep : PaperIV.targetSize n = PaperIV.targetSize (n - 1) + (n + 1) / 3 :=
    targetSize_sub_one n hn
  omega

/-! ## 3. El núcleo de un contraejemplo mínimo -/

variable {n : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- **Grado mínimo crítico.**  Si el objetivo ya vale en `n−1` y `G` es un contraejemplo de
orden `≤ n`, entonces todo vértice tiene grado `≥ ⌊(n+1)/3⌋ + 1`. -/
theorem minDegree_of_minimal_counterexample (hn : 1 ≤ n) (hIH : TargetOn (n - 1))
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V ≤ n)
    (hchord : G.IsChordal)
    (hbad : ¬ ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n) :
    ∀ v : V, (n + 1) / 3 < G.degree v := by
  intro v
  by_contra hle
  push_neg at hle
  exact hbad (target_of_small_degree hn hIH G Finset.univ (fun a b _ => Finset.mem_univ a)
    (by simpa using hcard) hchord (Finset.mem_univ v) hle)

/-- Un contraejemplo tiene vértices. -/
theorem nonempty_of_minimal_counterexample
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbad : ¬ ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n) :
    Nonempty V := by
  by_contra hempty
  rw [not_nonempty_iff] at hempty
  obtain ⟨Q, hQ4, hQ0⟩ := exists_empty_cliquePartition G (fun a _ _ => hempty.false a)
  exact hbad ⟨Q, hQ4, by simp [hQ0]⟩

/-- El vecindario cerrado de un vértice simplicial es una clique con `deg(v) + 1` vértices. -/
theorem isClique_closedNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hv : G.IsSimplicial v) :
    G.IsClique ((insert v (G.neighborFinset v) : Finset V) : Set V) ∧
      (insert v (G.neighborFinset v)).card = G.degree v + 1 := by
  constructor
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      SimpleGraph.mem_neighborFinset] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hb
    · rcases hb with rfl | hb
      · exact ha.symm
      · exact hv ha hb hab
  · rw [Finset.card_insert_of_notMem (by simp), SimpleGraph.card_neighborFinset_eq_degree]

/-- **Clique grande en un contraejemplo mínimo.**  Todo cordal tiene un vértice simplicial
(Dirac); su vecindario cerrado es una clique, luego `ω(G) ≥ δ(G) + 1 ≥ ⌊(n+1)/3⌋ + 2`. -/
theorem exists_large_clique_of_minimal_counterexample (hn : 1 ≤ n) (hIH : TargetOn (n - 1))
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V ≤ n)
    (hchord : G.IsChordal)
    (hbad : ¬ ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n) :
    ∃ K : Finset V, G.IsClique (K : Set V) ∧ (n + 1) / 3 + 2 ≤ K.card := by
  haveI : Nonempty V := nonempty_of_minimal_counterexample G hbad
  obtain ⟨v, hv⟩ := hchord.exists_isSimplicial
  obtain ⟨hclique, hcardK⟩ := isClique_closedNeighborFinset G hv
  refine ⟨insert v (G.neighborFinset v), hclique, ?_⟩
  have := minDegree_of_minimal_counterexample hn hIH G hcard hchord hbad v
  omega

/-- Un contraejemplo de orden mínimo tiene **exactamente** `n` vértices: con menos, la
hipótesis de inducción `TargetOn (n−1)` ya lo resolvería. -/
theorem card_eq_of_minimal_counterexample (hIH : TargetOn (n - 1))
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V ≤ n)
    (hchord : G.IsChordal)
    (hbad : ¬ ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n) :
    Fintype.card V = n := by
  by_contra hne
  have hlt : Fintype.card V ≤ n - 1 := by omega
  obtain ⟨Q, hQ4, hQsize⟩ :=
    hIH V G Finset.univ (fun a b _ => Finset.mem_univ a) (by simpa using hlt) hchord
  exact hbad ⟨Q, hQ4, le_trans hQsize (targetSize_mono (by omega))⟩

/-- Un contraejemplo de orden mínimo es denso: `2e(G) ≥ n·(⌊(n+1)/3⌋ + 1)`, o sea
`e(G) ≳ n²/6`. -/
theorem card_edges_of_minimal_counterexample (hn : 1 ≤ n) (hIH : TargetOn (n - 1))
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V ≤ n)
    (hchord : G.IsChordal)
    (hbad : ¬ ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n) :
    n * ((n + 1) / 3 + 1) ≤ 2 * G.edgeFinset.card := by
  have hdeg := minDegree_of_minimal_counterexample hn hIH G hcard hchord hbad
  have hcard' : Fintype.card V = n :=
    card_eq_of_minimal_counterexample hIH G hcard hchord hbad
  have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hlow : ∑ _v : V, ((n + 1) / 3 + 1) ≤ ∑ v : V, G.degree v :=
    Finset.sum_le_sum fun v _ => hdeg v
  rw [Finset.sum_const, Finset.card_univ, hcard', smul_eq_mul] at hlow
  omega

/-- **El núcleo de contraejemplo mínimo, completo.** -/
theorem kernel_of_minimal_counterexample (hn : 1 ≤ n) (hIH : TargetOn (n - 1))
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V ≤ n)
    (hchord : G.IsChordal)
    (hbad : ¬ ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n) :
    (∀ v : V, (n + 1) / 3 < G.degree v) ∧
      ∃ K : Finset V, G.IsClique (K : Set V) ∧ (n + 1) / 3 + 2 ≤ K.card :=
  ⟨minDegree_of_minimal_counterexample hn hIH G hcard hchord hbad,
    exists_large_clique_of_minimal_counterexample hn hIH G hcard hchord hbad⟩

/-- Reformulación positiva: para pasar de `n−1` a `n` basta encontrar, en cada cordal de
orden `≤ n`, **un** vértice de grado `≤ ⌊(n+1)/3⌋`. -/
theorem targetOn_of_small_degree_vertex (hn : 1 ≤ n) (hIH : TargetOn (n - 1))
    (hdeg : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (s : Finset V), (∀ a b : V, G.Adj a b → a ∈ s) → s.card ≤ n → G.IsChordal →
        s.Nonempty → ∃ v ∈ s, G.degree v ≤ (n + 1) / 3) :
    TargetOn n := by
  intro V _ _ G _ s hsupp hcard hchord
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · obtain ⟨Q, hQ4, hQ0⟩ := exists_empty_cliquePartition G (by
      intro a b hab
      have := hsupp a b hab
      simp at this)
    exact ⟨Q, hQ4, by simp [hQ0]⟩
  · obtain ⟨v, hv, hvdeg⟩ := hdeg V G s hsupp hcard hchord hs
    exact target_of_small_degree hn hIH G s hsupp hcard hchord hv hvdeg

end ExactReduction
