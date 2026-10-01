import PaperIV.FarRounding
import PaperIV.ChordalStructure
import Mathlib.Tactic.IntervalCases

/-!
# Reducción simplicial: borrar un vértice y pagar su astro

Sea `G` cordal de orden `n` y `v` un vértice de grado `d`.  El subgrafo inducido `G − v` es
cordal (subgrafos inducidos de cordales lo son) y toda partición en cliques de `G − v` se
**levanta** a una de `G` añadiendo una pieza `K₂` por cada arista del astro de `v`:

```text
c₄(G) ≤ c₄(G − v) + d.
```

Como `M(n) − M(n−1) = ⌊(n+1)/3⌋`, el paso inductivo cierra en cuanto `d ≤ M(n) − M(n−1)`.

## Resultados principales

* `PaperIV.SimplicialReduction.exists_cliquePartition_of_delete_vertex` — el levantamiento:
  de una partición de `G − v` de orden `≤ r` sale una de `G` de orden `≤ r` y tamaño
  `≤ size + deg v`.  No se usa cordalidad ni simplicialidad: vale para cualquier vértice.
* `PaperIV.SimplicialReduction.SharpBoundAt` — la cota aguda `M(n) = ⌊n(n+1)/6⌋` para todos los
  cordales de orden `n`, con piezas de orden `≤ 4`.
* `PaperIV.SimplicialReduction.sharpBound_of_isSimplicial_degree_le` — **el paso inductivo
  pedido**: si vale la cota aguda en orden `n` y `G` cordal de orden `n+1` tiene un vértice
  simplicial de grado `≤ M(n+1) − M(n)`, entonces `G` cumple la cota aguda.
* `PaperIV.SimplicialReduction.sharpBoundAt_succ_of_largeSimplicialDegree` — la reducción:
  basta tratar los cordales en los que **todo** vértice simplicial tiene grado
  `> M(n+1) − M(n)`.
* `PaperIV.SimplicialReduction.sharpBoundAt_of_largeCliqueRegime` — el corolario que interesa:
  la conjetura para todo `n` se sigue del **régimen de clique grande**
  `ω(G) > M(n+1) − M(n) + 1`, vía Dirac.
* `PaperIV.SimplicialReduction.targetSize_succ_sub_targetSize` — el valor exacto del salto:
  `M(n+1) − M(n) = ⌊(n+2)/3⌋`.

La cordalidad se usa exactamente en dos sitios: para que `G − v` siga siendo cordal
(`SimpleGraph.IsChordal.induce`) y para que exista un vértice simplicial
(`SimpleGraph.IsChordal.exists_isSimplicial`, Dirac 1961).
-/

namespace PaperIV.SimplicialReduction

open Finset SimpleGraph PaperIV.FarRounding

universe u

/-! ## 1. Aritmética del objetivo `M(n) = ⌊n(n+1)/6⌋` -/

/-- `M` es monótona. -/
theorem targetSize_mono : Monotone targetSize := by
  intro m n hmn
  exact Nat.div_le_div_right (Nat.mul_le_mul hmn (Nat.succ_le_succ hmn))

/-- El salto exacto del objetivo: `M(n+1) − M(n) = ⌊(n+2)/3⌋ ≈ n/3`. -/
theorem targetSize_succ_sub_targetSize (n : ℕ) :
    targetSize (n + 1) - targetSize n = (n + 2) / 3 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 6 ∧ n = 6 * q + r :=
    ⟨n / 6, n % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  have e1 : (6 * q + r) * (6 * q + r + 1)
      = 36 * (q * q) + (12 * r + 6) * q + r * (r + 1) := by ring
  have e2 : (6 * q + r + 1) * (6 * q + r + 1 + 1)
      = 36 * (q * q) + (12 * r + 18) * q + (r + 1) * (r + 2) := by ring
  simp only [targetSize]
  rw [e1, e2]
  generalize q * q = s
  interval_cases r <;> omega

/-- Reformulación cómoda del paso inductivo: `M(n) + (M(n+1) − M(n)) = M(n+1)`. -/
theorem targetSize_add_jump (n : ℕ) :
    targetSize n + (targetSize (n + 1) - targetSize n) = targetSize (n + 1) :=
  Nat.add_sub_cancel' (targetSize_mono (Nat.le_succ n))

/-! ## 2. El levantamiento de una partición de `G − v` -/

section Lift

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- `pairs` conmuta con las imágenes inyectivas. -/
theorem pairs_image {W : Type*} [DecidableEq W] {f : W → V} (hf : Function.Injective f)
    (K : Finset W) : pairs (K.image f) = (pairs K).image (Sym2.map f) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · intro he
      rw [mk_mem_pairs] at he
      obtain ⟨hx, hy, hxy⟩ := he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      refine Finset.mem_image.2 ⟨s(a, b), mk_mem_pairs.2 ⟨ha, hb, fun h => hxy (by rw [h])⟩, ?_⟩
      simp
    · intro he
      obtain ⟨e', he', heq⟩ := Finset.mem_image.1 he
      induction e' using Sym2.ind with
      | _ a b =>
        rw [mk_mem_pairs] at he'
        obtain ⟨ha, hb, hab⟩ := he'
        have heq' : s(f a, f b) = s(x, y) := by simpa using heq
        rw [Sym2.eq_iff] at heq'
        rcases heq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact mk_mem_pairs.2 ⟨Finset.mem_image_of_mem f ha, Finset.mem_image_of_mem f hb,
            fun h => hab (hf h)⟩
        · exact mk_mem_pairs.2 ⟨Finset.mem_image_of_mem f hb, Finset.mem_image_of_mem f ha,
            fun h => hab (hf h).symm⟩

omit [Fintype V] in
/-- Una pieza de `G − v` subida a `V` no toca a `v`. -/
theorem not_mem_pairs_image_val {v : V} {K : Finset {u : V | u ≠ v}} {e : Sym2 V}
    (he : e ∈ pairs (K.image (Subtype.val : {u : V | u ≠ v} → V))) : v ∉ e := by
  intro hv
  rw [mem_pairs] at he
  obtain ⟨a, _, ha⟩ := Finset.mem_image.1 (he.1 v hv)
  exact a.2 ha

omit [Fintype V] in
/-- El soporte de arista de una pieza del astro es un único par. -/
theorem pairs_star {v u : V} (h : v ≠ u) : pairs ({v, u} : Finset V) = {s(v, u)} := by
  have hset : ({v, u} : Finset V) = (s(v, u) : Sym2 V).toFinset := by
    ext z; simp [Sym2.mem_toFinset]
  rw [hset, pairs_toFinset (by simp [h])]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)

/-- Las aristas de `G − v`, subidas a `V`, son exactamente las aristas de `G` que evitan `v`. -/
theorem image_edgeFinset_induce :
    (G.induce {u : V | u ≠ v}).edgeFinset.image (Sym2.map (Subtype.val : {u : V | u ≠ v} → V))
      = G.edgeFinset.filter (fun e => v ∉ e) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Sym2.mem_iff]
    constructor
    · rintro ⟨e', he', heq⟩
      induction e' using Sym2.ind with
      | _ a b =>
        have heq' : s((a : V), (b : V)) = s(x, y) := by simpa using heq
        have hab : G.Adj (a : V) (b : V) := by simpa using he'
        rw [Sym2.eq_iff] at heq'
        rcases heq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hab, by rintro (h | h); exacts [a.2 h.symm, b.2 h.symm]⟩
        · exact ⟨hab.symm, by rintro (h | h); exacts [b.2 h.symm, a.2 h.symm]⟩
    · rintro ⟨hadj, hv⟩
      have hx : x ≠ v := fun h => hv (Or.inl h.symm)
      have hy : y ≠ v := fun h => hv (Or.inr h.symm)
      exact ⟨s((⟨x, hx⟩ : {u : V | u ≠ v}), ⟨y, hy⟩), by simpa using hadj, by simp⟩

/-- El astro de `v`, cubierto por piezas `K₂`. -/
def starPieces : Finset (Finset V) := (G.neighborFinset v).image (fun u => ({v, u} : Finset V))

theorem starPieces_covers :
    (starPieces G v).biUnion pairs = G.edgeFinset.filter (fun e => v ∈ e) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [starPieces, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.mem_iff]
    constructor
    · rintro ⟨K, ⟨u, hu, rfl⟩, hmem⟩
      have hvu : G.Adj v u := by simpa using hu
      rw [mk_mem_pairs] at hmem
      obtain ⟨hx, hy, hxy⟩ := hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact ⟨hvu, Or.inl rfl⟩
      · exact ⟨hvu.symm, Or.inr rfl⟩
      · exact absurd rfl hxy
    · rintro ⟨hadj, hv⟩
      rcases hv with rfl | rfl
      · exact ⟨{v, y}, ⟨y, by simpa using hadj, rfl⟩, mk_mem_pairs.2 ⟨by simp, by simp, hadj.ne⟩⟩
      · exact ⟨{v, x}, ⟨x, by simpa using hadj.symm, rfl⟩,
          mk_mem_pairs.2 ⟨by simp, by simp, hadj.ne⟩⟩

/-- El astro de `v`, visto como conjunto de aristas. -/
theorem image_star_edges :
    (G.neighborFinset v).image (fun u => s(v, u)) = G.edgeFinset.filter (fun e => v ∈ e) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, SimpleGraph.mem_neighborFinset, Sym2.mem_iff]
    constructor
    · rintro ⟨u, hu, heq⟩
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hu, Or.inl rfl⟩
      · exact ⟨hu.symm, Or.inr rfl⟩
    · rintro ⟨hadj, hv⟩
      rcases hv with rfl | rfl
      · exact ⟨y, hadj, rfl⟩
      · exact ⟨x, hadj.symm, Sym2.eq_swap⟩

/-- Las piezas de una partición de `G − v`, subidas a `V`, cubren exactamente las aristas de `G`
que evitan `v`. -/
theorem biUnion_pairs_lift (Q : CliquePartition (G.induce {u : V | u ≠ v})) :
    (Q.pieces.biUnion fun K => pairs (K.image (Subtype.val : {u : V | u ≠ v} → V)))
      = G.edgeFinset.filter (fun e => v ∉ e) := by
  have hstep : (Q.pieces.biUnion fun K => pairs (K.image (Subtype.val : {u : V | u ≠ v} → V)))
      = (Q.pieces.biUnion pairs).image (Sym2.map (Subtype.val : {u : V | u ≠ v} → V)) := by
    rw [Finset.biUnion_image]
    exact Finset.biUnion_congr rfl (fun K _ => pairs_image Subtype.val_injective K)
  rw [hstep, Q.covers, image_edgeFinset_induce]

/-- **El levantamiento.**  Una partición en cliques de `G − v` más una pieza `K₂` por arista del
astro de `v` es una partición en cliques de `G`. -/
def liftPartition (Q : CliquePartition (G.induce {u : V | u ≠ v})) : CliquePartition G where
  pieces := Q.pieces.image (fun K => K.image (Subtype.val : {u : V | u ≠ v} → V))
      ∪ starPieces G v
  isClique := by
    intro K hK a ha b hb hab
    rcases Finset.mem_union.1 hK with hK | hK
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      have := Q.isClique K' hK' a' ha' b' hb' (fun h => hab (by rw [h]))
      simpa using this
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hK
      have hvu : G.Adj v u := by simpa using hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hvu
      · exact hvu.symm
      · exact absurd rfl hab
  two_le_card := by
    intro K hK
    rcases Finset.mem_union.1 hK with hK | hK
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact Q.two_le_card K' hK'
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hK
      have hvu : G.Adj v u := by simpa using hu
      rw [Finset.card_insert_of_notMem (by simp [hvu.ne]), Finset.card_singleton]
  edgeDisjoint := by
    intro K hK L hL hKL
    rcases Finset.mem_union.1 hK with hK | hK <;> rcases Finset.mem_union.1 hL with hL | hL
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hL
      have hne : K' ≠ L' := fun h => hKL (by rw [h])
      rw [pairs_image Subtype.val_injective, pairs_image Subtype.val_injective]
      exact (Finset.disjoint_image (Sym2.map.injective Subtype.val_injective)).2
        (Q.edgeDisjoint K' hK' L' hL' hne)
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hL
      have hvu : G.Adj v u := by simpa using hu
      refine Finset.disjoint_left.2 (fun e he he' => ?_)
      rw [pairs_star hvu.ne, Finset.mem_singleton] at he'
      subst he'
      exact not_mem_pairs_image_val he (by simp)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hL
      have hvu : G.Adj v u := by simpa using hu
      refine Finset.disjoint_right.2 (fun e he he' => ?_)
      rw [pairs_star hvu.ne, Finset.mem_singleton] at he'
      subst he'
      exact not_mem_pairs_image_val he (by simp)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hL
      have hvu : G.Adj v u := by simpa using hu
      have hvw : G.Adj v w := by simpa using hw
      have huw : u ≠ w := by
        intro h; exact hKL (by rw [h])
      rw [pairs_star hvu.ne, pairs_star hvw.ne, Finset.disjoint_singleton]
      intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
      · exact huw rfl
      · exact hvu.ne rfl
  covers := by
    rw [Finset.union_biUnion]
    have h1 : (Q.pieces.image (fun K => K.image (Subtype.val : {u : V | u ≠ v} → V))).biUnion pairs
        = G.edgeFinset.filter (fun e => v ∉ e) := by
      rw [Finset.image_biUnion, biUnion_pairs_lift]
    rw [h1, starPieces_covers, Finset.union_comm,
      Finset.filter_union_filter_not_eq (fun e => v ∈ e) G.edgeFinset]

@[simp] theorem liftPartition_size (Q : CliquePartition (G.induce {u : V | u ≠ v})) :
    (liftPartition G v Q).size
      ≤ Q.size + G.degree v := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
  · exact Finset.card_image_le
  · exact le_trans Finset.card_image_le (le_of_eq (G.card_neighborFinset_eq_degree v))

/-- **Coste del astro.**  De una partición de `G − v` de orden `≤ r` (con `2 ≤ r`) sale una de
`G` de orden `≤ r` cuyo tamaño excede al de aquélla en a lo sumo `deg v`.  No hace falta que `G`
sea cordal ni que `v` sea simplicial. -/
theorem exists_cliquePartition_of_delete_vertex {r : ℕ} (hr : 2 ≤ r)
    (Q : CliquePartition (G.induce {u : V | u ≠ v})) (hQ : Q.OrderAtMost r) :
    ∃ P : CliquePartition G, P.OrderAtMost r ∧ P.size ≤ Q.size + G.degree v := by
  refine ⟨liftPartition G v Q, ?_, liftPartition_size G v Q⟩
  intro K hK
  rcases Finset.mem_union.1 hK with hK | hK
  · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact hQ K' hK'
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hK
    have hvu : G.Adj v u := by simpa using hu
    rw [Finset.card_insert_of_notMem (by simp [hvu.ne]), Finset.card_singleton]
    exact hr

end Lift

/-! ## 3. La cota aguda y el paso inductivo -/

/-- **La cota aguda en orden `n`**: todo cordal de orden `n` tiene una partición en cliques de
orden `≤ 4` con a lo sumo `M(n) = ⌊n(n+1)/6⌋` piezas. -/
def SharpBoundAt (n : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n → G.IsChordal →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n

/-- El caso base: en orden `0` no hay aristas. -/
theorem sharpBoundAt_zero : SharpBoundAt.{u} 0 := by
  intro V _ _ G _ hcard _
  have hempty : IsEmpty V := Fintype.card_eq_zero_iff.1 hcard
  refine ⟨⟨∅, by simp, by simp, by simp, ?_⟩, by simp [CliquePartition.OrderAtMost], by
    simp [CliquePartition.size, targetSize]⟩
  rw [Finset.biUnion_empty]
  symm
  refine Finset.eq_empty_of_forall_notMem (fun e he => ?_)
  induction e using Sym2.ind with
  | _ x _ => exact hempty.elim x

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Cardinal del grafo borrado. -/
theorem card_delete (v : V) : Fintype.card {u : V | u ≠ v} = Fintype.card V - 1 := by
  simp [Set.coe_setOf, Fintype.card_subtype_compl]

/-- **Paso inductivo por grado pequeño.**  Si vale la cota aguda en orden `n` y `G` es cordal de
orden `n+1` con un vértice de grado `≤ M(n+1) − M(n)`, entonces `G` cumple la cota aguda. -/
theorem sharpBound_of_degree_le {n : ℕ} (hn : SharpBoundAt.{u} n) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard : Fintype.card V = n + 1) (hG : G.IsChordal) (v : V)
    (hdeg : G.degree v ≤ targetSize (n + 1) - targetSize n) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize (n + 1) := by
  classical
  obtain ⟨Q, hQ4, hQsize⟩ :=
    hn {u : V | u ≠ v} (G.induce {u : V | u ≠ v}) (by rw [card_delete v, hcard]; omega)
      (hG.induce _)
  obtain ⟨P, hP4, hPsize⟩ :=
    exists_cliquePartition_of_delete_vertex G v (by norm_num) Q hQ4
  refine ⟨P, hP4, ?_⟩
  calc P.size ≤ Q.size + G.degree v := hPsize
    _ ≤ targetSize n + (targetSize (n + 1) - targetSize n) := Nat.add_le_add hQsize hdeg
    _ = targetSize (n + 1) := targetSize_add_jump n

/-- **La reducción simplicial, en la forma pedida.**  El vértice simplicial de grado pequeño
cierra el paso inductivo.

La hipótesis `hv : G.IsSimplicial v` se deja explícita porque es la del enunciado del encargo,
pero conviene decir que **este paso no la necesita**: el levantamiento cuesta `deg v` piezas para
cualquier vértice.  La simplicialidad es lo que garantiza, vía Dirac, que tal vértice *exista*, y
es lo que se explota en el refinamiento del coste del astro
(`PaperIV/SimplicialReductionRefined.lean`). -/
theorem sharpBound_of_isSimplicial_degree_le {n : ℕ} (hn : SharpBoundAt.{u} n) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard : Fintype.card V = n + 1) (hG : G.IsChordal) (v : V)
    (hv : G.IsSimplicial v) (hdeg : G.degree v ≤ targetSize (n + 1) - targetSize n) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize (n + 1) := by
  have _hclique : G.IsClique (G.neighborSet v) := hv
  exact sharpBound_of_degree_le hn G hcard hG v hdeg

/-! ## 4. La reducción al régimen de grado simplicial grande -/

/-- **La reducción.**  Si vale la cota aguda en orden `n` y se sabe tratar los cordales de orden
`n+1` en los que *todo* vértice simplicial tiene grado `> M(n+1) − M(n)`, entonces vale la cota
aguda en orden `n+1`. -/
theorem sharpBoundAt_succ_of_largeSimplicialDegree {n : ℕ} (hn : SharpBoundAt.{u} n)
    (hbig : ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W = n + 1 → H.IsChordal →
      (∀ w : W, H.IsSimplicial w → targetSize (n + 1) - targetSize n < H.degree w) →
        ∃ Q : CliquePartition H, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize (n + 1)) :
    SharpBoundAt.{u} (n + 1) := by
  classical
  intro W _ _ H _ hcard hH
  by_cases hsmall : ∃ w : W, H.IsSimplicial w ∧ H.degree w ≤ targetSize (n + 1) - targetSize n
  · obtain ⟨w, hw, hdeg⟩ := hsmall
    exact sharpBound_of_isSimplicial_degree_le hn H hcard hH w hw hdeg
  · push_neg at hsmall
    exact hbig W H hcard hH (fun w hw => hsmall w hw)

/-- Un vértice simplicial de grado `d` da una clique de orden `d+1`. -/
theorem card_clique_of_isSimplicial (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hv : G.IsSimplicial v) :
    G.IsClique (insert v (G.neighborFinset v) : Finset V) ∧
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
  · rw [Finset.card_insert_of_notMem (by simp), G.card_neighborFinset_eq_degree]

/-- **El régimen de clique grande.**  Si todo vértice simplicial de un cordal no vacío tiene
grado `> Δ`, entonces su número de clique supera `Δ + 1`.  (Dirac: el vértice simplicial
existe.) -/
theorem cliqueNum_gt_of_all_isSimplicial_degree_gt [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsChordal) {Δ : ℕ}
    (hbig : ∀ v : V, G.IsSimplicial v → Δ < G.degree v) : Δ + 1 < G.cliqueNum := by
  obtain ⟨v, hv⟩ := hG.exists_isSimplicial
  obtain ⟨hclique, hcard⟩ := card_clique_of_isSimplicial G hv
  have h1 : (insert v (G.neighborFinset v)).card ≤ G.cliqueNum :=
    SimpleGraph.IsClique.card_le_cliqueNum (tc := hclique)
  have h2 := hbig v hv
  omega

/-- **Corolario: la conjetura se reduce al régimen de clique grande.**  Basta demostrar la cota
aguda para los cordales `G` de orden `n+1` con `ω(G) > M(n+1) − M(n) + 1 ≈ n/3`; el resto sale
por la reducción simplicial. -/
theorem sharpBoundAt_of_largeCliqueRegime
    (H : ∀ (n : ℕ) (W : Type u) [Fintype W] [DecidableEq W] (K : SimpleGraph W)
      [DecidableRel K.Adj], Fintype.card W = n + 1 → K.IsChordal →
      targetSize (n + 1) - targetSize n + 1 < K.cliqueNum →
        ∃ Q : CliquePartition K, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize (n + 1)) :
    ∀ n : ℕ, SharpBoundAt.{u} n := by
  intro n
  induction n with
  | zero => exact sharpBoundAt_zero
  | succ m ih =>
      refine sharpBoundAt_succ_of_largeSimplicialDegree ih ?_
      intro W _ _ K _ hcard hK hdeg
      haveI : Nonempty W := Fintype.card_pos_iff.1 (by omega)
      exact H m W K hcard hK (cliqueNum_gt_of_all_isSimplicial_degree_gt K hK hdeg)

end PaperIV.SimplicialReduction
