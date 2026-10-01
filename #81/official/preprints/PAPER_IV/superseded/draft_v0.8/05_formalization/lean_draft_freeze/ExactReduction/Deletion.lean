import PaperIV.FarRounding
import PaperIV.ChordalStructure

/-!
# Borrado de un vértice: el paso elemental de una reducción integral exacta

`deleteAt G v` es `G` sin las aristas incidentes a `v` (el vértice queda aislado, el tipo
de vértices no cambia; así la inducción no necesita transportar particiones a lo largo de
subtipos).

* `deleteAt_isChordal` — la cordalidad se conserva.
* `exists_cliquePartition_of_deleteAt` — **el paso de coste `deg(v)`**: toda partición de
  `deleteAt G v` se extiende a una de `G` añadiendo un `K₂` por arista incidente a `v`.

Con `ExactReduction.targetSize_sub_one` (`M(n) = M(n−1) + ⌊(n+1)/3⌋`) esto da el núcleo de
contraejemplo mínimo de `ExactReduction.MinimalKernel`.
-/

namespace ExactReduction

open PaperIV.FarRounding Finset

variable {V : Type*} [DecidableEq V]

/-- `G` sin las aristas incidentes a `v`. -/
def deleteAt (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ v ∧ b ≠ v
  symm := by
    rintro a b ⟨h, ha, hb⟩
    exact ⟨h.symm, hb, ha⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    DecidableRel (deleteAt G v).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a b ∧ a ≠ v ∧ b ≠ v))

@[simp] theorem deleteAt_adj {G : SimpleGraph V} {v a b : V} :
    (deleteAt G v).Adj a b ↔ G.Adj a b ∧ a ≠ v ∧ b ≠ v := Iff.rfl

theorem deleteAt_le (G : SimpleGraph V) (v : V) : deleteAt G v ≤ G := fun _ _ h => h.1

theorem deleteAt_isolated (G : SimpleGraph V) (v : V) (w : V) : ¬ (deleteAt G v).Adj v w := by
  rintro ⟨-, hv, -⟩
  exact hv rfl

/-! ## 1. La cordalidad se conserva -/

private theorem walk_start_ne {H : SimpleGraph V} {v : V} (hv : ∀ w, ¬ H.Adj v w)
    {a b : V} (c : H.Walk a b) (hpos : 0 < c.length) : a ≠ v := by
  cases c with
  | nil => simp at hpos
  | cons h p => exact fun hav => hv _ (hav ▸ h)

private theorem walk_support_ne {H : SimpleGraph V} {v : V} (hv : ∀ w, ¬ H.Adj v w) :
    ∀ {a b : V} (c : H.Walk a b), a ≠ v → ∀ x ∈ c.support, x ≠ v := by
  intro a b c
  induction c with
  | nil =>
    intro ha x hx
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ ha
  | @cons a b' d h p ih =>
    intro ha x hx
    have hb' : b' ≠ v := fun hbv => hv a ((hbv ▸ h).symm)
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact ih hb' x hx

/-- Borrar las aristas de un vértice conserva la cordalidad. -/
theorem deleteAt_isChordal {G : SimpleGraph V} (hG : G.IsChordal) (v : V) :
    (deleteAt G v).IsChordal := by
  intro u c hc hlen
  have hv : ∀ w, ¬ (deleteAt G v).Adj v w := deleteAt_isolated G v
  have hu : u ≠ v := walk_start_ne hv c (by omega)
  have hsupp : ∀ x ∈ c.support, x ≠ v := walk_support_ne hv c hu
  let φ : deleteAt G v →g G := ⟨id, fun {a b} h => h.1⟩
  have hinj : Function.Injective φ := fun a b h => h
  obtain ⟨x, y, hx, hy, hadj, hchord⟩ :=
    hG (c.map φ) (hc.map hinj) (by rwa [SimpleGraph.Walk.length_map])
  rw [SimpleGraph.Walk.support_map] at hx hy
  simp only [List.mem_map] at hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨x', y', hx', hy', ⟨hadj, hsupp x' hx', hsupp y' hy'⟩, fun hmem => hchord ?_⟩
  rw [SimpleGraph.Walk.edges_map]
  exact List.mem_map.2 ⟨s(x', y'), hmem, rfl⟩

/-! ## 2. El paso de coste `deg(v)` -/

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {v : V}

private theorem not_mem_of_mem_pieces {Q' : CliquePartition (deleteAt G v)}
    {K : Finset V} (hK : K ∈ Q'.pieces) : v ∉ K := by
  intro hv
  obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (s := K) (a := v) (by
    have := Q'.two_le_card K hK; omega)
  exact deleteAt_isolated G v u (Q'.isClique K hK v hv u hu (Ne.symm huv))

/-- **Paso de borrado de un vértice.**  Una partición de `deleteAt G v` se completa a una
partición de `G` con `deg(v)` piezas `K₂` adicionales. -/
theorem exists_cliquePartition_of_deleteAt (Q' : CliquePartition (deleteAt G v))
    {r : ℕ} (hr : 2 ≤ r) (hQ' : Q'.OrderAtMost r) :
    ∃ Q : CliquePartition G, Q.OrderAtMost r ∧ Q.size ≤ Q'.size + G.degree v := by
  classical
  set New : Finset (Finset V) := (G.neighborFinset v).image (fun u => ({v, u} : Finset V))
    with hNew
  have hmemNew : ∀ L ∈ New, ∃ u, G.Adj v u ∧ L = {v, u} := by
    intro L hL
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hL
    exact ⟨u, by simpa using hu, rfl⟩
  have hpairsNew : ∀ u : V, G.Adj v u → pairs ({v, u} : Finset V) = {s(v, u)} := by
    intro u hu
    have : ({v, u} : Finset V) = (s(v, u) : Sym2 V).toFinset := by
      ext x; simp [Sym2.mem_toFinset, or_comm]
    rw [this, pairs_toFinset]
    simpa [Sym2.isDiag_iff_proj_eq] using hu.ne
  have hvnot : ∀ K ∈ Q'.pieces, v ∉ K := fun K hK => not_mem_of_mem_pieces hK
  refine ⟨⟨Q'.pieces ∪ New, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- las piezas son cliques de `G`
    intro K hK a ha b hb hab
    rcases Finset.mem_union.1 hK with hK | hK
    · exact (Q'.isClique K hK a ha b hb hab).1
    · obtain ⟨u, hu, rfl⟩ := hmemNew K hK
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hu
      · exact hu.symm
      · exact absurd rfl hab
  · -- cada pieza tiene al menos dos vértices
    intro K hK
    rcases Finset.mem_union.1 hK with hK | hK
    · exact Q'.two_le_card K hK
    · obtain ⟨u, hu, rfl⟩ := hmemNew K hK
      rw [Finset.card_pair hu.ne]
  · -- disyunción en aristas
    intro K hK L hL hKL
    have key : ∀ K ∈ Q'.pieces, ∀ L ∈ New, Disjoint (pairs K) (pairs L) := by
      intro K hK L hL
      obtain ⟨u, hu, rfl⟩ := hmemNew L hL
      rw [hpairsNew u hu, Finset.disjoint_singleton_right]
      intro hmem
      exact (hvnot K hK) (mk_mem_pairs.1 hmem).1
    rcases Finset.mem_union.1 hK with hK' | hK' <;> rcases Finset.mem_union.1 hL with hL' | hL'
    · exact Q'.edgeDisjoint K hK' L hL' hKL
    · exact key K hK' L hL'
    · exact (key L hL' K hK').symm
    · obtain ⟨u, hu, rfl⟩ := hmemNew K hK'
      obtain ⟨w, hw, rfl⟩ := hmemNew L hL'
      rw [hpairsNew u hu, hpairsNew w hw, Finset.disjoint_singleton]
      intro hEq
      refine hKL ?_
      rcases Sym2.eq_iff.1 hEq with ⟨-, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
      · exact absurd h2 hu.ne'
  · -- se cubre exactamente `E(G)`
    rw [biUnion_union_eq, Q'.covers]
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Finset.mem_biUnion, deleteAt_adj]
      constructor
      · rintro (⟨hab, -, -⟩ | ⟨L, hL, hmem⟩)
        · exact hab
        · obtain ⟨u, hu, rfl⟩ := hmemNew L hL
          rw [hpairsNew u hu, Finset.mem_singleton] at hmem
          rcases Sym2.eq_iff.1 hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hu
          · exact hu.symm
      · intro hab
        by_cases hav : a = v
        · subst hav
          refine Or.inr ⟨{a, b}, Finset.mem_image.2 ⟨b, by simpa using hab, rfl⟩, ?_⟩
          rw [hpairsNew b hab]
          exact Finset.mem_singleton_self _
        · by_cases hbv : b = v
          · subst hbv
            refine Or.inr ⟨{b, a}, Finset.mem_image.2 ⟨a, by simpa using hab.symm, rfl⟩, ?_⟩
            rw [hpairsNew a hab.symm, Finset.mem_singleton, Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
          · exact Or.inl ⟨hab, hav, hbv⟩
  · -- orden
    intro K hK
    rcases Finset.mem_union.1 hK with hK' | hK'
    · exact hQ' K hK'
    · obtain ⟨u, hu, rfl⟩ := hmemNew K hK'
      rw [Finset.card_pair hu.ne]
      exact hr
  · -- tamaño
    show (Q'.pieces ∪ New).card ≤ Q'.pieces.card + G.degree v
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
    refine le_trans Finset.card_image_le ?_
    rw [SimpleGraph.card_neighborFinset_eq_degree]

end ExactReduction
