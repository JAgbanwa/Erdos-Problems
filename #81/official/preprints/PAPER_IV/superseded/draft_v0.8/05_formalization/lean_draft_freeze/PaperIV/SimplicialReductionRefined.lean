import PaperIV.SimplicialReduction

/-!
# Afinar el coste del astro, y por qué la hipótesis inductiva reforzada no se mantiene

La reducción simplicial básica (`PaperIV/SimplicialReduction.lean`) cobra `d = deg v` piezas por
el astro de un vértice simplicial `v`.  Es tosco: si `v` es simplicial, `{v} ∪ N(v)` es una clique,
así que una pieza de `G − v` **contenida en `N(v)`** de tamaño `2` o `3` se puede *ascender*
absorbiendo a `v`: la pieza `K` se sustituye por `insert v K`, que sigue siendo una clique de
orden `≤ 4`, y el ascenso cubre `|K|` aristas del astro **sin pagar ninguna pieza nueva**.

## Resultados principales

* `PaperIV.SimplicialReductionRefined.exists_cliquePartition_upgraded` — la versión con ascensos:
  dada una partición `Q` de `G − v` y un **troceado** de `N(v)` en trozos disjuntos de tamaño
  `≤ 3`, donde todo trozo de tamaño `≥ 2` es (la subida de) una pieza de `Q`, se obtiene una
  partición `P` de `G` de orden `≤ 4` con

  ```text
  P.size + ∑ (tamaños de los trozos grandes) ≤ Q.size + deg v.
  ```

  Con trozos todos singulares se recupera el coste `d`; con trozos todos de tamaño `3` el astro
  **sale gratis** (`exists_cliquePartition_freeStar`).

* `PaperIV.SimplicialReductionRefined.StrongLoosePieceHypothesis` — la hipótesis inductiva
  reforzada del encargo, en su forma más débil posible: para todo cordal y toda arista suya,
  existe una partición **óptima** (entre las de orden `≤ 4`) que contiene esa arista como pieza
  `K₂` suelta.

* `PaperIV.SimplicialReductionRefined.not_strongLoosePieceHypothesis` — **es falsa**, con
  contraejemplo explícito: el triángulo `K₃`.  Su única partición óptima es la pieza `{0,1,2}`,
  de tamaño `1`; cualquier partición que contenga `{0,1}` como pieza tiene tamaño `≥ 2`.

## Dónde falla exactamente el refuerzo

El mecanismo de ascenso es correcto y está cuantificado arriba: el ahorro es exactamente la suma
de los tamaños de los trozos ascendidos.  Lo que **no** se puede mantener por inducción es la
premisa que lo alimenta, a saber, que la partición óptima de `G − v` se pueda elegir con un
emparejamiento (o una descomposición en triángulos) prescrito dentro de `N(v)` como piezas
sueltas.  El contraejemplo es mínimo y decisivo: en `G = K₄` con `v` simplicial, `G − v = K₃` y
`N(v)` es ese triángulo; la partición óptima de `K₃` es la pieza `{a,b,c}` y tiene tamaño `1`,
mientras que forzar la arista `{a,b}` como pieza suelta obliga a tamaño `3`.  Forzar el
emparejamiento cuesta `+2` piezas en `G − v` y el ascenso sólo devuelve `1`: el balance es peor
que el del astro tosco.

Dicho de otro modo: el coste real del astro no es una función del grado, sino de la *deficiencia*
`c₄(G−v ; piezas prescritas en N(v)) − c₄(G−v)`, y esa deficiencia puede comerse todo el ahorro.
Ése es el obstáculo del rango intermedio: sin control estructural adicional sobre cómo se cruzan
las particiones óptimas de `G − v` con `N(v)`, la constante del astro no baja de `d`.
-/

namespace PaperIV.SimplicialReductionRefined

open Finset SimpleGraph PaperIV.FarRounding PaperIV.SimplicialReduction

/-! ## 1. Dos lemas sobre soportes de aristas -/

section Pairs

variable {V : Type*} [DecidableEq V]

/-- El soporte de aristas de `insert v C`, con `v ∉ C`, son las aristas de `C` más el astro. -/
theorem pairs_insert {v : V} {C : Finset V} (hv : v ∉ C) :
    pairs (insert v C) = pairs C ∪ C.image (fun u => s(v, u)) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mk_mem_pairs, Finset.mem_union, Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact Or.inr ⟨y, hy, rfl⟩
      · rcases hy with rfl | hy
        · exact Or.inr ⟨x, hx, Sym2.eq_swap⟩
        · exact Or.inl ⟨hx, hy, hxy⟩
    · rintro (⟨hx, hy, hxy⟩ | ⟨u, hu, heq⟩)
      · exact ⟨Or.inr hx, Or.inr hy, hxy⟩
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Or.inl rfl, Or.inr hu, fun h => hv (h ▸ hu)⟩
        · exact ⟨Or.inr hu, Or.inl rfl, fun h => hv (h ▸ hu)⟩

/-- Un conjunto con a lo sumo un vértice no tiene aristas. -/
theorem pairs_eq_empty_of_card_le_one {C : Finset V} (h : C.card ≤ 1) : pairs C = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun e he => ?_)
  induction e using Sym2.ind with
  | _ x y =>
    rw [mk_mem_pairs] at he
    have : 2 ≤ C.card := Finset.one_lt_card.2 ⟨x, he.1, y, he.2.1, he.2.2⟩
    omega

/-- Dos vértices de una arista del soporte de `C` están en `C`. -/
theorem not_mem_pairs_of_not_mem {C : Finset V} {z : V} (hz : z ∉ C) {e : Sym2 V}
    (he : e ∈ pairs C) : z ∉ e := by
  intro hmem
  exact hz ((mem_pairs.1 he).1 z hmem)

end Pairs

/-! ## 2. El levantamiento con ascensos -/

section Upgrade

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)

/-- **Levantamiento con ascensos.**  `chunks` es un troceado de `N(v)` en trozos disjuntos no
vacíos de tamaño `≤ 3`, cada trozo de tamaño `≥ 2` siendo la subida de una pieza de `Q`.  Cada
trozo `C` produce la pieza `insert v C`: los trozos de tamaño `1` son las piezas `K₂` del astro
tosco, y los de tamaño `2` ó `3` ascienden una pieza ya existente y cubren sus aristas del astro
gratis. -/
theorem exists_cliquePartition_upgraded (hv : G.IsSimplicial v)
    (Q : CliquePartition (G.induce {u : V | u ≠ v})) (hQ4 : Q.OrderAtMost 4)
    (chunks : Finset (Finset V))
    (hne : ∀ C ∈ chunks, C.Nonempty)
    (hle : ∀ C ∈ chunks, C.card ≤ 3)
    (hdisj : ∀ C ∈ chunks, ∀ D ∈ chunks, C ≠ D → Disjoint C D)
    (hcov : chunks.biUnion (fun C => C) = G.neighborFinset v)
    (hpiece : ∀ C ∈ chunks, 2 ≤ C.card →
      ∃ K ∈ Q.pieces, K.image (Subtype.val : {u : V | u ≠ v} → V) = C) :
    ∃ P : CliquePartition G, P.OrderAtMost 4 ∧
      P.size + (Q.pieces.filter
          (fun K => K.image (Subtype.val : {u : V | u ≠ v} → V) ∈ chunks)).card
        ≤ Q.size + chunks.card := by
  classical
  set val : {u : V | u ≠ v} → V := Subtype.val with hval
  set F : Finset (Finset {u : V | u ≠ v}) :=
    Q.pieces.filter (fun K => K.image val ∈ chunks) with hF
  -- hechos básicos sobre los trozos
  have hsub : ∀ C ∈ chunks, ∀ u ∈ C, G.Adj v u := by
    intro C hC u hu
    have : u ∈ chunks.biUnion (fun C => C) := Finset.mem_biUnion.2 ⟨C, hC, hu⟩
    rw [hcov] at this
    simpa using this
  have hvnot : ∀ C ∈ chunks, v ∉ C := by
    intro C hC hmem
    exact (hsub C hC v hmem).ne rfl
  have hFsub : F ⊆ Q.pieces := Finset.filter_subset _ _
  -- toda arista de un trozo viene de una pieza de `F`
  have hfromF : ∀ C ∈ chunks, ∀ e ∈ pairs C, ∃ K ∈ F, K.image val = C := by
    intro C hC e he
    have hcard : 2 ≤ C.card := by
      by_contra h
      rw [pairs_eq_empty_of_card_le_one (by omega)] at he
      exact absurd he (Finset.notMem_empty e)
    obtain ⟨K, hK, hKC⟩ := hpiece C hC hcard
    exact ⟨K, Finset.mem_filter.2 ⟨hK, by rw [hKC]; exact hC⟩, hKC⟩
  -- las piezas
  refine ⟨⟨(Q.pieces \ F).image (fun K => K.image val) ∪ chunks.image (fun C => insert v C),
    ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- cliques
    intro K hK a ha b hb hab
    rcases Finset.mem_union.1 hK with hK | hK
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      have := Q.isClique K' (Finset.mem_sdiff.1 hK').1 a' ha' b' hb' (fun h => hab (by rw [h]))
      simpa using this
    · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hK
      rcases Finset.mem_insert.1 ha with hav | ha
      · rcases Finset.mem_insert.1 hb with hbv | hb
        · exact absurd (hav.trans hbv.symm) hab
        · rw [hav]; exact hsub C hC b hb
      · rcases Finset.mem_insert.1 hb with hbv | hb
        · rw [hbv]; exact (hsub C hC a ha).symm
        · exact hv (by simpa using hsub C hC a ha) (by simpa using hsub C hC b hb) hab
  · -- tamaño ≥ 2
    intro K hK
    rcases Finset.mem_union.1 hK with hK | hK
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact Q.two_le_card K' (Finset.mem_sdiff.1 hK').1
    · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hK
      rw [Finset.card_insert_of_notMem (hvnot C hC)]
      have := Finset.card_pos.2 (hne C hC)
      omega
  · -- aristas disjuntas
    intro K hK L hL hKL
    rcases Finset.mem_union.1 hK with hK | hK <;> rcases Finset.mem_union.1 hL with hL | hL
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hL
      have hne' : K' ≠ L' := fun h => hKL (by rw [h])
      rw [pairs_image Subtype.val_injective, pairs_image Subtype.val_injective]
      exact (Finset.disjoint_image (Sym2.map.injective Subtype.val_injective)).2
        (Q.edgeDisjoint K' (Finset.mem_sdiff.1 hK').1 L' (Finset.mem_sdiff.1 hL').1 hne')
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hL
      refine Finset.disjoint_left.2 (fun e he he' => ?_)
      rw [pairs_insert (hvnot C hC), Finset.mem_union] at he'
      rcases he' with he' | he'
      · obtain ⟨L', hL'F, hL'C⟩ := hfromF C hC e he'
        have hne' : K' ≠ L' := by
          intro h; exact (Finset.mem_sdiff.1 hK').2 (h ▸ hL'F)
        have hdis := Q.edgeDisjoint K' (Finset.mem_sdiff.1 hK').1 L'
          (hFsub hL'F) hne'
        rw [← hL'C, pairs_image Subtype.val_injective] at he'
        rw [pairs_image Subtype.val_injective] at he
        exact (Finset.disjoint_left.1
          ((Finset.disjoint_image (Sym2.map.injective Subtype.val_injective)).2 hdis) he) he'
      · obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 he'
        exact not_mem_pairs_image_val he (by simp)
    · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 hL
      refine Finset.disjoint_right.2 (fun e he he' => ?_)
      rw [pairs_insert (hvnot C hC), Finset.mem_union] at he'
      rcases he' with he' | he'
      · obtain ⟨K', hK'F, hK'C⟩ := hfromF C hC e he'
        have hne' : K' ≠ L' := by
          intro h; exact (Finset.mem_sdiff.1 hL').2 (h ▸ hK'F)
        have hdis := Q.edgeDisjoint K' (hFsub hK'F) L' (Finset.mem_sdiff.1 hL').1 hne'
        rw [← hK'C, pairs_image Subtype.val_injective] at he'
        rw [pairs_image Subtype.val_injective] at he
        exact (Finset.disjoint_left.1
          ((Finset.disjoint_image (Sym2.map.injective Subtype.val_injective)).2 hdis) he') he
      · obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 he'
        exact not_mem_pairs_image_val he (by simp)
    · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hK
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 hL
      have hCD : C ≠ D := by
        intro h; exact hKL (by rw [h])
      have hdisCD := hdisj C hC D hD hCD
      refine Finset.disjoint_left.2 (fun e he he' => ?_)
      rw [pairs_insert (hvnot C hC), Finset.mem_union] at he
      rw [pairs_insert (hvnot D hD), Finset.mem_union] at he'
      rcases he with he | he <;> rcases he' with he' | he'
      · obtain ⟨K', hK'F, hK'C⟩ := hfromF C hC e he
        obtain ⟨L', hL'F, hL'D⟩ := hfromF D hD e he'
        have hne' : K' ≠ L' := by
          intro h; exact hCD (by rw [← hK'C, ← hL'D, h])
        have hdis := Q.edgeDisjoint K' (hFsub hK'F) L' (hFsub hL'F) hne'
        rw [← hK'C, pairs_image Subtype.val_injective] at he
        rw [← hL'D, pairs_image Subtype.val_injective] at he'
        exact (Finset.disjoint_left.1
          ((Finset.disjoint_image (Sym2.map.injective Subtype.val_injective)).2 hdis) he) he'
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he'
        exact not_mem_pairs_of_not_mem (hvnot C hC) he (by simp)
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
        exact not_mem_pairs_of_not_mem (hvnot D hD) he' (by simp)
      · obtain ⟨u, hu, hue⟩ := Finset.mem_image.1 he
        obtain ⟨w, hw, hwe⟩ := Finset.mem_image.1 he'
        have heq : s(v, w) = s(v, u) := by rw [hwe, hue]
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, hwu⟩ | ⟨hvu, _⟩
        · exact (Finset.disjoint_left.1 hdisCD hu) (hwu ▸ hw)
        · exact (hsub C hC u hu).ne hvu
  · -- cubrimiento
    rw [Finset.union_biUnion, Finset.image_biUnion, Finset.image_biUnion]
    have hstar : (chunks.biUnion fun C => C.image (fun u => s(v, u)))
        = G.edgeFinset.filter (fun e => v ∈ e) := by
      rw [← image_star_edges, ← hcov, Finset.biUnion_image]
    have hchunkpairs : (chunks.biUnion fun C => pairs C)
        = F.biUnion (fun K => pairs (K.image val)) := by
      ext e
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨C, hC, he⟩
        obtain ⟨K, hKF, hKC⟩ := hfromF C hC e he
        exact ⟨K, hKF, by rw [hKC]; exact he⟩
      · rintro ⟨K, hKF, he⟩
        exact ⟨K.image val, (Finset.mem_filter.1 hKF).2, he⟩
    have hsplit : (Q.pieces \ F).biUnion (fun K => pairs (K.image val))
        ∪ F.biUnion (fun K => pairs (K.image val))
        = Q.pieces.biUnion (fun K => pairs (K.image val)) := by
      rw [← Finset.union_biUnion, Finset.sdiff_union_of_subset hFsub]
    calc ((Q.pieces \ F).biUnion fun K => pairs (K.image val))
          ∪ (chunks.biUnion fun C => pairs (insert v C))
        = ((Q.pieces \ F).biUnion fun K => pairs (K.image val))
          ∪ ((chunks.biUnion fun C => pairs C)
            ∪ (chunks.biUnion fun C => C.image (fun u => s(v, u)))) := by
          rw [← Finset.biUnion_union]
          exact congrArg _ (Finset.biUnion_congr rfl
            (fun C hC => pairs_insert (hvnot C hC)))
      _ = (((Q.pieces \ F).biUnion fun K => pairs (K.image val))
            ∪ (chunks.biUnion fun C => pairs C))
          ∪ (chunks.biUnion fun C => C.image (fun u => s(v, u))) := by
          rw [Finset.union_assoc]
      _ = G.edgeFinset.filter (fun e => v ∉ e) ∪ G.edgeFinset.filter (fun e => v ∈ e) := by
          rw [hstar, hchunkpairs, hsplit, biUnion_pairs_lift]
      _ = G.edgeFinset := by
          rw [Finset.union_comm, Finset.filter_union_filter_not_eq (fun e => v ∈ e) G.edgeFinset]
  · -- orden ≤ 4
    intro K hK
    rcases Finset.mem_union.1 hK with hK | hK
    · obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 hK
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact hQ4 K' (Finset.mem_sdiff.1 hK').1
    · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hK
      rw [Finset.card_insert_of_notMem (hvnot C hC)]
      have := hle C hC
      omega
  · -- contabilidad
    have hcard : ((Q.pieces \ F).image (fun K => K.image val)
        ∪ chunks.image (fun C => insert v C)).card
        ≤ (Q.pieces \ F).card + chunks.card :=
      le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have hsd : (Q.pieces \ F).card + F.card = Q.pieces.card :=
      Finset.card_sdiff_add_card_eq_card hFsub
    show ((Q.pieces \ F).image (fun K => K.image val)
        ∪ chunks.image (fun C => insert v C)).card + F.card ≤ Q.size + chunks.card
    unfold CliquePartition.size
    omega

/-- **El coste del astro, afinado.**  Con el mismo troceado, el ahorro respecto del coste tosco
`deg v` es exactamente la suma de los tamaños de los trozos ascendidos. -/
theorem exists_cliquePartition_upgraded_cost (hv : G.IsSimplicial v)
    (Q : CliquePartition (G.induce {u : V | u ≠ v})) (hQ4 : Q.OrderAtMost 4)
    (chunks : Finset (Finset V))
    (hne : ∀ C ∈ chunks, C.Nonempty)
    (hle : ∀ C ∈ chunks, C.card ≤ 3)
    (hdisj : ∀ C ∈ chunks, ∀ D ∈ chunks, C ≠ D → Disjoint C D)
    (hcov : chunks.biUnion (fun C => C) = G.neighborFinset v)
    (hpiece : ∀ C ∈ chunks, 2 ≤ C.card →
      ∃ K ∈ Q.pieces, K.image (Subtype.val : {u : V | u ≠ v} → V) = C) :
    ∃ P : CliquePartition G, P.OrderAtMost 4 ∧
      P.size + ∑ C ∈ chunks.filter (fun C => 2 ≤ C.card), C.card ≤ Q.size + G.degree v := by
  classical
  obtain ⟨P, hP4, hPsize⟩ :=
    exists_cliquePartition_upgraded G v hv Q hQ4 chunks hne hle hdisj hcov hpiece
  refine ⟨P, hP4, ?_⟩
  set F : Finset (Finset {u : V | u ≠ v}) :=
    Q.pieces.filter (fun K => K.image (Subtype.val : {u : V | u ≠ v} → V) ∈ chunks) with hFdef
  set big : Finset (Finset V) := chunks.filter (fun C => 2 ≤ C.card) with hbigdef
  -- los trozos parten `N(v)`
  have hsum : ∑ C ∈ chunks, C.card = G.degree v := by
    have hpair : (↑chunks : Set (Finset V)).PairwiseDisjoint (fun C => C) := by
      intro C hC D hD hCD
      exact hdisj C (by simpa using hC) D (by simpa using hD) hCD
    have := Finset.card_biUnion hpair
    rw [hcov, G.card_neighborFinset_eq_degree] at this
    exact this.symm
  -- `F` está en biyección con los trozos grandes
  have hFcard : F.card = big.card := by
    refine Finset.card_bij (fun K _ => K.image (Subtype.val : {u : V | u ≠ v} → V)) ?_ ?_ ?_
    · intro K hK
      have hK' := Finset.mem_filter.1 hK
      refine Finset.mem_filter.2 ⟨hK'.2, ?_⟩
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact Q.two_le_card K hK'.1
    · intro K₁ _ K₂ _ h
      exact Finset.image_injective Subtype.val_injective h
    · intro C hC
      have hC' := Finset.mem_filter.1 hC
      obtain ⟨K, hK, hKC⟩ := hpiece C hC'.1 hC'.2
      exact ⟨K, Finset.mem_filter.2 ⟨hK, by rw [hKC]; exact hC'.1⟩, hKC⟩
  -- los trozos pequeños son singletons
  have hsmall : ∑ C ∈ chunks.filter (fun C => ¬ 2 ≤ C.card), C.card
      = (chunks.filter (fun C => ¬ 2 ≤ C.card)).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl (fun C hC => ?_)
    have hC' := Finset.mem_filter.1 hC
    have h1 := Finset.card_pos.2 (hne C hC'.1)
    omega
  have hsplit : ∑ C ∈ big, C.card + ∑ C ∈ chunks.filter (fun C => ¬ 2 ≤ C.card), C.card
      = ∑ C ∈ chunks, C.card :=
    Finset.sum_filter_add_sum_filter_not chunks (fun C => 2 ≤ C.card) (fun C => C.card)
  have hcards : big.card + (chunks.filter (fun C => ¬ 2 ≤ C.card)).card = chunks.card :=
    Finset.card_filter_add_card_filter_not (s := chunks) (fun C => 2 ≤ C.card)
  omega

/-- **El astro gratis.**  Si `N(v)` se parte en triángulos que ya son piezas de la partición de
`G − v`, cada uno asciende a un `K₄` y el astro no cuesta **ninguna** pieza. -/
theorem exists_cliquePartition_freeStar (hv : G.IsSimplicial v)
    (Q : CliquePartition (G.induce {u : V | u ≠ v})) (hQ4 : Q.OrderAtMost 4)
    (chunks : Finset (Finset V))
    (hcard3 : ∀ C ∈ chunks, C.card = 3)
    (hdisj : ∀ C ∈ chunks, ∀ D ∈ chunks, C ≠ D → Disjoint C D)
    (hcov : chunks.biUnion (fun C => C) = G.neighborFinset v)
    (hpiece : ∀ C ∈ chunks, ∃ K ∈ Q.pieces,
      K.image (Subtype.val : {u : V | u ≠ v} → V) = C) :
    ∃ P : CliquePartition G, P.OrderAtMost 4 ∧ P.size ≤ Q.size := by
  classical
  obtain ⟨P, hP4, hPcost⟩ :=
    exists_cliquePartition_upgraded_cost G v hv Q hQ4 chunks
      (fun C hC => Finset.card_pos.1 (by rw [hcard3 C hC]; norm_num))
      (fun C hC => le_of_eq (hcard3 C hC)) hdisj hcov (fun C hC _ => hpiece C hC)
  refine ⟨P, hP4, ?_⟩
  have hfilter : chunks.filter (fun C => 2 ≤ C.card) = chunks :=
    Finset.filter_true_of_mem (fun C hC => by rw [hcard3 C hC]; norm_num)
  have hsum : ∑ C ∈ chunks, C.card = G.degree v := by
    have hpair : (↑chunks : Set (Finset V)).PairwiseDisjoint (fun C => C) := by
      intro C hC D hD hCD
      exact hdisj C (by simpa using hC) D (by simpa using hD) hCD
    have := Finset.card_biUnion hpair
    rw [hcov, G.card_neighborFinset_eq_degree] at this
    exact this.symm
  rw [hfilter, hsum] at hPcost
  omega

end Upgrade

/-! ## 3. La hipótesis inductiva reforzada es falsa -/

section Counterexample

/-- Todo grafo con a lo sumo tres vértices es cordal: no hay ciclos de longitud `≥ 4`. -/
theorem chordal_of_card_le_three {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 3) : G.IsChordal := by
  intro x c hc hlen
  exfalso
  have h1 : c.support.tail.Nodup := hc.support_nodup
  have h2 : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  have h3 : c.support.tail.length ≤ Fintype.card V := h1.length_le_card
  omega

/-- La partición óptima del triángulo: una sola pieza. -/
def triangleK3 : CliquePartition (⊤ : SimpleGraph (Fin 3)) where
  pieces := {Finset.univ}
  isClique := by decide
  two_le_card := by decide
  edgeDisjoint := by decide
  covers := by decide

@[simp] theorem triangleK3_size : triangleK3.size = 1 := by decide

theorem triangleK3_orderAtMost : triangleK3.OrderAtMost 4 := by
  intro K hK
  have hKu : K = Finset.univ := Finset.mem_singleton.1 hK
  subst hKu
  decide

/-- Forzar una arista del triángulo como pieza `K₂` suelta cuesta al menos dos piezas. -/
theorem two_le_size_of_loose_pair (Q : CliquePartition (⊤ : SimpleGraph (Fin 3)))
    (h01 : ({0, 1} : Finset (Fin 3)) ∈ Q.pieces) : 2 ≤ Q.size := by
  have hedge : s((0 : Fin 3), 2) ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset := by decide
  rw [← Q.covers] at hedge
  obtain ⟨L, hL, hLmem⟩ := Finset.mem_biUnion.1 hedge
  have hne : L ≠ ({0, 1} : Finset (Fin 3)) := by
    intro h
    rw [h] at hLmem
    revert hLmem
    decide
  exact Finset.one_lt_card.2 ⟨L, hL, {0, 1}, h01, hne⟩

/-- **La hipótesis inductiva reforzada**, en la forma más débil que aún serviría para el
refinamiento: para todo cordal y toda arista suya existe una partición de tamaño mínimo (entre
las de orden `≤ 4`) que contiene esa arista como pieza `K₂` suelta.

Es la premisa que alimentaría a `exists_cliquePartition_upgraded` con un emparejamiento prescrito
dentro de `N(v)`. -/
def StrongLoosePieceHypothesis : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
    H.IsChordal → ∀ a b : V, H.Adj a b →
      ∃ Q : CliquePartition H, ({a, b} : Finset V) ∈ Q.pieces ∧ Q.OrderAtMost 4 ∧
        ∀ R : CliquePartition H, R.OrderAtMost 4 → Q.size ≤ R.size

/-- **La hipótesis reforzada es falsa.**  Contraejemplo: el triángulo `K₃`, que es exactamente
`K₄ − v` para `v` simplicial, con `N(v)` igual a ese triángulo.  Su partición óptima es la pieza
`{0,1,2}`, de tamaño `1`; toda partición que contenga `{0,1}` como pieza tiene tamaño `≥ 2`.
Forzar el emparejamiento cuesta más piezas en `G − v` de las que devuelve el ascenso del astro. -/
theorem not_strongLoosePieceHypothesis : ¬ StrongLoosePieceHypothesis := by
  intro h
  obtain ⟨Q, hQmem, _, hQmin⟩ :=
    h (Fin 3) (⊤ : SimpleGraph (Fin 3)) (chordal_of_card_le_three _ (by simp)) 0 1 (by decide)
  have h2 : 2 ≤ Q.size := two_le_size_of_loose_pair Q hQmem
  have h1 : Q.size ≤ 1 := by
    have := hQmin triangleK3 triangleK3_orderAtMost
    simpa using this
  omega

end Counterexample

end PaperIV.SimplicialReductionRefined
