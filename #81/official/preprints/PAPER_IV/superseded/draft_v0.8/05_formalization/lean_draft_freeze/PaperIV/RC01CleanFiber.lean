import PaperIV.RC01DeviationCleanup
import PaperIV.RC01CleanedSpreadPacking

/-!
# RC01: la fibra limpia literal de un patrón reducido

Este módulo instancia la limpieza de copias de `PaperIV.CopyCleanup` sobre las
fibras literales del grafo reducido, sin ninguna hipótesis abstracta.

* la fibra bruta de un patrón reducido `H : Finset P` es `profileFiber`: los
  items de `G` cuyo perfil de partes es exactamente `H` y que lo recorren
  transversalmente (un vértice por parte);
* las posiciones de raíz son los pares de partes `pq : Finset P`; la raíz de una
  copia en esa posición es su única arista que cruza `pq` (`rootEdge`);
* las raíces malas son literalmente `RC01DeviationCleanup.deviationBad` aplicado
  al conteo literal de la fibra bruta en esa posición (`rootCount`);
* la fibra limpia es literalmente `CopyCleanup.cleaned` de la fibra bruta con
  esas raíces malas, en **una sola pasada** sobre las tres posiciones de un `K₃`
  o las seis de un `K₄`.

Se demuestra todo lo que consume `RC01CleanedSpreadPacking.cleanedSpreadPacking`:
contención en `items G`, la pertenencia a `servingT` de cualquier patrón con una
copia por `e`, la desigualdad física de dispersión con presupuesto
`(1+u) · A_σ · pairVolume`, y la retención `1-v` explícita a partir de las tres
(o seis) familias malas y de `CopyCleanup.card_removed_le`.
-/

namespace PaperIV.RC01CleanFiber

open Finset
open MixedRounding
open PaperIV.PatternTransfer
open PaperIV.RootedCountingBridge
open PaperIV.CopyCleanup
open PaperIV.RC01DeviationCleanup
open PaperIV.RC01CanonicalFractional
open PaperIV.RC01CanonicalNormalization

variable {V P : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Elección canónica de una raíz -/

/-- Elección canónica de un elemento de un conjunto finito de recursos.  Cuando
el conjunto es vacío se devuelve un par diagonal, que nunca es un recurso
físico. -/
noncomputable def pickEdge (s : Finset (Sym2 V)) : Sym2 V :=
  if h : s.Nonempty then h.choose else s(Classical.arbitrary V, Classical.arbitrary V)

omit [Fintype V] [DecidableEq V] in
theorem pickEdge_mem {s : Finset (Sym2 V)} (h : s.Nonempty) : pickEdge s ∈ s := by
  rw [pickEdge, dif_pos h]
  exact h.choose_spec

omit [Fintype V] [DecidableEq V] in
theorem pickEdge_mem_or_isDiag (s : Finset (Sym2 V)) :
    pickEdge s ∈ s ∨ (pickEdge s).IsDiag := by
  by_cases h : s.Nonempty
  · exact Or.inl (pickEdge_mem h)
  · refine Or.inr ?_
    rw [pickEdge, dif_neg h]
    simp

omit [Fintype V] [DecidableEq V] in
theorem pickEdge_singleton (e : Sym2 V) : pickEdge ({e} : Finset (Sym2 V)) = e := by
  have h : ({e} : Finset (Sym2 V)).Nonempty := ⟨e, Finset.mem_singleton_self e⟩
  simpa using pickEdge_mem h

/-! ## 2. Fibras brutas, posiciones y raíces -/

/-- La fibra bruta de un patrón reducido: los items cuyo perfil de partes es
exactamente `H` y que lo recorren transversalmente. -/
def profileFiber (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → P)
    (H : Finset P) : Finset (Finset V) :=
  (items G).filter (fun K => K.image part = H ∧ K.card = H.card)

omit [Nonempty V] [Fintype P] in
theorem profileFiber_subset_items (part : V → P) (H : Finset P) :
    profileFiber G part H ⊆ items G := Finset.filter_subset _ _

omit [Nonempty V] [Fintype P] in
theorem mem_profileFiber {part : V → P} {H : Finset P} {K : Finset V} :
    K ∈ profileFiber G part H ↔
      K ∈ items G ∧ K.image part = H ∧ K.card = H.card := by
  simp [profileFiber, and_assoc]

omit [Nonempty V] [Fintype P] in
/-- Las partes son inyectivas sobre una copia de la fibra bruta. -/
theorem injOn_of_mem_profileFiber {part : V → P} {H : Finset P} {K : Finset V}
    (hK : K ∈ profileFiber G part H) :
    ∀ a ∈ K, ∀ b ∈ K, part a = part b → a = b := by
  obtain ⟨-, himg, hcard⟩ := mem_profileFiber.1 hK
  have hcard' : (K.image part).card = K.card := by rw [himg, hcard]
  have hinj : Set.InjOn part (K : Set V) := Finset.card_image_iff.1 hcard'
  intro a ha b hb hab
  exact hinj (by simpa using ha) (by simpa using hb) hab

/-- Las aristas físicas que cruzan un par de partes.  Es la reindexación de
`PatternTransfer.crossEdges` por el par de partes en vez de por un
representante. -/
def crossPair (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → P)
    (pq : Finset P) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun f => partsOf part f = pq)

omit [DecidableEq V] [Nonempty V] [Fintype P] in
theorem crossEdges_eq_crossPair (part : V → P) (e : Sym2 V) :
    crossEdges G part e = crossPair G part (partsOf part e) := rfl

omit [DecidableEq V] [Nonempty V] [Fintype P] in
theorem not_isDiag_of_mem_crossPair {part : V → P} {pq : Finset P} {e : Sym2 V}
    (he : e ∈ crossPair G part pq) : ¬ e.IsDiag := by
  have h : e ∈ G.edgeFinset := (Finset.mem_filter.1 he).1
  rw [SimpleGraph.mem_edgeFinset] at h
  exact G.not_isDiag_of_mem_edgeSet h

/-- La raíz de una copia en una posición: su única arista que cruza ese par de
partes. -/
noncomputable def rootEdge (part : V → P) (pq : Finset P) (K : Finset V) : Sym2 V :=
  pickEdge ((pairs K).filter (fun e => partsOf part e = pq))

omit [Nonempty V] [Fintype P] in
/-- Dos aristas de una copia transversal que cruzan el mismo par de partes
coinciden. -/
theorem pairs_eq_of_partsOf_eq {part : V → P} {H : Finset P} {K : Finset V}
    (hK : K ∈ profileFiber G part H) {e f : Sym2 V}
    (he : e ∈ pairs K) (hf : f ∈ pairs K)
    (h : partsOf part e = partsOf part f) : e = f := by
  have hinj := injOn_of_mem_profileFiber hK
  revert he hf h
  induction e using Sym2.ind with
  | _ a b =>
    induction f using Sym2.ind with
    | _ c d =>
      intro he hf h
      rw [mk_mem_pairs] at he hf
      rw [partsOf_mk, partsOf_mk] at h
      obtain ⟨haK, hbK, hab⟩ := he
      obtain ⟨hcK, hdK, hcd⟩ := hf
      have hc : part c ∈ ({part a, part b} : Finset P) := by
        rw [h]; simp
      have hd : part d ∈ ({part a, part b} : Finset P) := by
        rw [h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
      rcases hc with hc | hc <;> rcases hd with hd | hd
      · exact absurd (Eq.trans (hinj c hcK a haK hc) (hinj d hdK a haK hd).symm) hcd
      · rw [hinj c hcK a haK hc, hinj d hdK b hbK hd]
      · rw [hinj c hcK b hbK hc, hinj d hdK a haK hd]
        exact Sym2.eq_swap
      · exact absurd (Eq.trans (hinj c hcK b hbK hc) (hinj d hdK b hbK hd).symm) hcd

omit [Fintype P] in
/-- Cada arista de una copia transversal **es** su raíz en la posición
correspondiente. -/
theorem rootEdge_eq_of_mem_pairs {part : V → P} {H : Finset P} {K : Finset V}
    (hK : K ∈ profileFiber G part H) {e : Sym2 V} (he : e ∈ pairs K) :
    rootEdge part (partsOf part e) K = e := by
  have hsingle : (pairs K).filter (fun f => partsOf part f = partsOf part e)
      = ({e} : Finset (Sym2 V)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hf, hpf⟩
      exact (pairs_eq_of_partsOf_eq hK he hf hpf.symm).symm
    · rintro rfl
      exact ⟨he, rfl⟩
  rw [rootEdge, hsingle, pickEdge_singleton]

omit [Fintype V] [Fintype P] in
/-- Recíproco: si la raíz de una copia en una posición es un recurso físico,
ese recurso es una arista de la copia que cruza ese par de partes. -/
theorem mem_pairs_of_rootEdge_eq {part : V → P} {pq : Finset P} {K : Finset V}
    {e : Sym2 V} (hdiag : ¬ e.IsDiag) (h : rootEdge part pq K = e) :
    e ∈ pairs K ∧ partsOf part e = pq := by
  rcases pickEdge_mem_or_isDiag ((pairs K).filter (fun f => partsOf part f = pq)) with
    hmem | hdiag'
  · have hmem' : e ∈ (pairs K).filter (fun f => partsOf part f = pq) := by
      rw [← h]; exact hmem
    exact ⟨(Finset.mem_filter.1 hmem').1, (Finset.mem_filter.1 hmem').2⟩
  · have hdiag'' : e.IsDiag := by rw [← h]; exact hdiag'
    exact absurd hdiag'' hdiag

/-! ## 3. La limpieza literal -/

/-- El conteo literal de la fibra bruta en una posición de raíz. -/
noncomputable def rootCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → P) (H : Finset P) (pq : Finset P) (e : Sym2 V) : ℚ :=
  ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ)

/-- Las raíces de desviación bilateral mala de una posición: literalmente
`RC01DeviationCleanup.deviationBad` del conteo literal. -/
noncomputable def badRoots (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → P) (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) (pq : Finset P) :
    Finset (Sym2 V) :=
  deviationBad (crossPair G part pq) (rootCount G part H pq) (A H pq) u

/-- **La fibra limpia.**  Es literalmente `CopyCleanup.cleaned` de la fibra bruta,
retirando en una sola pasada toda copia que use una raíz mala en cualquiera de
sus posiciones. -/
noncomputable def cleanFiber (G : SimpleGraph V) [DecidableRel G.Adj]
    (part : V → P) (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) :
    Finset (Finset V) :=
  cleaned (profileFiber G part H) (rootEdge part) (badRoots G part A u H)

theorem cleanFiber_subset (part : V → P) (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) : cleanFiber G part A u H ⊆ profileFiber G part H :=
  cleaned_subset _ _ _

/-- **(A.1)** La fibra limpia sigue contenida en `items G`. -/
theorem cleanFiber_subset_items (part : V → P) (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) : cleanFiber G part A u H ⊆ items G :=
  (cleanFiber_subset part A u H).trans (profileFiber_subset_items part H)

/-- Every transversal copy in a profile fiber makes its profile serve each of
its physical edges. -/
theorem serving_of_mem_profileFiber {part : V → P}
    {H : Finset P} {K : Finset V} (hK' : K ∈ profileFiber G part H)
    {e : Sym2 V} (he : e ∈ pairs K) : H ∈ servingT part e := by
  have hinj := injOn_of_mem_profileFiber hK'
  obtain ⟨-, himg, -⟩ := mem_profileFiber.1 hK'
  revert he
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    rw [mk_mem_pairs] at he
    obtain ⟨haK, hbK, hab⟩ := he
    have hne : part a ≠ part b := fun h => hab (hinj a haK b hbK h)
    have hcard : (partsOf part s(a, b)).card = 2 := by
      rw [partsOf_mk]
      exact Finset.card_pair hne
    have hsub : partsOf part s(a, b) ⊆ H := by
      rw [partsOf_mk, ← himg]
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Finset.mem_image_of_mem part haK
      · exact Finset.mem_image_of_mem part hbK
    rw [servingT, if_pos hcard, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsub⟩

/-- **(A.2)** Una copia limpia por `e` fuerza que su patrón sirva a `e`. -/
theorem serving_of_mem_cleanFiber {part : V → P}
    {A : Finset P → Finset P → ℚ} {u : ℚ}
    {H : Finset P} {K : Finset V} (hK : K ∈ cleanFiber G part A u H)
    {e : Sym2 V} (he : e ∈ pairs K) : H ∈ servingT part e :=
  serving_of_mem_profileFiber (cleanFiber_subset part A u H hK) he

/-- La pertenencia a `activeServing` que pide `cleanedSpreadPacking`. -/
theorem activeServing_of_oneCount_pos {part : V → P}
    {A : Finset P → Finset P → ℚ} {u : ℚ}
    {Pats : Finset (Finset P)} {H : Finset P} (hH : H ∈ Pats) {e : Sym2 V}
    (hcount : 0 < oneCount (cleanFiber G part A u) H e) :
    H ∈ PaperIV.RC01CleanedSpreadPacking.activeServing Pats part e := by
  obtain ⟨K, hK⟩ := Finset.card_pos.1 hcount
  rw [Finset.mem_filter] at hK
  exact Finset.mem_filter.2 ⟨hH, serving_of_mem_cleanFiber hK.1 hK.2⟩

/-! ## 4. La desigualdad física de dispersión -/

/-- Las copias limpias que usan `e` están entre las copias limpias cuya raíz en
la posición de `e` es `e`. -/
theorem oneCount_le_fiber_card (part : V → P)
    (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) (e : Sym2 V) :
    oneCount (cleanFiber G part A u) H e
      ≤ (fiber (cleanFiber G part A u H) (rootEdge part (partsOf part e)) e).card := by
  apply Finset.card_le_card
  intro K hK
  rw [Finset.mem_filter] at hK
  rw [fiber, Finset.mem_filter]
  exact ⟨hK.1, rootEdge_eq_of_mem_pairs (cleanFiber_subset part A u H hK.1) hK.2⟩

/-- **(A.3)** El presupuesto físico `(1+u) · A_σ · pairVolume(e)` domina la carga
de la fibra limpia sobre cualquier recurso.  Sobre las raíces malas la fibra
limpia es vacía; sobre las buenas se aplica
`RC01DeviationCleanup.cleaned_count_mul_volume_le_budget`. -/
theorem cleanFiber_oneCount_mul_densT_le_budget (part : V → P)
    (A : Finset P → Finset P → ℚ) (vol : Finset P → ℚ)
    (u : ℚ) (hu : 0 ≤ u) (H : Finset P)
    (hvolpos : 0 < vol H)
    (hvol : ∀ f : Sym2 V, A H (partsOf part f) * densT G part f ≤ vol H)
    (e : Sym2 V) :
    (oneCount (cleanFiber G part A u) H e : ℚ) * densT G part e
      ≤ (1 + u) * vol H := by
  rcases Nat.eq_zero_or_pos (oneCount (cleanFiber G part A u) H e) with hzero | hpos
  · rw [hzero]
    have : (0 : ℚ) ≤ (1 + u) * vol H := by nlinarith
    simpa using this
  · obtain ⟨K, hK⟩ := Finset.card_pos.1 hpos
    rw [Finset.mem_filter] at hK
    obtain ⟨hKclean, hKe⟩ := hK
    have hKraw : K ∈ profileFiber G part H := cleanFiber_subset part A u H hKclean
    set pq := partsOf part e with hpq
    have hroot : rootEdge part pq K = e := rootEdge_eq_of_mem_pairs hKraw hKe
    -- `e` es un recurso físico del par de partes `pq`
    have hitem : K ∈ items G := profileFiber_subset_items part H hKraw
    have hEdge : e ∈ G.edgeFinset := pairs_subset_edgeFinset (mem_items.1 hitem) hKe
    have hmemE : e ∈ crossPair G part pq := Finset.mem_filter.2 ⟨hEdge, rfl⟩
    -- `e` no es una raíz mala, porque `K` sobrevivió a la limpieza
    have hgood : e ∉ badRoots G part A u H pq := by
      have hcl : ∀ i, rootEdge part i K ∉ badRoots G part A u H i :=
        (Finset.mem_filter.1 hKclean).2
      have := hcl pq
      rwa [hroot] at this
    -- la cota de la limpieza bilateral
    have hbound := cleaned_count_mul_volume_le_budget
      (Cs := profileFiber G part H) (rt := rootEdge part)
      (E := fun i => crossPair G part i) (c := fun i => rootCount G part H i)
      (A := A H) (u := fun _ => u)
      (fun i f => rfl) (i := pq) (e := e)
      (pairVolume := densT G part e) (densT_pos part e).le hmemE hgood
    have hcount : ((fiber (cleanFiber G part A u H)
        (rootEdge part pq) e).card : ℚ) * densT G part e
        ≤ (1 + u) * (A H pq * densT G part e) := hbound
    have hone : (oneCount (cleanFiber G part A u) H e : ℚ)
        ≤ ((fiber (cleanFiber G part A u H) (rootEdge part pq) e).card : ℚ) := by
      exact_mod_cast oneCount_le_fiber_card part A u H e
    have hstep : (oneCount (cleanFiber G part A u) H e : ℚ) * densT G part e
        ≤ ((fiber (cleanFiber G part A u H) (rootEdge part pq) e).card : ℚ)
          * densT G part e :=
      mul_le_mul_of_nonneg_right hone (densT_pos part e).le
    have hfinal : (1 + u) * (A H pq * densT G part e) ≤ (1 + u) * vol H := by
      apply mul_le_mul_of_nonneg_left
      · simpa [pq] using hvol e
      · linarith
    linarith

/-! ## 5. La retención explícita -/

omit [Fintype P] in
/-- Fuera de las posiciones del patrón no se retira ninguna copia. -/
theorem fiber_eq_empty_of_notMem_positions (part : V → P)
    (A : Finset P → Finset P → ℚ)
    (u : ℚ) (H : Finset P) {pq : Finset P} (hpq : pq ∉ H.powersetCard 2)
    {e : Sym2 V} (he : e ∈ badRoots G part A u H pq) :
    fiber (profileFiber G part H) (rootEdge part pq) e = ∅ := by
  have hE : e ∈ crossPair G part pq := (mem_deviationBad_iff.1 he).1
  have hdiag : ¬ e.IsDiag := not_isDiag_of_mem_crossPair hE
  refine Finset.eq_empty_of_forall_notMem ?_
  intro K hK
  rw [fiber, Finset.mem_filter] at hK
  obtain ⟨hKmem, hroot⟩ := hK
  obtain ⟨hpairs, hparts⟩ := mem_pairs_of_rootEdge_eq hdiag hroot
  apply hpq
  obtain ⟨-, himg, -⟩ := mem_profileFiber.1 hKmem
  have hinj := injOn_of_mem_profileFiber hKmem
  rw [Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · rw [← hparts, ← himg]
    revert hpairs
    induction e using Sym2.ind with
    | _ a b =>
      intro hpairs
      rw [mk_mem_pairs] at hpairs
      rw [partsOf_mk]
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Finset.mem_image_of_mem part hpairs.1
      · exact Finset.mem_image_of_mem part hpairs.2.1
  · rw [← hparts]
    revert hpairs
    induction e using Sym2.ind with
    | _ a b =>
      intro hpairs
      rw [mk_mem_pairs] at hpairs
      obtain ⟨haK, hbK, hab⟩ := hpairs
      rw [partsOf_mk]
      exact Finset.card_pair (fun h => hab (hinj a haK b hbK h))

/-- Las copias retiradas sólo pueden contarse en las tres (o seis) posiciones del
patrón. -/
theorem card_removed_le_positions (part : V → P)
    (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) :
    (removed (profileFiber G part H) (rootEdge part)
        (badRoots G part A u H)).card
      ≤ ∑ pq ∈ H.powersetCard 2, ∑ e ∈ badRoots G part A u H pq,
          (fiber (profileFiber G part H) (rootEdge part pq) e).card := by
  refine le_trans (card_removed_le _ _ _) ?_
  refine le_of_eq ?_
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro pq _ hpq
  refine Finset.sum_eq_zero ?_
  intro e he
  rw [fiber_eq_empty_of_notMem_positions part A u H hpq he]
  simp

/-- Retention from a literal budget for every root position.  Unlike the
`beta * M` convenience corollary below, this statement does not force all root
positions or both pattern sizes through one uniform fibre bound. -/
theorem cleanFiber_card_ge_of_root_budgets (part : V → P)
    (A : Finset P → Finset P → ℚ) (u : ℚ) (H : Finset P)
    (budget : Finset P → ℚ) {reference v : ℚ}
    (href : reference ≤ ((profileFiber G part H).card : ℚ))
    (hrow : ∀ pq ∈ H.powersetCard 2,
      ∑ e ∈ badRoots G part A u H pq,
          ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ)
        ≤ budget pq)
    (hbudget : ∑ pq ∈ H.powersetCard 2, budget pq ≤ v * reference) :
    (1 - v) * reference ≤ ((cleanFiber G part A u H).card : ℚ) := by
  refine cleaned_card_ge_of_removed_le (profileFiber G part H) (rootEdge part)
    (badRoots G part A u H) href ?_
  have hnat := card_removed_le_positions (G := G) part A u H
  have hcast : ((removed (profileFiber G part H) (rootEdge part)
        (badRoots G part A u H)).card : ℚ)
      ≤ ∑ pq ∈ H.powersetCard 2, ∑ e ∈ badRoots G part A u H pq,
          ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ) := by
    exact_mod_cast hnat
  calc
    ((removed (profileFiber G part H) (rootEdge part)
        (badRoots G part A u H)).card : ℚ)
        ≤ ∑ pq ∈ H.powersetCard 2, ∑ e ∈ badRoots G part A u H pq,
            ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ) := hcast
    _ ≤ ∑ pq ∈ H.powersetCard 2, budget pq := Finset.sum_le_sum hrow
    _ ≤ v * reference := hbudget

/-- The minimal retention interface: the graph-specific adapter only has to
bound the literal total loss over the active root positions. -/
theorem cleanFiber_card_ge_of_total_root_loss (part : V → P)
    (A : Finset P → Finset P → ℚ) (u : ℚ) (H : Finset P)
    {reference v : ℚ}
    (href : reference ≤ ((profileFiber G part H).card : ℚ))
    (hloss : ∑ pq ∈ H.powersetCard 2,
      ∑ e ∈ badRoots G part A u H pq,
        ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ)
      ≤ v * reference) :
    (1 - v) * reference ≤ ((cleanFiber G part A u H).card : ℚ) := by
  exact cleanFiber_card_ge_of_root_budgets part A u H
    (fun pq => ∑ e ∈ badRoots G part A u H pq,
      ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ))
    href (fun _ _ => le_rfl) hloss

/-- **(A.4)** Retención explícita `1 - v`: la suma sobre las tres (K₃) o seis (K₄)
familias de raíces malas, junto con `CopyCleanup.card_removed_le`, deja al menos
una fracción `1-v` del volumen de referencia. -/
theorem cleanFiber_card_ge (part : V → P)
    (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) {beta M reference v : ℚ} (hM : 0 ≤ M)
    (hbad : ∀ pq ∈ H.powersetCard 2,
      ((badRoots G part A u H pq).card : ℚ) ≤ beta)
    (hfib : ∀ pq : Finset P, ∀ e : Sym2 V,
      ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ) ≤ M)
    (href : reference ≤ ((profileFiber G part H).card : ℚ))
    (hloss : ((H.card.choose 2 : ℕ) : ℚ) * (beta * M) ≤ v * reference) :
    (1 - v) * reference ≤ ((cleanFiber G part A u H).card : ℚ) := by
  refine cleaned_card_ge_of_removed_le (profileFiber G part H) (rootEdge part)
    (badRoots G part A u H) href ?_
  have hnat := card_removed_le_positions (G := G) part A u H
  have hcast : ((removed (profileFiber G part H) (rootEdge part)
        (badRoots G part A u H)).card : ℚ)
      ≤ ∑ pq ∈ H.powersetCard 2, ∑ e ∈ badRoots G part A u H pq,
          ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ) := by
    exact_mod_cast hnat
  have hrow : ∀ pq ∈ H.powersetCard 2,
      ∑ e ∈ badRoots G part A u H pq,
        ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ)
        ≤ beta * M := by
    intro pq hpq
    calc ∑ e ∈ badRoots G part A u H pq,
          ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ)
        ≤ ∑ _e ∈ badRoots G part A u H pq, M :=
          Finset.sum_le_sum (fun e _ => hfib pq e)
      _ = ((badRoots G part A u H pq).card : ℚ) * M := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ beta * M := mul_le_mul_of_nonneg_right (hbad pq hpq) hM
  have hsum : ∑ pq ∈ H.powersetCard 2, ∑ e ∈ badRoots G part A u H pq,
        ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ)
      ≤ ((H.card.choose 2 : ℕ) : ℚ) * (beta * M) := by
    calc ∑ pq ∈ H.powersetCard 2, ∑ e ∈ badRoots G part A u H pq,
          ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ)
        ≤ ∑ _pq ∈ H.powersetCard 2, beta * M := Finset.sum_le_sum hrow
      _ = ((H.powersetCard 2).card : ℚ) * (beta * M) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((H.card.choose 2 : ℕ) : ℚ) * (beta * M) := by
          rw [Finset.card_powersetCard]
  linarith

/-- Forma explícita de la retención para un patrón `K₃`: tres familias malas. -/
theorem cleanFiber_card_ge_K3 (part : V → P)
    (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) (hH : H.card = 3) {beta M reference v : ℚ} (hM : 0 ≤ M)
    (hbad : ∀ pq ∈ H.powersetCard 2,
      ((badRoots G part A u H pq).card : ℚ) ≤ beta)
    (hfib : ∀ pq : Finset P, ∀ e : Sym2 V,
      ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ) ≤ M)
    (href : reference ≤ ((profileFiber G part H).card : ℚ))
    (hloss : 3 * (beta * M) ≤ v * reference) :
    (1 - v) * reference ≤ ((cleanFiber G part A u H).card : ℚ) := by
  refine cleanFiber_card_ge part A u H hM hbad hfib href ?_
  rw [hH]
  simpa using hloss

/-- Forma explícita de la retención para un patrón `K₄`: seis familias malas. -/
theorem cleanFiber_card_ge_K4 (part : V → P)
    (A : Finset P → Finset P → ℚ) (u : ℚ)
    (H : Finset P) (hH : H.card = 4) {beta M reference v : ℚ} (hM : 0 ≤ M)
    (hbad : ∀ pq ∈ H.powersetCard 2,
      ((badRoots G part A u H pq).card : ℚ) ≤ beta)
    (hfib : ∀ pq : Finset P, ∀ e : Sym2 V,
      ((fiber (profileFiber G part H) (rootEdge part pq) e).card : ℚ) ≤ M)
    (href : reference ≤ ((profileFiber G part H).card : ℚ))
    (hloss : 6 * (beta * M) ≤ v * reference) :
    (1 - v) * reference ≤ ((cleanFiber G part A u H).card : ℚ) := by
  refine cleanFiber_card_ge part A u H hM hbad hfib href ?_
  rw [hH]
  simpa using hloss

end PaperIV.RC01CleanFiber
