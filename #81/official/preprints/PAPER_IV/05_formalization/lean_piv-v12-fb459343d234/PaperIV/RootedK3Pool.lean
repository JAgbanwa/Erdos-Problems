import PaperIV.RootedK3Counting
import PaperIV.RootedK4Pool

/-!
# De la cota local a `hdeg` sobre el pool canónico de **triángulos**

Gemelo de `PaperIV.RootedK4Pool`, con `r = 3`:

* `canonicalTripleOf_*` — la terna canónica de una ranura buena cumple las hipótesis del conteo
  local (tamaños iguales, partes disjuntas, discrepancia en las tres parejas **en los dos
  órdenes**);
* `pairBadEdges3` — **una ranura por pareja ordenada de partes**, no una por ranura: es lo que
  impide que el excepcional crezca como `k³t² = k n²` y que la condición sobre `δ` dependa
  de `n`;
* `exists_canonicalPoolK3_deg_lower_bound` — **`hdeg`** para el pool de triángulos, en la forma
  que consume el calendario.

Las constantes: `11 = 5 + 2·3` del segundo momento (contra `23 = 11 + 2·6` en `K₄`), y el
umbral `(1−u)·d₀²·t` (contra `(1−u)·d₀⁵·t²`): un triángulo tiene **una** parte libre sobre la
arista raíz y **dos** densidades fuera de la raíz.
-/

namespace PaperIV.RootedK3Degree

open Finset
open PaperIV.OneStepEstimate
open PaperIV.PatternCounting PaperIV.RegularityFormat PaperIV.RC01Candidates
open PaperIV.RC01K3Pool
open PaperIV.FarRounding
open PaperIV.NibbleHypotheses (deg)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]
variable {δ : ℚ}

/-! ## 1. Permutar los índices no cambia los candidatos -/

omit [Fintype α] in
theorem piece_comp_perm3 (φ : Fin 3 → α) (σ : Equiv.Perm (Fin 3)) :
    piece (φ ∘ σ) = piece φ := by
  calc piece (φ ∘ σ) = (Finset.univ.image (σ : Fin 3 → Fin 3)).image φ :=
        (Finset.image_image).symm
    _ = piece φ := by rw [Finset.image_univ_equiv]; rfl

theorem candidates_comp_perm3 {V : Fin 3 → Finset α} (σ : Equiv.Perm (Fin 3)) :
    candidates G (V ∘ σ) patK3 = candidates G V patK3 := by
  classical
  ext K
  constructor
  · rintro hK
    obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
    obtain ⟨hmem, hadj⟩ := mem_transversal_K3.1 hφ
    refine mem_candidates.2 ⟨φ ∘ σ.symm, mem_transversal_K3.2 ⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
    · have := hmem (σ.symm i)
      simpa using this
    · exact hadj _ _ (fun h => hij (σ.symm.injective h))
    · exact piece_comp_perm3 φ σ.symm
  · rintro hK
    obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
    obtain ⟨hmem, hadj⟩ := mem_transversal_K3.1 hφ
    refine mem_candidates.2 ⟨φ ∘ σ, mem_transversal_K3.2 ⟨fun i => hmem (σ i), fun i j hij => ?_⟩,
      ?_⟩
    · exact hadj _ _ (fun h => hij (σ.injective h))
    · exact piece_comp_perm3 φ σ

/-! ## 2. La terna canónica cumple las hipótesis del conteo -/

/-- Las tres parejas de una terna buena cumplen (3.2) **en los dos órdenes**. -/
theorem canonicalTripleOf_discrep (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) {i j : Fin 3} (hij : i ≠ j) :
    DiscrepAt G δ (G.edgeDensity (canonicalTripleOf R S i) (canonicalTripleOf R S j))
      (canonicalTripleOf R S i) (canonicalTripleOf R S j) := by
  have hgood := (mem_goodK3Tuples.1 (canonicalTripleOf_spec R hS).1).2.2
  have hor : ∀ a b : Fin 3, a ≠ b → ((a, b) ∈ patK3 ∨ (b, a) ∈ patK3) := by decide
  rcases hor i j hij with h | h
  · exact R.discrep _ (canonicalTripleOf_mem_parts R hS i) _ (canonicalTripleOf_mem_parts R hS j)
      (canonicalTripleOf_ne R hS hij) (hgood (i, j) h)
  · have hsymm := R.discrep _ (canonicalTripleOf_mem_parts R hS j) _
      (canonicalTripleOf_mem_parts R hS i) (canonicalTripleOf_ne R hS (Ne.symm hij)) (hgood (j, i) h)
    have := PaperIV.RootedK4Degree.discrepAt_symm hsymm
    rwa [G.edgeDensity_comm (canonicalTripleOf R S j) (canonicalTripleOf R S i)] at this

theorem canonicalTripleOf_perm_card (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ((canonicalTripleOf R S ∘ σ) i).card = R.size :=
  canonicalTripleOf_card R hS (σ i)

theorem canonicalTripleOf_perm_disjoint (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint ((canonicalTripleOf R S ∘ σ) i) ((canonicalTripleOf R S ∘ σ) j) :=
  canonicalTripleOf_disjoint R hS (fun h => hij (σ.injective h))

theorem canonicalTripleOf_perm_discrep (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (hij : i ≠ j) :
    DiscrepAt G δ
      (G.edgeDensity ((canonicalTripleOf R S ∘ σ) i) ((canonicalTripleOf R S ∘ σ) j))
      ((canonicalTripleOf R S ∘ σ) i) ((canonicalTripleOf R S ∘ σ) j) :=
  canonicalTripleOf_discrep R hS (fun h => hij (σ.injective h))

/-- Permutar los índices no cambia los soportes: siguen siendo los del pool canónico. -/
theorem k3CandidateSupports_perm_subset_pool (R : EqualRegularity G δ) {S : Finset (Finset α)}
    (hS : S ∈ goodK3Slots R) (σ : Equiv.Perm (Fin 3)) :
    k3CandidateSupports G (canonicalTripleOf R S ∘ σ) ⊆ canonicalSupportPoolK3 R := by
  have heq : k3CandidateSupports G (canonicalTripleOf R S ∘ σ)
      = k3CandidateSupports G (canonicalTripleOf R S) := by
    rw [k3CandidateSupports, k3CandidateSupports, candidates_comp_perm3]
  rw [heq]
  exact k3CandidateSupports_subset_pool R hS

/-! ## 3. Una ranura por **pareja de partes** -/

/-- Una ranura buena con una orientación que pone la pareja `q` en la raíz y tiene las dos
densidades restantes por encima de `d₀²`. -/
def SlotFor3 (R : EqualRegularity G δ) (d₀ : ℚ) (q : Finset α × Finset α)
    (Sσ : Finset (Finset α) × Equiv.Perm (Fin 3)) : Prop :=
  Sσ.1 ∈ goodK3Slots R ∧
    (canonicalTripleOf R Sσ.1 ∘ Sσ.2) 0 = q.1 ∧ (canonicalTripleOf R Sσ.1 ∘ Sσ.2) 1 = q.2 ∧
    d₀ ^ 2 ≤ rootProd3 G (canonicalTripleOf R Sσ.1 ∘ Sσ.2)

theorem rootEdges3_of_slotFor {R : EqualRegularity G δ} {d₀ : ℚ} {q : Finset α × Finset α}
    {Sσ : Finset (Finset α) × Equiv.Perm (Fin 3)} (h : SlotFor3 R d₀ q Sσ) :
    rootEdges3 G (canonicalTripleOf R Sσ.1 ∘ Sσ.2)
      = PaperIV.RootedK4Degree.pairRootEdges G q := by
  rw [rootEdges3, PaperIV.RootedK4Degree.pairRootEdges, h.2.1, h.2.2.1]

open scoped Classical in
/-- Las raíces malas de la ranura elegida para la pareja `q`. -/
noncomputable def pairBadEdges3 (R : EqualRegularity G δ) (u d₀ : ℚ)
    (q : Finset α × Finset α) : Finset (Sym2 α) :=
  if h : ∃ Sσ : Finset (Finset α) × Equiv.Perm (Fin 3), SlotFor3 R d₀ q Sσ then
    badRootEdges3 G (canonicalTripleOf R h.choose.1 ∘ h.choose.2)
      ((1 - u) * (d₀ ^ 2 * (R.size : ℚ)))
  else ∅

/-- **El excepcional de conteo**: las raíces malas, una ranura por pareja de partes. -/
noncomputable def poolBadEdges3 (R : EqualRegularity G δ) (u d₀ : ℚ) : Finset (Sym2 α) :=
  (R.parts ×ˢ R.parts).biUnion (pairBadEdges3 R u d₀)

theorem card_pairBadEdges3_le (R : EqualRegularity G δ) {u d₀ : ℚ} (hδ : 0 ≤ δ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hd₀ : 0 < d₀) (q : Finset α × Finset α) :
    ((pairBadEdges3 R u d₀ q).card : ℚ)
      ≤ 11 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 2) ^ 2 := by
  classical
  have hK0 : (0 : ℚ) ≤ 11 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 2) ^ 2 := by
    have hpos : (0 : ℚ) < (u * d₀ ^ 2) ^ 2 := by positivity
    positivity
  rw [pairBadEdges3]
  by_cases h : ∃ Sσ : Finset (Finset α) × Equiv.Perm (Fin 3), SlotFor3 R d₀ q Sσ
  · rw [dif_pos h]
    obtain ⟨hS, -, -, hrp⟩ := h.choose_spec
    have hp2 : (0 : ℚ) < d₀ ^ 2 := by positivity
    exact card_badRootEdges3_le hδ hu hu1 hp2
      (canonicalTripleOf_perm_card R hS h.choose.2)
      (fun i j hij => canonicalTripleOf_perm_disjoint R hS h.choose.2 hij)
      (fun i j hij => canonicalTripleOf_perm_discrep R hS h.choose.2 hij) R.size_pos hrp le_rfl
  · rw [dif_neg h]
    simpa using hK0

theorem card_poolBadEdges3_le (R : EqualRegularity G δ) {u d₀ : ℚ} (hδ : 0 ≤ δ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hd₀ : 0 < d₀) :
    ((poolBadEdges3 R u d₀).card : ℚ)
      ≤ (R.parts.card : ℚ) ^ 2 * (11 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 2) ^ 2) := by
  classical
  have hcb : ((poolBadEdges3 R u d₀).card : ℚ)
      ≤ ∑ q ∈ R.parts ×ˢ R.parts, ((pairBadEdges3 R u d₀ q).card : ℚ) := by
    have := Finset.card_biUnion_le (s := R.parts ×ˢ R.parts) (t := pairBadEdges3 R u d₀)
    rw [poolBadEdges3]
    exact_mod_cast this
  refine hcb.trans ?_
  refine (Finset.sum_le_sum (fun q _ => card_pairBadEdges3_le R hδ hu hu1 hd₀ q)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
  have hcast : ((R.parts.card * R.parts.card : ℕ) : ℚ) = (R.parts.card : ℚ) ^ 2 := by
    push_cast; ring
  rw [hcast]

/-! ## 4. `hdeg` para el pool de triángulos, dado el recubrimiento -/

/-- **`hdeg`, brazo `K₃`.**  Si fuera de un excepcional `Eexc` toda arista de `G` está entre dos
partes que admiten una ranura buena con las dos densidades restantes `≥ d₀²`, entonces fuera de
un excepcional apenas mayor el grado del pool canónico de triángulos está acotado por debajo. -/
theorem exists_canonicalPoolK3_deg_lower_bound (R : EqualRegularity G δ) {u d₀ : ℚ}
    (hδ : 0 ≤ δ) (hu : 0 < u) (hu1 : u ≤ 1) (hd₀ : 0 < d₀)
    (Eexc : Finset (Sym2 α))
    (hcover : ∀ e ∈ G.edgeFinset, e ∉ Eexc → ∃ q ∈ R.parts ×ˢ R.parts,
        (∃ Sσ : Finset (Finset α) × Equiv.Perm (Fin 3), SlotFor3 R d₀ q Sσ) ∧
        e ∈ PaperIV.RootedK4Degree.pairRootEdges G q)
    (hthr : 1 ≤ (1 - u) * (d₀ ^ 2 * (R.size : ℚ))) :
    ∃ E0 : Finset (Sym2 α), ∃ d : ℕ, 0 < d ∧
      (E0.card : ℚ) ≤ (Eexc.card : ℚ)
        + (R.parts.card : ℚ) ^ 2 * (11 * δ * (R.size : ℚ) ^ 2 / (u * d₀ ^ 2) ^ 2) ∧
      (1 - u) * (d₀ ^ 2 * (R.size : ℚ)) - 1 ≤ (d : ℚ) ∧
      ∀ e ∈ G.edgeFinset, e ∉ E0 → d ≤ deg (canonicalSupportPoolK3 R) e := by
  classical
  set thr : ℚ := (1 - u) * (d₀ ^ 2 * (R.size : ℚ)) with hthrdef
  refine ⟨Eexc ∪ poolBadEdges3 R u d₀, ⌊thr⌋₊, ?_, ?_, ?_, ?_⟩
  · exact Nat.floor_pos.2 hthr
  · have hunion : (((Eexc ∪ poolBadEdges3 R u d₀).card : ℕ) : ℚ)
        ≤ (Eexc.card : ℚ) + ((poolBadEdges3 R u d₀).card : ℚ) := by
      exact_mod_cast Finset.card_union_le Eexc (poolBadEdges3 R u d₀)
    linarith [card_poolBadEdges3_le R hδ hu hu1 hd₀]
  · have h := Nat.sub_one_lt_floor thr
    linarith [h.le]
  · intro e heG hE0
    rw [Finset.mem_union, not_or] at hE0
    obtain ⟨q, hq, hex, hroot⟩ := hcover e heG hE0.1
    have hnotpair : e ∉ pairBadEdges3 R u d₀ q := by
      intro hbad
      exact hE0.2 (Finset.mem_biUnion.2 ⟨q, hq, hbad⟩)
    rw [pairBadEdges3, dif_pos hex] at hnotpair
    obtain ⟨hS, -, -, -⟩ := hex.choose_spec
    have hrootEdges : e ∈ rootEdges3 G (canonicalTripleOf R hex.choose.1 ∘ hex.choose.2) := by
      rw [rootEdges3_of_slotFor hex.choose_spec]
      exact hroot
    have hdegq : thr ≤ (deg (canonicalSupportPoolK3 R) e : ℚ) :=
      deg_ge_of_notMem_badRootEdges3
        (fun i j hij => canonicalTripleOf_perm_disjoint R hS hex.choose.2 hij)
        (k3CandidateSupports_perm_subset_pool R hS hex.choose.2) hrootEdges hnotpair
    have hfl : ((⌊thr⌋₊ : ℕ) : ℚ) ≤ thr := Nat.floor_le (by linarith)
    have hle : ((⌊thr⌋₊ : ℕ) : ℚ) ≤ ((deg (canonicalSupportPoolK3 R) e : ℕ) : ℚ) :=
      le_trans hfl hdegq
    exact_mod_cast hle

end PaperIV.RootedK3Degree
