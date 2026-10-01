import PaperIV.TelescopeK4Full
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

/-!
# El adaptador de regularidad: de Szemerédi al formato (3.1)–(3.2) de RC01

Bloque «Regularidad adaptada» del contrato de formalización de RC01 (§3.3, §20.5).

## Qué entrega

`szemeredi_regularity` de Mathlib da una **equipartición**: las partes difieren en a lo sumo
un vértice.  RC01 consume otra cosa (§3.3):

* partes de tamaño **exactamente** `t`, más una clase de basura `V₀` con `|V₀| ≤ δn`;
* a lo sumo `δk²` parejas excepcionales;
* y para las demás, **discrepancia de cortes** (3.2) *para todos los subconjuntos*, no la
  definición de uniformidad con sus dos condiciones de tamaño.

`EqualRegularity` es ese formato y `exists_equalRegularity` lo construye.

## Cómo

Se recorta cada parte a exactamente `t = n/k` vértices.  El recorte no destruye la
discrepancia gracias a las dos operaciones de `OneStepEstimate`:

* `DiscrepAt.restrict` la restringe a subconjuntos pagando el cuadrado de la razón de
  tamaños; aquí `#s ≤ t+1 ≤ 2t`, luego el factor es `4`;
* `DiscrepAt.reDensity` cambia la densidad global por la de las partes recortadas al doble
  de coste.

Con `ε = δ/8` sale `4·2·ε = δ`.  Obsérvese que **no** hace falta el argumento `3/t` de la
fuente: al dejar la densidad como parámetro libre en (3.2) el cambio se absorbe en la propia
desigualdad.

## Enganche

La salida encaja directamente en `TelescopeK3Full.counting_lemma_K3` y
`TelescopeK4Full.counting_lemma_K4`, que desde ahora consumen `DiscrepAt` y no
`SimpleGraph.IsUniform`.
-/

namespace PaperIV.RegularityFormat

open Finset SimpleGraph
open PaperIV.OneStepEstimate

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 1. Recorte canónico de una parte -/

/-- Un subconjunto distinguido de `s` con exactamente `t` elementos, cuando cabe. -/
noncomputable def trim (t : ℕ) (s : Finset α) : Finset α :=
  if h : t ≤ #s then (Finset.exists_subset_card_eq h).choose else s

theorem trim_subset {t : ℕ} {s : Finset α} (h : t ≤ #s) : trim t s ⊆ s := by
  rw [trim, dif_pos h]
  exact (Finset.exists_subset_card_eq h).choose_spec.1

theorem card_trim {t : ℕ} {s : Finset α} (h : t ≤ #s) : #(trim t s) = t := by
  rw [trim, dif_pos h]
  exact (Finset.exists_subset_card_eq h).choose_spec.2

/-- **Puente ℝ → ℚ.**  `szemeredi_regularity` está enunciado sobre `ℝ` (su cota explícita
`SzemerediRegularity.bound` usa `Real.log`), pero todas las cantidades en juego —densidades y
cardinales— son racionales.  La uniformidad real con parámetro racional **es** la racional. -/
theorem isUniform_of_real {ε : ℚ} {s u : Finset α} (h : G.IsUniform ((ε : ℝ)) s u) :
    G.IsUniform ε s u := by
  intro s' hs' u' hu' h1 h2
  have h1' : ((#s : ℝ)) * (ε : ℝ) ≤ (#s' : ℝ) := by exact_mod_cast h1
  have h2' : ((#u : ℝ)) * (ε : ℝ) ≤ (#u' : ℝ) := by exact_mod_cast h2
  have hlt := h hs' hu' h1' h2'
  exact_mod_cast hlt

/-! ## 2. El formato (3.1)–(3.2) -/

/-- **Formato (3.1)–(3.2).**  Partes de tamaño exactamente `size`, disjuntas, con a lo sumo
`δ·k²` parejas excepcionales, discrepancia `δ` en las demás, y basura `≤ δn`. -/
structure EqualRegularity (G : SimpleGraph α) [DecidableRel G.Adj] (δ : ℚ) where
  /-- las partes buenas -/
  parts : Finset (Finset α)
  /-- el tamaño común -/
  size : ℕ
  size_pos : 0 < size
  card_part : ∀ P ∈ parts, #P = size
  pairwise_disjoint : ∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q
  /-- las parejas excepcionales -/
  bad : Finset (Finset α × Finset α)
  card_bad : (#bad : ℚ) ≤ δ * (#parts : ℚ) ^ 2
  /-- (3.2) en las parejas no excepcionales -/
  discrep : ∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → (P, Q) ∉ bad →
    DiscrepAt G δ (G.edgeDensity P Q) P Q
  /-- `|V₀| ≤ δn` -/
  garbage : ((Fintype.card α : ℚ) - (#parts : ℚ) * (size : ℚ)) ≤ δ * (Fintype.card α : ℚ)

/-! ## 3. La construcción -/

set_option maxHeartbeats 1000000 in
/-- **El adaptador.**  Para `n` suficientemente grande —cuantificado por la cota de
Szemerédi, que es anterior al grafo— hay una partición en el formato (3.1)–(3.2). -/
theorem exists_equalRegularity {δ : ℚ} (hδ : 0 < δ) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hk₀card : k₀ ≤ Fintype.card α)
    (hn : ((SzemerediRegularity.bound (((δ / 8 : ℚ) : ℝ)) k₀ : ℕ) : ℚ)
            ≤ δ * (Fintype.card α : ℚ)) :
    ∃ R : EqualRegularity G δ,
      k₀ ≤ #R.parts ∧ #R.parts ≤ SzemerediRegularity.bound (((δ / 8 : ℚ) : ℝ)) k₀ := by
  classical
  have hδR : (0 : ℝ) < ((δ / 8 : ℚ) : ℝ) := by
    have : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    push_cast
    linarith
  obtain ⟨P, hequi, hkl, hkL, huniR⟩ :
      ∃ P : Finpartition (Finset.univ : Finset α),
        P.IsEquipartition ∧ k₀ ≤ #P.parts ∧
          #P.parts ≤ SzemerediRegularity.bound (((δ / 8 : ℚ) : ℝ)) k₀ ∧
          P.IsUniform G (((δ / 8 : ℚ) : ℝ)) :=
    szemeredi_regularity G hδR hk₀card
  set k : ℕ := #P.parts with hkdef
  set t : ℕ := #(Finset.univ : Finset α) / k with htdef
  have hkpos : 0 < k := lt_of_lt_of_le hk₀ hkl
  have hkn : k ≤ #(Finset.univ : Finset α) := P.card_parts_le_card
  have htpos : 0 < t := (Nat.one_le_div_iff hkpos).2 hkn
  have htle : ∀ s ∈ P.parts, t ≤ #s := fun s hs => hequi.average_le_card_part hs
  have htge : ∀ s ∈ P.parts, #s ≤ t + 1 := fun s hs => hequi.card_part_le_average_add_one hs
  have hinj : Set.InjOn (trim t) (P.parts : Set (Finset α)) := by
    intro s hs u hu heq
    rw [Finset.mem_coe] at hs hu
    by_contra hne
    have hdisj : Disjoint s u := P.disjoint hs hu hne
    have hcard : #(trim t s) = t := card_trim (htle s hs)
    obtain ⟨x, hx⟩ : (trim t s).Nonempty := Finset.card_pos.1 (by rw [hcard]; exact htpos)
    exact (Finset.disjoint_left.1 hdisj) (trim_subset (htle s hs) hx)
      (trim_subset (htle u hu) (heq ▸ hx))
  have hcardimg : #(P.parts.image (trim t)) = k := Finset.card_image_of_injOn hinj
  have hsum : ∑ p ∈ P.parts, #p = #(Finset.univ : Finset α) := P.sum_card_parts
  have hub : #(Finset.univ : Finset α) ≤ k * (t + 1) := by
    rw [← hsum]
    calc ∑ p ∈ P.parts, #p ≤ ∑ _p ∈ P.parts, (t + 1) := Finset.sum_le_sum htge
      _ = k * (t + 1) := by rw [Finset.sum_const, smul_eq_mul]
  refine ⟨{ parts := P.parts.image (trim t)
            size := t
            size_pos := htpos
            card_part := ?_
            pairwise_disjoint := ?_
            bad := (P.nonUniforms G (((δ / 8 : ℚ) : ℝ))).image (fun q => (trim t q.1, trim t q.2))
            card_bad := ?_
            discrep := ?_
            garbage := ?_ }, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hQ
    exact card_trim (htle s hs)
  · intro Q hQ R hR hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hQ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hR
    have hsu : s ≠ u := by rintro rfl; exact hne rfl
    exact Finset.disjoint_of_subset_left (trim_subset (htle s hs))
      (Finset.disjoint_of_subset_right (trim_subset (htle u hu)) (P.disjoint hs hu hsu))
  · have h1 : #((P.nonUniforms G (((δ / 8 : ℚ) : ℝ))).image (fun q => (trim t q.1, trim t q.2)))
        ≤ #(P.nonUniforms G (((δ / 8 : ℚ) : ℝ))) := Finset.card_image_le
    have h1' : (#((P.nonUniforms G (((δ / 8 : ℚ) : ℝ))).image (fun q => (trim t q.1, trim t q.2))) : ℚ)
        ≤ (#(P.nonUniforms G (((δ / 8 : ℚ) : ℝ))) : ℚ) := by exact_mod_cast h1
    have h2 : (#(P.nonUniforms G (((δ / 8 : ℚ) : ℝ))) : ℚ) ≤ ((k * (k - 1) : ℕ) : ℚ) * (δ / 8) := by
      have hu0 := huniR
      rw [Finpartition.IsUniform] at hu0
      exact_mod_cast hu0
    have h3 : ((k * (k - 1) : ℕ) : ℚ) ≤ ((k * k : ℕ) : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_left k (Nat.sub_le k 1)
    have h4 : ((k * k : ℕ) : ℚ) = (k : ℚ) ^ 2 := by push_cast; ring
    have hk2 : (0 : ℚ) ≤ (k : ℚ) ^ 2 := by positivity
    rw [hcardimg]
    calc (#((P.nonUniforms G (((δ / 8 : ℚ) : ℝ))).image (fun q => (trim t q.1, trim t q.2))) : ℚ)
        ≤ ((k * (k - 1) : ℕ) : ℚ) * (δ / 8) := le_trans h1' h2
      _ ≤ (k : ℚ) ^ 2 * (δ / 8) := by
          rw [← h4]; exact mul_le_mul_of_nonneg_right h3 (by linarith)
      _ ≤ δ * (k : ℚ) ^ 2 := by nlinarith
  · intro Q hQ R hR hne hnb
    obtain ⟨s, hs, hsQ⟩ := Finset.mem_image.1 hQ
    obtain ⟨u, hu, huR⟩ := Finset.mem_image.1 hR
    have hsu : s ≠ u := by rintro rfl; exact hne (hsQ.symm.trans huR)
    have hu' : G.IsUniform (δ / 8 : ℚ) s u := by
      refine isUniform_of_real ?_
      by_contra hcon
      refine hnb (Finset.mem_image.2 ⟨(s, u), ?_, ?_⟩)
      · rw [Finpartition.mk_mem_nonUniforms]
        exact ⟨hs, hu, hsu, hcon⟩
      · rw [Prod.mk.injEq]
        exact ⟨hsQ, huR⟩
    have hts : t ≤ #s := htle s hs
    have htu : t ≤ #u := htle u hu
    have ht1 : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast htpos
    have hsle : (#s : ℚ) ≤ 2 * (#(trim t s) : ℚ) := by
      rw [card_trim hts]
      have h1 : (#s : ℚ) ≤ (t : ℚ) + 1 := by exact_mod_cast htge s hs
      linarith
    have hule : (#u : ℚ) ≤ 2 * (#(trim t u) : ℚ) := by
      rw [card_trim htu]
      have h1 : (#u : ℚ) ≤ (t : ℚ) + 1 := by exact_mod_cast htge u hu
      linarith
    have hd0 : DiscrepAt G (δ / 8) (G.edgeDensity s u) s u :=
      discrepAt_of_isUniform (by linarith) hu'
    have hd1 := hd0.restrict (by linarith) (by norm_num : (0 : ℚ) ≤ 2)
      (trim_subset hts) (trim_subset htu) hsle hule
    have hd2 : DiscrepAt G (δ / 2) (G.edgeDensity s u) (trim t s) (trim t u) :=
      hd1.mono (by linarith)
    have hps : 0 < #(trim t s) := by rw [card_trim hts]; exact htpos
    have hpu : 0 < #(trim t u) := by rw [card_trim htu]; exact htpos
    have hd3 := hd2.reDensity (by linarith) hps hpu
    rw [← hsQ, ← huR]
    exact hd3.mono (by linarith)
  · rw [hcardimg]
    have hnq : ((#(Finset.univ : Finset α) : ℕ) : ℚ) ≤ (k : ℚ) * ((t : ℚ) + 1) := by
      exact_mod_cast hub
    have hkb : (k : ℚ) ≤ δ * (Fintype.card α : ℚ) := by
      refine le_trans ?_ hn
      exact_mod_cast hkL
    have hcu : (Fintype.card α : ℚ) = ((#(Finset.univ : Finset α) : ℕ) : ℚ) := by
      rw [Finset.card_univ]
    rw [hcu]
    rw [hcu] at hkb
    nlinarith [hnq, hkb]
  · rw [hcardimg]; exact hkl
  · rw [hcardimg]; exact hkL

end PaperIV.RegularityFormat
