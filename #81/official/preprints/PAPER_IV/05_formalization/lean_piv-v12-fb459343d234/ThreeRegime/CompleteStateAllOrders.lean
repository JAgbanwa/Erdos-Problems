import ThreeRegime.HalvingFrames
import ThreeRegime.TrianglePackingParity

/-!
# El estado completo cierra para todo orden

Se ensamblan las seis clases de restos módulo `6` a partir de los dos marcos de
`ThreeRegime.HalvingFrames`:

| `n % 6` | construcción | piezas `K₄` |
|---|---|---|
| `3` | Bose sobre `ZMod (n/3)`, sin el punto extra | `0` |
| `4` | Bose sobre `ZMod ((n-1)/3)` con columnas `K₄` | `(n-1)/3` |
| `5` | la anterior más un vértice aislado | `(n-2)/3` |
| `1` | Skolem sobre `ZMod ((n-1)/3)` | `0` |
| `0` | Skolem sobre `ZMod (n/3)` menos un punto | `0` |
| `2` | Bose sobre `ZMod ((n+1)/3)` menos un punto | `0` |

En los casos `n ≡ 0, 2, 3, 1 (mod 6)` basta con triángulos; en `n ≡ 4, 5 (mod 6)` hacen falta
piezas `K₄`, como exige `not_triangle_obligation_of_four_mod_six`.
-/

namespace ThreeRegime.CompleteStateAllOrders

open Finset PaperIV PaperIV.FarRounding ThreeRegime.Latin ThreeRegime.Transport ThreeRegime.Owner

/-! ## 1. Reducciones genéricas -/

/-- Basta construir el empaquetamiento sobre *algún* tipo de cardinal `n`. -/
theorem exists_packing_fin_of_card {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (hcard : Fintype.card V = n) (P : Packing (⊤ : SimpleGraph V))
    (h : n * (n - 2) ≤ 3 * P.gain) :
    ∃ P' : Packing (⊤ : SimpleGraph (Fin n)), n * (n - 2) ≤ 3 * P'.gain := by
  classical
  let e : Fin n ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨comapPacking e.toEmbedding P (fun _ _ w _ => ⟨e.symm w, by simp [e]⟩), ?_⟩
  rw [comapPacking_gain]
  exact h

/-- Una descomposición triangular completa de `K_{n+1}` produce el empaquetamiento que hace
falta en `K_n`: se borra un punto. -/
theorem exists_packing_of_delete {V : Type*} [Fintype V] [DecidableEq V]
    (P : Packing (⊤ : SimpleGraph V)) (htri : ∀ K ∈ P.pieces, K.card = 3)
    (hcov : P.pieces.biUnion pairs = (⊤ : SimpleGraph V).edgeFinset)
    (v : V) (n : ℕ) (hn : Fintype.card V = n + 1) :
    ∃ P' : Packing (⊤ : SimpleGraph (Fin n)), n * (n - 2) ≤ 3 * P'.gain := by
  classical
  have hcount := six_mul_card_pieces_avoiding P htri hcov v
  rw [hn] at hcount
  set B := P.pieces.filter (fun K => v ∉ K) with hB
  have hBsub : B ⊆ P.pieces := Finset.filter_subset _ _
  set PB := subPacking P B hBsub with hPB
  have htriB : ∀ K ∈ PB.pieces, K.card = 3 := fun K hK => htri K (hBsub hK)
  have hgainB : PB.gain = 2 * B.card := ThreeRegime.gain_of_all_triangles PB htriB
  -- `6·|B| = n·(n−2)` en cuanto `n ≥ 2`
  have hkey : n * (n - 2) ≤ 6 * B.card := by
    rcases Nat.lt_or_ge n 2 with hsmall | hbig
    · have : n * (n - 2) = 0 := by
        interval_cases n <;> simp
      omega
    · have hring : (n + 1) * n = n * (n - 2) + 3 * n := by
        obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      simp only [Nat.add_sub_cancel] at hcount
      omega
  -- se retrae al subtipo que evita `v`
  have hcardS : Fintype.card {x : V // x ≠ v} = n := by
    have h1 : Fintype.card {x : V // ¬ (x = v)}
        = Fintype.card V - Fintype.card {x : V // x = v} := Fintype.card_subtype_compl _
    rw [Fintype.card_subtype_eq, hn] at h1
    simpa using h1
  have hsub : ∀ K ∈ PB.pieces, ∀ w ∈ K, ∃ u : {x : V // x ≠ v},
      (Function.Embedding.subtype (fun x : V => x ≠ v)) u = w := by
    intro K hK w hw
    have hne : w ≠ v := by
      intro h
      exact (Finset.mem_filter.1 hK).2 (h ▸ hw)
    exact ⟨⟨w, hne⟩, rfl⟩
  refine exists_packing_fin_of_card hcardS
    (comapPacking (Function.Embedding.subtype _) PB hsub) ?_
  rw [comapPacking_gain, hgainB]
  omega

/-! ## 2. Los marcos completos -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Si el marco cubre todas las aristas, el objetivo se cumple sobre `Pt Q`. -/
theorem full_frame_closes (F : Frame Q) (hp : F.HasPartner) :
    Fintype.card (Pt Q) * (Fintype.card (Pt Q) - 2) ≤ 3 * F.packing.gain := by
  classical
  set N := Fintype.card (Pt Q) with hN
  have h1 := three_mul_gain F.packing
  rw [Frame.packing_pieces, F.biUnion_eq_edgeFinset hp,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at h1
  have h2 := ThreeRegime.six_mul_choose_two N
  have hstep : N * (N - 2) ≤ N * (N - 1) := Nat.mul_le_mul_left N (by omega)
  have hC : 2 * Nat.choose N 2 = N * (N - 1) := by omega
  rw [h1]
  calc N * (N - 2) ≤ N * (N - 1) := hstep
    _ = 2 * Nat.choose N 2 := hC.symm
    _ ≤ 2 * Nat.choose N 2 + 3 * (F.blocks.filter (fun K => K.card = 4)).card :=
        Nat.le_add_right _ _

/-! ## 3. Las seis clases -/

section Cases

/-- `n ≡ 4 (mod 6)`: Bose con columnas `K₄`. -/
theorem closes_four_mod_six (M : ℕ) [NeZero M] (hM : M % 2 = 1) :
    ∃ P : Packing (⊤ : SimpleGraph (Fin (3 * M + 1))),
      (3 * M + 1) * (3 * M + 1 - 2) ≤ 3 * P.gain := by
  have hcard : Fintype.card (Pt (ZMod M)) = 3 * M + 1 := by
    rw [Frame.card_Pt, ZMod.card]
  refine exists_packing_fin_of_card hcard (oddFrame M hM true).packing ?_
  have := full_frame_closes (oddFrame M hM true) (oddFrame_hasPartner M hM)
  rwa [hcard] at this

/-- `n ≡ 1 (mod 6)`: Skolem. -/
theorem closes_one_mod_six (M : ℕ) [NeZero M] (hM : M % 2 = 0) (h2 : 2 ≤ M) :
    ∃ P : Packing (⊤ : SimpleGraph (Fin (3 * M + 1))),
      (3 * M + 1) * (3 * M + 1 - 2) ≤ 3 * P.gain := by
  have hcard : Fintype.card (Pt (ZMod M)) = 3 * M + 1 := by
    rw [Frame.card_Pt, ZMod.card]
  refine exists_packing_fin_of_card hcard (evenFrame hM).packing ?_
  have := full_frame_closes (evenFrame hM) (evenFrame_hasPartner hM h2)
  rwa [hcard] at this

/-! ### La descomposición triangular de `K_{3M}` (Bose sin el punto extra) -/

/-- Los bloques de Bose sin `K₄` evitan el punto extra, luego se retraen a `Q × ZMod 3`. -/
noncomputable def bosePacking (M : ℕ) [NeZero M] (hM : M % 2 = 1) :
    Packing (⊤ : SimpleGraph (ZMod M × ZMod 3)) :=
  comapPacking ⟨Sum.inl, Sum.inl_injective⟩ (oddFrame M hM false).packing
    (by
      intro K hK w hw
      rcases w with ⟨p, i⟩ | u
      · exact ⟨(p, i), rfl⟩
      · exfalso
        have : (star : Pt (ZMod M)) ∈ K := by
          cases u; exact hw
        exact (oddFrame M hM false).star_notMem_of_fixed rfl
          (oddFrame_s M hM false) hK this)

theorem bosePacking_tri (M : ℕ) [NeZero M] (hM : M % 2 = 1) :
    ∀ K ∈ (bosePacking M hM).pieces, K.card = 3 := by
  intro K hK
  obtain ⟨K₀, hK₀, hcard⟩ := comapPacking_card_exists _ _ _ hK
  rw [hcard]
  exact (oddFrame M hM false).all_card_three rfl hK₀

theorem bosePacking_cov (M : ℕ) [NeZero M] (hM : M % 2 = 1) :
    (bosePacking M hM).pieces.biUnion pairs
      = (⊤ : SimpleGraph (ZMod M × ZMod 3)).edgeFinset := by
  classical
  refine Finset.Subset.antisymm (bosePacking M hM).biUnion_subset_edgeFinset (fun e he => ?_)
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact he
    refine mem_comapPacking_biUnion _ _ _ ?_
    have hmap : Sym2.map (⟨Sum.inl, Sum.inl_injective⟩ : (ZMod M × ZMod 3) ↪ Pt (ZMod M))
        s(a, b) = s(pt a.1 a.2, pt b.1 b.2) := by simp
    rw [hmap]
    exact (oddFrame M hM false).coverage_inner a.1 b.1 a.2 b.2
      (by simpa [Prod.ext_iff] using hab)

/-- `n ≡ 3 (mod 6)`: Bose puro. -/
theorem closes_three_mod_six (M : ℕ) [NeZero M] (hM : M % 2 = 1) :
    ∃ P : Packing (⊤ : SimpleGraph (Fin (3 * M))),
      (3 * M) * (3 * M - 2) ≤ 3 * P.gain := by
  classical
  have hcard : Fintype.card (ZMod M × ZMod 3) = 3 * M := by
    rw [Fintype.card_prod, ZMod.card, ZMod.card]; ring
  refine exists_packing_fin_of_card hcard (bosePacking M hM) ?_
  set N := 3 * M with hNdef
  have h1 := three_mul_gain (bosePacking M hM)
  rw [bosePacking_cov M hM, SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcard] at h1
  have h2 := ThreeRegime.six_mul_choose_two N
  have hstep : N * (N - 2) ≤ N * (N - 1) := Nat.mul_le_mul_left N (by omega)
  have hC : 2 * Nat.choose N 2 = N * (N - 1) := by omega
  omega

/-- `n ≡ 2 (mod 6)`: Bose menos un punto. -/
theorem closes_two_mod_six (M : ℕ) [NeZero M] (hM : M % 2 = 1) :
    ∃ P : Packing (⊤ : SimpleGraph (Fin (3 * M - 1))),
      (3 * M - 1) * (3 * M - 1 - 2) ≤ 3 * P.gain := by
  classical
  have hMpos : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hcard : Fintype.card (ZMod M × ZMod 3) = (3 * M - 1) + 1 := by
    rw [Fintype.card_prod, ZMod.card, ZMod.card]
    omega
  exact exists_packing_of_delete (bosePacking M hM) (bosePacking_tri M hM)
    (bosePacking_cov M hM) (0, 0) _ hcard

/-- `n ≡ 0 (mod 6)`: Skolem menos un punto. -/
theorem closes_zero_mod_six (M : ℕ) [NeZero M] (hM : M % 2 = 0) (h2 : 2 ≤ M) :
    ∃ P : Packing (⊤ : SimpleGraph (Fin (3 * M))),
      (3 * M) * (3 * M - 2) ≤ 3 * P.gain := by
  classical
  have hcard : Fintype.card (Pt (ZMod M)) = 3 * M + 1 := by
    rw [Frame.card_Pt, ZMod.card]
  refine exists_packing_of_delete (evenFrame hM).packing ?_ ?_ star _ hcard
  · intro K hK
    exact (evenFrame hM).all_card_three rfl hK
  · exact (evenFrame hM).biUnion_eq_edgeFinset (evenFrame_hasPartner hM h2)

/-- `n ≡ 5 (mod 6)`: Bose con columnas `K₄` más un vértice aislado. -/
theorem closes_five_mod_six (M : ℕ) [NeZero M] (hM : M % 2 = 1) :
    ∃ P : Packing (⊤ : SimpleGraph (Fin (3 * M + 2))),
      (3 * M + 2) * (3 * M + 2 - 2) ≤ 3 * P.gain := by
  classical
  set F := oddFrame M hM true with hF
  set g : Pt (ZMod M) ↪ (Pt (ZMod M) ⊕ Unit) := ⟨Sum.inl, Sum.inl_injective⟩ with hg
  have hcardW : Fintype.card (Pt (ZMod M)) = 3 * M + 1 := by
    rw [Frame.card_Pt, ZMod.card]
  have hcard : Fintype.card (Pt (ZMod M) ⊕ Unit) = 3 * M + 2 := by
    rw [Fintype.card_sum, hcardW]; simp
  refine exists_packing_fin_of_card hcard (mapPacking g F.packing) ?_
  have h1 := three_mul_gain (mapPacking g F.packing)
  rw [mapPacking_biUnion_card, mapPacking_card_four, Frame.packing_pieces,
    F.biUnion_eq_edgeFinset (oddFrame_hasPartner M hM),
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcardW,
    F.filter_card_four_card rfl (oddFrame_s M hM true)] at h1
  rw [ZMod.card] at h1
  have h2 := ThreeRegime.six_mul_choose_two (3 * M + 1)
  have h3 : 3 * M + 1 - 1 = 3 * M := by omega
  rw [h3] at h2
  have hring : (3 * M + 2) * (3 * M + 2 - 2) = (3 * M + 1) * (3 * M) + 3 * M := by
    simp only [Nat.add_sub_cancel]
    ring
  omega

end Cases

/-! ## 4. El ensamblaje -/

/-- **Para todo `n` existe el empaquetamiento mixto que la ruta del centro necesita.** -/
theorem exists_packing (n : ℕ) :
    ∃ P : Packing (⊤ : SimpleGraph (Fin n)), n * (n - 2) ≤ 3 * P.gain := by
  classical
  match hn : n with
  | 0 => exact ⟨⟨∅, by simp, by simp⟩, by simp⟩
  | 1 => exact ⟨⟨∅, by simp, by simp⟩, by simp⟩
  | (m + 2) =>
    set n := m + 2 with hndef
    have hn2 : 2 ≤ n := by omega
    have hres : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
      omega
    rcases hres with h | h | h | h | h | h
    · -- n ≡ 0
      obtain ⟨M, hM⟩ : ∃ M, n = 3 * M := ⟨n / 3, by omega⟩
      have hMe : M % 2 = 0 := by omega
      have hM2 : 2 ≤ M := by omega
      haveI : NeZero M := ⟨by omega⟩
      rw [hM]
      exact closes_zero_mod_six M hMe hM2
    · -- n ≡ 1
      obtain ⟨M, hM⟩ : ∃ M, n = 3 * M + 1 := ⟨n / 3, by omega⟩
      have hMe : M % 2 = 0 := by omega
      have hM2 : 2 ≤ M := by omega
      haveI : NeZero M := ⟨by omega⟩
      rw [hM]
      exact closes_one_mod_six M hMe hM2
    · -- n ≡ 2
      obtain ⟨M, hM⟩ : ∃ M, n = 3 * M - 1 ∧ M % 2 = 1 ∧ 1 ≤ M := ⟨(n + 1) / 3, by omega⟩
      haveI : NeZero M := ⟨by omega⟩
      rw [hM.1]
      exact closes_two_mod_six M hM.2.1
    · -- n ≡ 3
      obtain ⟨M, hM⟩ : ∃ M, n = 3 * M ∧ M % 2 = 1 := ⟨n / 3, by omega⟩
      haveI : NeZero M := ⟨by omega⟩
      rw [hM.1]
      exact closes_three_mod_six M hM.2
    · -- n ≡ 4
      obtain ⟨M, hM⟩ : ∃ M, n = 3 * M + 1 ∧ M % 2 = 1 := ⟨n / 3, by omega⟩
      haveI : NeZero M := ⟨by omega⟩
      rw [hM.1]
      exact closes_four_mod_six M hM.2
    · -- n ≡ 5
      obtain ⟨M, hM⟩ : ∃ M, n = 3 * M + 2 ∧ M % 2 = 1 := ⟨n / 3, by omega⟩
      haveI : NeZero M := ⟨by omega⟩
      rw [hM.1]
      exact closes_five_mod_six M hM.2

/-- **El estado completo cierra para todo orden.**  Para todo `n`, el grafo completo `K_n`
admite una partición en cliques de orden a lo sumo `4` con a lo sumo `targetSize n` piezas. -/
theorem complete_state_closes (n : ℕ) :
    ∃ Q : CliquePartition (⊤ : SimpleGraph (Fin n)),
      Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n := by
  obtain ⟨P, hP⟩ := exists_packing n
  have hc : Fintype.card (Fin n) = n := Fintype.card_fin n
  have := TrianglePackingParity.centre_closes_of_gain P (by rw [hc]; exact hP)
  rwa [hc] at this

end ThreeRegime.CompleteStateAllOrders
