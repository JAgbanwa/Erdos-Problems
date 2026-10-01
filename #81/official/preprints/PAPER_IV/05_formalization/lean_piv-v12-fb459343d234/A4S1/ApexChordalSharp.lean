import A4S1.DefectOneAbsorbedStability
import A4S1.PerVertexAbsorption

/-!
# The sharp order-four bound `c₄(G) ≤ Q₁(n)` for apex-chordal graphs

**Main theorem (`apex_chordal_sharp`).**  For all sufficiently large `n`, every graph
`G` on `Fin n` having a vertex `x` with `G - x` chordal has a literal clique partition
with pieces of order at most four and at most `Q₁(n) = defectTarget 1 n = M(n+1) - 1`
pieces.

Such graphs have rooted defect one
(`PaperIV.DefectApexCorollaries.rootedDefectAt_of_induce_chordal`), and the class contains
the exact defect comparator `(K_A ⊔ I_{x}) ∨ I_H`, so this is the literal A4 order-four
target on the apex-chordal subclass.  No stability or localization hypothesis is assumed;
the statement is unconditional.

## Proof

Suppose every order-four partition of `G` has more than `Q₁(n)` pieces.

1. Padding the edges at `x` shows that `G - x` is near-extremal with deficit `O(n)`, so the
   near branch of the chordal package (`chordal_near_partition`) produces a clique `R` and
   a physical order-four partition `Q` of `G - x` with
   `|Q| ≤ B_{n-1}(r) - (117/1825) m - (12687/20000) A`.
2. For a root vertex `a`, the non-singleton links of `a` towards common hosts are at most
   `(r-1) + 2c_a`, and `∑ c_a ≤ 2m` (`A4S1.PerVertex`).  With the missing column `A_a`,
   every root neighbour `a` of `x` has at least `ν - (r-1) - e_a` good hosts,
   `e_a = A_a + 2 c_a`, where `ν = |N_H(x)|`.
3. A balanced selection gives `S ⊆ N_R(x)` with `|S| + e_a ≤ ν - r + 1` on `S` and either
   `S = N_R(x)` or `(ρ - |S|)(ν - r + 1 - |S|) ≤ ∑ e_a ≤ A + 4m`.
4. Host absorption produces an order-four partition of `G` with
   `|Q| + ρ + ν - 2|S|` pieces.
5. The exact window gap `6·(Q₁(n) - B_{n-1}(r) - (n-1-r)) = q² + 3q + 2 - 2[3 ∣ n]`,
   `q = 3r - n`, and the integer inequality `A4S1.PerVertex.apex_arith` give at most
   `Q₁(n)` pieces — a contradiction.
-/

namespace A4S1.ApexSharp

open Finset
open PaperIV.FarRounding
open PaperIV.DefectApexStability
open PaperIV.DefectTargetArithmetic
open A4S1.HostAbsorption
open A4S1.PerVertex

/-! ### The exact window gap -/

theorem six_mul_div_six (n : ℕ) :
    6 * ((n + 1) * (n + 2) / 6) + 2 * (if n % 3 = 0 then 1 else 0) = (n + 1) * (n + 2) := by
  have h6 := Nat.div_add_mod ((n + 1) * (n + 2)) 6
  have hmod : (n + 1) * (n + 2) % 6 = 2 * (if n % 3 = 0 then 1 else 0) := by
    have : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have h3 : n % 3 = n % 6 % 3 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
    rw [Nat.mul_mod, Nat.add_mod, Nat.add_mod n 2, h3]
    interval_cases (n % 6) <;> simp
  omega

theorem defectTarget_one_eq (n : ℕ) : defectTarget 1 n = (n + 1) * (n + 2) / 6 - 1 := by
  simp [defectTarget, targetSize]

/-- **The exact window gap.**  With `q = 3r - n`, the gap
`Q₁(n) - B_{n-1}(r) - (n-1-r)` is nonnegative, at least `q(q+3)/6`, and at least `q` when
`q ≥ 1`. -/
theorem window_gap (n r : ℕ) (hn : 1 ≤ n) :
    let gap : ℚ := (defectTarget 1 n : ℚ) - PaperIV.splitBaseline ((n - 1 : ℕ) : ℚ) r -
      (((n - 1 : ℕ) : ℚ) - r)
    0 ≤ gap ∧ ((((3 * r - n : ℤ)) * (3 * r - n + 3) : ℤ) : ℚ) ≤ 6 * gap ∧
      (1 ≤ (3 * r - n : ℤ) → (((3 * r - n : ℤ)) : ℚ) ≤ gap) := by
  intro gap
  have h6 := six_mul_div_six n
  have hpos : 1 ≤ (n + 1) * (n + 2) / 6 := by
    apply Nat.le_div_iff_mul_le (by norm_num) |>.mpr; nlinarith
  have hTQ : 6 * (defectTarget 1 n : ℚ) + 2 * ((if n % 3 = 0 then 1 else 0 : ℕ) : ℚ) =
      ((n : ℚ) + 1) * ((n : ℚ) + 2) - 6 := by
    rw [defectTarget_one_eq]
    have : ((6 * ((n + 1) * (n + 2) / 6) + 2 * (if n % 3 = 0 then 1 else 0) : ℕ) : ℚ) =
      (((n + 1) * (n + 2) : ℕ) : ℚ) := by rw [h6]
    push_cast [Nat.cast_sub hpos] at this ⊢
    linarith
  have hn1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub hn]; simp
  set q : ℤ := 3 * r - n with hq
  have hqQ : (q : ℚ) = 3 * (r : ℚ) - n := by rw [hq]; push_cast; ring
  have hgap : 6 * gap =
      (q : ℚ) ^ 2 + 3 * q + 2 - 2 * ((if n % 3 = 0 then 1 else 0 : ℕ) : ℚ) := by
    simp only [gap, PaperIV.splitBaseline, hn1, hqQ]
    linarith
  have hδ : n % 3 = 0 → (3 : ℤ) ∣ q := by
    intro h
    rw [hq]
    have : (3 : ℤ) ∣ (n : ℤ) := by exact_mod_cast Nat.dvd_of_mod_eq_zero h
    exact dvd_sub (dvd_mul_right 3 _) this
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : n % 3 = 0
    · obtain ⟨k, hk⟩ := hδ h
      rw [if_pos h] at hgap
      have hk' : (q : ℚ) = 3 * k := by exact_mod_cast hk
      have : (0 : ℤ) ≤ 9 * k ^ 2 + 9 * k := by
        rcases le_or_gt 0 k with h0 | h0
        · positivity
        · have : k ≤ -1 := by omega
          nlinarith
      have : (0 : ℚ) ≤ 9 * (k : ℚ) ^ 2 + 9 * k := by exact_mod_cast this
      push_cast at hgap
      nlinarith
    · rw [if_neg h] at hgap
      have : (0 : ℤ) ≤ q ^ 2 + 3 * q + 2 := by
        rcases le_or_gt (-1) q with h0 | h0
        · nlinarith
        · have : q ≤ -2 := by omega
          nlinarith
      have : (0 : ℚ) ≤ (q : ℚ) ^ 2 + 3 * q + 2 := by exact_mod_cast this
      push_cast at hgap
      nlinarith
  · have hle : ((if n % 3 = 0 then 1 else 0 : ℕ) : ℚ) ≤ 1 := by split_ifs <;> simp
    push_cast
    nlinarith
  · intro hq1
    by_cases h : n % 3 = 0
    · obtain ⟨k, hk⟩ := hδ h
      rw [if_pos h] at hgap
      have hk1 : 1 ≤ k := by omega
      have hk' : (q : ℚ) = 3 * k := by exact_mod_cast hk
      have hk1Q : (1 : ℚ) ≤ k := by exact_mod_cast hk1
      push_cast at hgap
      nlinarith
    · rw [if_neg h] at hgap
      have : (0 : ℤ) ≤ (q - 1) * (q - 2) := by
        rcases (show q = 1 ∨ 2 ≤ q by omega) with h1 | h2
        · rw [h1]; norm_num
        · nlinarith
      have : (0 : ℚ) ≤ ((q : ℚ) - 1) * ((q : ℚ) - 2) := by exact_mod_cast this
      push_cast at hgap
      nlinarith

/-! ### Transport of the root errors along the enumeration of `V ∖ {x}` -/

section Transport

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (e : W ↪ V)
  (he : ∀ y, y ∉ ({x} : Finset V) ↔ ∃ a, e a = y)
  (H : SimpleGraph W) [DecidableRel H.Adj] (hH : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b))
  (R' : Finset W)

include he hH in
/-- The missing columns of the pushed root sum to the missing incidences of `R'` in `H`. -/
theorem sum_missing_le :
    ∑ a ∈ R'.map e, ((hosts x (R'.map e)).filter fun h => ¬ G.Adj a h).card ≤
      PaperIV.RootVocab.missingIncidences H R' := by
  classical
  rw [Finset.sum_map, PaperIV.RootVocab.missingIncidences]
  refine Finset.sum_le_sum ?_
  intro a' _
  have hsub : ((hosts x (R'.map e)).filter fun h => ¬ G.Adj (e a') h) ⊆
      (PaperIV.RootVocab.missingColumn H R' a').map e := by
    intro y hy
    rw [Finset.mem_filter, mem_hosts] at hy
    obtain ⟨⟨hyx, hyR⟩, hna⟩ := hy
    obtain ⟨b, rfl⟩ := (he y).1 (by simpa using hyx)
    rw [Finset.mem_map' e]
    have hbR : b ∉ R' := fun hb => hyR (Finset.mem_map_of_mem e hb)
    simp only [PaperIV.RootVocab.missingColumn, PaperIV.RootVocab.outsideVertices,
      Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨hbR, fun h => hna ((hH a' b).1 h)⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_map _).le

include he hH in
/-- The host edges of the pushed root are the outside edges of `R'` in `H`. -/
theorem card_hostEdges_le :
    (hostEdges G x (R'.map e)).card ≤ (PaperIV.RootVocab.outsideEdges H R').card := by
  classical
  have hsub : hostEdges G x (R'.map e) ⊆
      (PaperIV.RootVocab.outsideEdges H R').map e.sym2Map := by
    intro z hz
    induction z using Sym2.ind with
    | _ u v =>
      rw [hostEdges, Finset.mem_filter] at hz
      obtain ⟨hadj, hall⟩ := hz
      have huH := mem_hosts.mp (hall u (Sym2.mem_mk_left _ _))
      have hvH := mem_hosts.mp (hall v (Sym2.mem_mk_right _ _))
      obtain ⟨u', rfl⟩ := (he u).1 (by simpa using huH.1)
      obtain ⟨v', rfl⟩ := (he v).1 (by simpa using hvH.1)
      rw [Finset.mem_map]
      refine ⟨s(u', v'), ?_, by simp [Function.Embedding.sym2Map_apply]⟩
      have hu'R : u' ∉ R' := fun h => huH.2 (Finset.mem_map_of_mem e h)
      have hv'R : v' ∉ R' := fun h => hvH.2 (Finset.mem_map_of_mem e h)
      have hG : G.Adj (e u') (e v') := by simpa using hadj
      simp only [PaperIV.RootVocab.outsideEdges, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      refine ⟨(hH u' v').2 hG, ?_⟩
      intro w hw
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [PaperIV.RootVocab.outsideVertices, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      rcases hw with rfl | rfl
      · exact hu'R
      · exact hv'R
  exact (Finset.card_le_card hsub).trans (Finset.card_map _).le

end Transport

/-! ### The main theorem -/

/-- **Sharp order-four bound for apex-chordal graphs.**  For all sufficiently large `n`,
every graph `G` on `Fin n` with a vertex `x` such that `G - x` is chordal has a clique
partition with pieces of order at most four and at most `Q₁(n) = M(n+1) - 1` pieces. -/
theorem apex_chordal_sharp :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n),
      (G.induce (({x}ᶜ : Finset (Fin n)) : Set (Fin n))).IsChordal →
      ∃ P : CliquePartition G, P.OrderAtMost 4 ∧ P.size ≤ defectTarget 1 n := by
  classical
  obtain ⟨Nst, hst⟩ := A4S1.DefectOneAbsorbed.chordal_near_partition
  refine ⟨Nst + ⌈8 / PaperIV.IntegralStability.gamma⌉₊ + 1000, ?_⟩
  intro n hn G _ x hch
  by_contra hcon
  push_neg at hcon
  set D : Finset (Fin n) := {x} with hDdef
  have hDs : D.card = 1 := Finset.card_singleton x
  have hgam := PaperIV.IntegralStability.gamma_pos
  set n' := (Dᶜ).card with hn'
  have hn'eq : n' = n - 1 := by rw [hn', Finset.card_compl, Fintype.card_fin, hDs]
  have hn'st : Nst ≤ n' := by omega
  let e : Fin n' ↪ Fin n := ((Dᶜ).orderEmbOfFin hn'.symm).toEmbedding
  have he : ∀ y, y ∉ D ↔ ∃ a, e a = y := by
    intro y
    have hr := Finset.range_orderEmbOfFin (Dᶜ) hn'.symm
    constructor
    · intro hy
      have hy' : y ∈ Set.range ((Dᶜ).orderEmbOfFin hn'.symm) := by
        rw [hr]; simpa using hy
      obtain ⟨a, ha⟩ := hy'
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (Dᶜ) hn'.symm a)
  have heD : ∀ a, e a ∉ D := fun a => (he (e a)).2 ⟨a, rfl⟩
  let H : SimpleGraph (Fin n') := G.comap e
  haveI : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (G.Adj (e a) (e b)))
  have hH : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b) := fun a b => Iff.rfl
  have hHch : PaperIV.FarRounding.IsChordal H := by
    let f' : Fin n' ↪ ((Dᶜ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨fun a => ⟨e a, by simpa using heD a⟩,
        fun a b h => e.injective (congrArg Subtype.val h)⟩
    exact hch.comap f' H (fun a b => Iff.rfl)
  set T := G.edgeFinset.filter (Touches D) with hTdef
  have hTdeg : T.card = (G.neighborFinset x).card :=
    A4S1.DefectOneAbsorbed.card_touch_singleton G x
  have hTle : (T.card : ℚ) ≤ n := by
    have h : T.card ≤ D.card * Fintype.card (Fin n) := card_touch_le G D
    rw [hDs, Fintype.card_fin, one_mul] at h
    exact_mod_cast h
  have hG0 : ∀ u v, (avoidPart G D).Adj u v ↔ G.Adj u v ∧ u ≠ x ∧ v ≠ x := by
    intro u v
    show (G.Adj u v ∧ u ∉ D ∧ v ∉ D) ↔ _
    simp [hDdef]
  -- every partition of `H` is large
  have hext : ∀ Q : CliquePartition H, Q.OrderAtMost 4 →
      (defectTarget 1 n : ℚ) + 1 - T.card ≤ (Q.size : ℚ) := by
    intro Q hQ
    obtain ⟨Q0, hQ04, hQ0s⟩ := exists_push_partition G D e he H hH Q hQ
    obtain ⟨P, hP4, hPs⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
      G (avoidPart G D) (avoidPart_le G D) Q0 hQ04
    rw [sdiff_avoidPart] at hPs
    have h1 : (defectTarget 1 n : ℚ) + 1 ≤ (P.size : ℚ) := by
      exact_mod_cast hcon P hP4
    have h2 : (P.size : ℚ) ≤ (Q0.size : ℚ) + T.card := by exact_mod_cast hPs
    rw [hQ0s] at h2
    linarith
  -- the chordal deficit
  set δ : ℚ := T.card - 1 - defectTarget 1 n + PaperIV.targetSize n' with hδdef
  have hTn' : PaperIV.targetSize n' ≤ defectTarget 1 n := by
    have h1 := targetSize_mono (show n' ≤ n by omega)
    have h2 := targetSize_le_defectTarget 1 n (by omega)
    rw [farRounding_targetSize_eq] at h2
    omega
  have hTn'Q : (PaperIV.targetSize n' : ℚ) ≤ (defectTarget 1 n : ℚ) := by exact_mod_cast hTn'
  have hceil : 8 ≤ PaperIV.IntegralStability.gamma * n := by
    have h1 : 8 / PaperIV.IntegralStability.gamma ≤
        (⌈8 / PaperIV.IntegralStability.gamma⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : (⌈8 / PaperIV.IntegralStability.gamma⌉₊ : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast (show ⌈8 / PaperIV.IntegralStability.gamma⌉₊ ≤ n by omega)
    rw [div_le_iff₀ hgam] at h1
    nlinarith
  have hn'Q : (n' : ℚ) = (n : ℚ) - 1 := by rw [hn'eq, Nat.cast_sub (by omega)]; simp
  have hsnQ : 1000 ≤ (n : ℚ) := by exact_mod_cast (show 1000 ≤ n by omega)
  have hδle : δ ≤ PaperIV.IntegralStability.gamma * (n' : ℚ) ^ 2 := by
    have hA : δ ≤ n := by rw [hδdef]; linarith
    have hB : (n : ℚ) ^ 2 / 4 ≤ (n' : ℚ) ^ 2 := by
      rw [hn'Q]; nlinarith
    have hC : (n : ℚ) ≤ PaperIV.IntegralStability.gamma * (n : ℚ) ^ 2 / 8 := by
      have hn0 : (0 : ℚ) ≤ n := by positivity
      nlinarith
    nlinarith
  -- the near branch on the induced graph
  obtain ⟨R', hR'cl, hR'2, Q, hQ4, hQle⟩ :=
    hst n' hn'st H hHch δ hδle (fun Q hQ => by have := hext Q hQ; linarith)
  set R : Finset (Fin n) := R'.map e with hRdef
  have hxR : x ∉ R := by
    intro h
    rw [hRdef, Finset.mem_map] at h
    obtain ⟨a, -, hax⟩ := h
    exact heD a (by rw [hax]; exact Finset.mem_singleton_self x)
  have hRcard : R.card = R'.card := Finset.card_map _
  obtain ⟨Q0, hQ04, hQ0s⟩ := exists_push_partition G D e he H hH Q hQ4
  -- the data of the selection
  set P : Finset (Fin n) := R.filter fun a => G.Adj x a with hPdef
  set Nx : Finset (Fin n) := (hosts x R).filter fun h => G.Adj x h with hNxdef
  set Acol : Fin n → ℕ := fun a => ((hosts x R).filter fun h => ¬ G.Adj a h).card with hAcol
  set cost : Fin n → ℕ := fun a => Acol a + 2 * (pieceHostEdges G x R Q0 a).card with hcost
  set F : ℤ := (Nx.card : ℤ) - ((R.card : ℤ) - 1) with hFdef
  obtain ⟨S, hSP, hSle, hsel⟩ := exists_balanced_selection P cost F
  have hPR : P ⊆ R := Finset.filter_subset _ _
  have hSR : S ⊆ R := hSP.trans hPR
  have hSx : ∀ a ∈ S, G.Adj x a := fun a ha => (Finset.mem_filter.mp (hSP ha)).2
  -- enough good hosts for every selected vertex
  have hgood : ∀ a ∈ S, S.card ≤
      ((commonHosts G x R a).filter fun h => ({a, h} : Finset (Fin n)) ∈ Q0.pieces).card := by
    intro a ha
    have haR := hSR ha
    have h1 := card_commonHosts_le_perVertex hG0 hxR Q0 haR
    have h2 := hSle a ha
    have h3 : (R.erase a).card = R.card - 1 := Finset.card_erase_of_mem haR
    have h4 : 1 ≤ R.card := Finset.card_pos.mpr ⟨a, haR⟩
    have h5 : Nx.card ≤ (commonHosts G x R a).card + Acol a := by
      have hsub : Nx ⊆ commonHosts G x R a ∪
          ((hosts x R).filter fun h => ¬ G.Adj a h) := by
        intro h hh
        rw [hNxdef, Finset.mem_filter] at hh
        by_cases hah : G.Adj a h
        · exact Finset.mem_union_left _ (by
            rw [commonHosts, Finset.mem_filter]; exact ⟨hh.1, hh.2, hah⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hh.1, hah⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [hcost] at h2
    omega
  obtain ⟨Qg, hQg4, hQgs⟩ := exists_absorbed_partition hG0 hxR Q0 hQ04 S hSR hSx hgood
  have hQgbig := hcon Qg hQg4
  -- degree of `x`
  have hdeg : (G.neighborFinset x).card = P.card + Nx.card := by
    have hEq : G.neighborFinset x = P ∪ Nx := by
      ext y
      simp only [SimpleGraph.mem_neighborFinset, hPdef, hNxdef, Finset.mem_union,
        Finset.mem_filter, mem_hosts]
      constructor
      · intro hy
        by_cases hyR : y ∈ R
        · exact Or.inl ⟨hyR, hy⟩
        · exact Or.inr ⟨⟨hy.ne.symm, hyR⟩, hy⟩
      · rintro (h | h)
        · exact h.2
        · exact h.2
    rw [hEq, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro y hyP hyN
    exact (mem_hosts.mp (Finset.mem_filter.mp hyN).1).2 (Finset.mem_filter.mp hyP).1
  -- sizes
  have hhosts : (hosts x R).card = n - 1 - R.card := by
    have hsub : R ⊆ ({x}ᶜ : Finset (Fin n)) := by
      intro y hy
      rw [Finset.mem_compl, Finset.mem_singleton]
      rintro rfl; exact hxR hy
    rw [hosts, Finset.card_sdiff_of_subset hsub, Finset.card_compl, Fintype.card_fin,
      Finset.card_singleton]
  have hNxle : Nx.card ≤ n - 1 - R.card := hhosts ▸ Finset.card_le_card (Finset.filter_subset _ _)
  have hRle : R.card ≤ n - 1 := by
    have := Finset.card_le_card (show R ⊆ ({x}ᶜ : Finset (Fin n)) by
      intro y hy
      rw [Finset.mem_compl, Finset.mem_singleton]
      rintro rfl; exact hxR hy)
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton] at this
    exact this
  have hSleP : S.card ≤ P.card := Finset.card_le_card hSP
  have hPleR : P.card ≤ R.card := Finset.card_le_card hPR
  -- the error mass
  set m := (PaperIV.RootVocab.outsideEdges H R').card with hmdef
  set A := PaperIV.RootVocab.missingIncidences H R' with hAdef
  have hcostsum : ∑ a ∈ P, (cost a : ℤ) ≤ (A : ℤ) + 4 * m := by
    have hA1 : ∑ a ∈ P, Acol a ≤ A := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hPR (fun _ _ _ => Nat.zero_le _))
        ?_
      exact sum_missing_le G x e he H hH R'
    have hc1 : ∑ a ∈ P, (pieceHostEdges G x R Q0 a).card ≤ 2 * m := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hPR (fun _ _ _ => Nat.zero_le _))
        ?_
      exact (sum_card_pieceHostEdges_le Q0 hQ04).trans
        (Nat.mul_le_mul_left 2 (card_hostEdges_le G x e he H hH R'))
    have hsplit : ∑ a ∈ P, cost a = ∑ a ∈ P, Acol a +
        2 * ∑ a ∈ P, (pieceHostEdges G x R Q0 a).card := by
      simp only [hcost, Finset.sum_add_distrib, Finset.mul_sum]
    have : ∑ a ∈ P, cost a ≤ A + 4 * m := by omega
    exact_mod_cast this
  -- the window gap
  obtain ⟨hgap0, hgapsq, hgapq⟩ := window_gap n R.card (by omega)
  -- the arithmetic
  have harith := apex_arith n R.card P.card Nx.card S.card
    ((defectTarget 1 n : ℚ) - PaperIV.splitBaseline ((n - 1 : ℕ) : ℚ) R.card -
      (((n - 1 : ℕ) : ℚ) - R.card))
    ((∑ a ∈ P, (cost a : ℤ) : ℤ) : ℚ)
    (by exact_mod_cast (show 1000 ≤ n by omega)) (by positivity) (by positivity)
    (by exact_mod_cast hSleP) (by exact_mod_cast hPleR)
    (by have := hNxle; omega) hgap0 hgapq hgapsq
    (by exact_mod_cast Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    (by
      rcases hsel with h | h
      · exact Or.inl (by exact_mod_cast h)
      · right
        have hF : F - S.card = (Nx.card : ℤ) - R.card + 1 - S.card := by rw [hFdef]; ring
        rw [hF] at h
        exact_mod_cast h)
  -- the ledger
  have hQg : (Qg.size : ℚ) + 2 * S.card = (Q.size : ℚ) + P.card + Nx.card := by
    have h := hQgs
    rw [hdeg, hQ0s] at h
    exact_mod_cast (show Qg.size + 2 * S.card = Q.size + P.card + Nx.card by omega)
  rw [hn'Q, ← hRcard] at hQle
  have hbig : (defectTarget 1 n : ℚ) + 1 ≤ (Qg.size : ℚ) := by exact_mod_cast hQgbig
  have hcostQ : (((∑ a ∈ P, (cost a : ℤ) : ℤ)) : ℚ) ≤ (A : ℚ) + 4 * m := by
    exact_mod_cast hcostsum
  have hn1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg _
  have hA0 : (0 : ℚ) ≤ A := Nat.cast_nonneg _
  push_cast at harith hcostQ
  rw [hn1] at harith
  linarith

end A4S1.ApexSharp
