/-
# Elementary graph-counting tools in the edge-set model.

Standard counting facts (in the edge-set model of `BKLO.Transformer`) used by the parts-confined
absorber of `BKLO/AbsorberPartsInterface.lean` and by the refutation of its unbounded-parts
variant:

* `edeg_union_of_disjoint`, `sum_edeg_eq_two_mul_card` — degrees add over edge-disjoint unions,
  and the handshake identity `∑_{v ∈ S} d(v) = 2e(G)`;
* `edeg_cliqueEdges_eq` — the degree of a vertex in a complete graph;
* `card_le_card_mul_of_edeg_le` — a bounded-degree edge set is small;
* `edeg_star`, `card_star` — the degrees and size of a star;
* `card_le_two_mul_of_bipartite` — **the counting obstruction**: if `X ∪ Y` is
  triangle-decomposable, `X` and `Y` are edge-disjoint and `Y` is bipartite, then every triangle of
  the decomposition uses an edge of `X`, whence `e(Y) ≤ 2 e(X)`.
-/
import BKLO.TransportV
import BKLO.Section10Defs

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Degrees -/

theorem edeg_union_of_disjoint {X Y : Finset (Sym2 V)} (h : Disjoint X Y) (v : V) :
    edeg (X ∪ Y) v = edeg X v + edeg Y v := by
  classical
  unfold edeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter h)]

/-- In a clique on `S`, an edge has exactly two endpoints, both in `S`. -/
theorem card_filter_mem_of_mem_cliqueEdges {S : Finset V} {e : Sym2 V} (he : e ∈ cliqueEdges S) :
    (S.filter (fun v => v ∈ e)).card = 2 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    rw [mem_cliqueEdgesV] at he
    obtain ⟨hmem, hne⟩ := he
    have hab : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using hne
    have ha : a ∈ S := hmem a (by simp)
    have hb : b ∈ S := hmem b (by simp)
    have : S.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v
      simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, rfl | rfl⟩ <;> simp
      · rintro (rfl | rfl) <;> simp [ha, hb]
    rw [this, Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]

/-- **Handshake.**  For an edge set living on `S`, the degrees sum to twice the number of edges. -/
theorem sum_edeg_eq_two_mul_card {S : Finset V} {R : Finset (Sym2 V)} (hR : R ⊆ cliqueEdges S) :
    ∑ v ∈ S, edeg R v = 2 * R.card := by
  classical
  have h1 : ∀ v : V, edeg R v = ∑ e ∈ R, if v ∈ e then 1 else 0 := by
    intro v; rw [edeg, Finset.card_filter]
  calc ∑ v ∈ S, edeg R v = ∑ v ∈ S, ∑ e ∈ R, (if v ∈ e then 1 else 0) := by
        exact Finset.sum_congr rfl fun v _ => h1 v
    _ = ∑ e ∈ R, ∑ v ∈ S, (if v ∈ e then 1 else 0) := Finset.sum_comm
    _ = ∑ e ∈ R, 2 := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [← Finset.card_filter]
        exact card_filter_mem_of_mem_cliqueEdges (hR he)
    _ = 2 * R.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- The degree of a vertex of a clique. -/
theorem edeg_cliqueEdges_eq {t : Finset V} {v : V} (hv : v ∈ t) :
    edeg (cliqueEdges t) v = t.card - 1 := by
  classical
  have hfil : (cliqueEdges t).filter (fun e => v ∈ e) = (t.erase v).image (fun u => s(v, u)) := by
    ext e
    induction e using Sym2.ind with
    | _ p q =>
      simp only [Finset.mem_filter, mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq,
        Finset.mem_image, Finset.mem_erase, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨hmem, hne⟩, hvpq⟩
        rcases hvpq with rfl | rfl
        · exact ⟨q, ⟨fun h => hne h.symm, hmem q (Or.inr rfl)⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨p, ⟨fun h => hne h, hmem p (Or.inl rfl)⟩, Or.inr ⟨rfl, rfl⟩⟩
      · rintro ⟨u, ⟨hu1, hu2⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩
          · rintro z (rfl | rfl)
            exacts [hv, hu2]
          · exact fun h => hu1 h.symm
        · refine ⟨⟨?_, ?_⟩, Or.inr rfl⟩
          · rintro z (rfl | rfl)
            exacts [hu2, hv]
          · exact fun h => hu1 h
  have hinj : Set.InjOn (fun u => s(v, u)) (t.erase v) := by
    intro a _ b _ hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  rw [edeg, hfil, Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hv]

/-- A bounded-degree edge set on `S` has at most `|S| · q` edges. -/
theorem card_le_card_mul_of_edeg_le {S : Finset V} {R : Finset (Sym2 V)} {q : ℕ}
    (hR : R ⊆ cliqueEdges S) (hq : ∀ v : V, edeg R v ≤ q) : R.card ≤ S.card * q := by
  classical
  have hsub : R ⊆ S.biUnion (fun v => R.filter (fun e => v ∈ e)) := by
    intro e he
    have hmem := mem_cliqueEdgesV.1 (hR he)
    obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
      induction e using Sym2.ind with
      | _ p q => exact ⟨p, by simp⟩
    exact Finset.mem_biUnion.2 ⟨x, hmem.1 x hx, Finset.mem_filter.2 ⟨he, hx⟩⟩
  calc R.card ≤ (S.biUnion (fun v => R.filter (fun e => v ∈ e))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (R.filter (fun e => v ∈ e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ S, q := Finset.sum_le_sum fun v _ => hq v
    _ = S.card * q := by rw [Finset.sum_const, smul_eq_mul]

/-! ### Stars -/

/-- The star with centre `x` and leaves `K`. -/
def star (x : V) (K : Finset V) : Finset (Sym2 V) := K.image (fun b => s(x, b))

theorem mem_star {x : V} {K : Finset V} {e : Sym2 V} :
    e ∈ star x K ↔ ∃ b ∈ K, e = s(x, b) := by
  simp [star, eq_comm]

theorem card_star (x : V) (K : Finset V) : (star x K).card = K.card := by
  classical
  refine Finset.card_image_of_injOn ?_
  intro a _ b _ hab
  simp only [Sym2.eq_iff] at hab
  rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
  · exact h
  · exact h2.trans h1

theorem edeg_star_centre (x : V) (K : Finset V) : edeg (star x K) x = K.card := by
  classical
  have : (star x K).filter (fun e => x ∈ e) = star x K := by
    refine Finset.filter_true_of_mem fun e he => ?_
    obtain ⟨b, _, rfl⟩ := mem_star.1 he
    simp
  rw [edeg, this, card_star]

theorem edeg_star_other {x v : V} {K : Finset V} (hv : v ≠ x) :
    edeg (star x K) v = if v ∈ K then 1 else 0 := by
  classical
  by_cases hvK : v ∈ K
  · rw [if_pos hvK, edeg]
    have : (star x K).filter (fun e => v ∈ e) = {s(x, v)} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨he, hve⟩
        obtain ⟨b, hb, rfl⟩ := mem_star.1 he
        simp only [Sym2.mem_iff] at hve
        rcases hve with rfl | rfl
        · exact absurd rfl hv
        · rfl
      · rintro rfl
        exact ⟨mem_star.2 ⟨v, hvK, rfl⟩, by simp⟩
    rw [this, Finset.card_singleton]
  · rw [if_neg hvK, edeg]
    have : (star x K).filter (fun e => v ∈ e) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun e he hve => ?_
      obtain ⟨b, hb, rfl⟩ := mem_star.1 he
      simp only [Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · exact hv rfl
      · exact hvK hb
    rw [this, Finset.card_empty]

/-! ### The counting obstruction -/

/-- `Y` is bipartite, witnessed by a `Bool`-colouring of the vertices. -/
def BipartiteEdges (Y : Finset (Sym2 V)) : Prop :=
  ∃ c : V → Bool, ∀ a b : V, s(a, b) ∈ Y → c a ≠ c b

/-- A bipartite edge set contains no triangle. -/
theorem not_cliqueEdges_subset_of_bipartite {Y : Finset (Sym2 V)} (hY : BipartiteEdges Y)
    {t : Finset V} (ht : t.card = 3) : ¬ cliqueEdges t ⊆ Y := by
  obtain ⟨c, hc⟩ := hY
  obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Finset.card_eq_three.1 ht
  intro hsub
  have hmem : ∀ x y : V, x ∈ ({a, b, d} : Finset V) → y ∈ ({a, b, d} : Finset V) → x ≠ y →
      s(x, y) ∈ Y := by
    intro x y hx hy hxy
    refine hsub (mem_cliqueEdgesV.2 ⟨?_, ?_⟩)
    · rintro z hz
      simp only [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> assumption
    · simpa [Sym2.isDiag_iff_proj_eq] using hxy
  have h1 := hc a b (hmem a b (by simp) (by simp) hab)
  have h2 := hc a d (hmem a d (by simp) (by simp) had)
  have h3 := hc b d (hmem b d (by simp) (by simp) hbd)
  revert h1 h2 h3
  cases c a <;> cases c b <;> cases c d <;> simp

/-- **The counting obstruction.**  If `X ∪ Y` is triangle-decomposable with `X`, `Y` edge-disjoint
and `Y` bipartite, then each triangle of the decomposition contains an edge of `X`, so there are at
most `e(X)` triangles and hence `e(X) + e(Y) ≤ 3 e(X)`. -/
theorem card_le_two_mul_of_bipartite {X Y : Finset (Sym2 V)} (hd : Disjoint X Y)
    (hY : BipartiteEdges Y) (h : TriDecomp (X ∪ Y)) : Y.card ≤ 2 * X.card := by
  classical
  obtain ⟨P, hc3, hdisj, hedges⟩ := h
  -- the decomposition has `3 |P|` edges
  have hcard : X.card + Y.card = 3 * P.card := by
    have h1 : (X ∪ Y).card = X.card + Y.card := Finset.card_union_of_disjoint hd
    have h2 : (famEdges P).card = ∑ t ∈ P, (cliqueEdges t).card := by
      unfold famEdges
      exact Finset.card_biUnion (fun x hx y hy hxy => hdisj x hx y hy hxy)
    have h3 : ∑ t ∈ P, (cliqueEdges t).card = 3 * P.card := by
      rw [Finset.sum_congr rfl (fun t ht => cliqueEdges_card_three (hc3 t ht))]
      simp [Finset.sum_const, Nat.mul_comm]
    rw [← h1, ← hedges, h2, h3]
  -- each triangle uses an edge of `X`
  have hex : ∀ t ∈ P, ∃ e ∈ cliqueEdges t, e ∈ X := by
    intro t ht
    by_contra hno
    push_neg at hno
    refine not_cliqueEdges_subset_of_bipartite hY (hc3 t ht) fun e he => ?_
    have : e ∈ X ∪ Y := by
      rw [hedges.symm] at *
      exact Finset.mem_biUnion.2 ⟨t, ht, he⟩
    rcases Finset.mem_union.1 this with hX | hY'
    · exact absurd hX (hno e he)
    · exact hY'
  choose f hf hfX using hex
  have hinj : ∀ (t : Finset V) (ht : t ∈ P) (t' : Finset V) (ht' : t' ∈ P),
      f t ht = f t' ht' → t = t' := by
    intro t ht t' ht' heq
    by_contra hne
    have := hdisj t ht t' ht' hne
    rw [Finset.disjoint_left] at this
    exact this (hf t ht) (heq ▸ hf t' ht')
  have hple : P.card ≤ X.card := by
    rcases Finset.eq_empty_or_nonempty P with rfl | ⟨t₀, ht₀⟩
    · simp
    · have e₀ : Sym2 V := f t₀ ht₀
      refine Finset.card_le_card_of_injOn (fun t => if ht : t ∈ P then f t ht else e₀) ?_ ?_
      · intro t ht
        simp only [Finset.mem_coe] at ht
        simp only [dif_pos ht, Finset.mem_coe]
        exact hfX t ht
      · intro t ht t' ht' heq
        simp only [Finset.mem_coe] at ht ht'
        simp only [dif_pos ht, dif_pos ht'] at heq
        exact hinj t ht t' ht' heq
  omega

end BKLO
