import BoundedCliqueGap.FlowerFull

/-
`BoundedCliqueGap.Shell` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung I2 — the SHELL: the relative flower, the assembly primitive

The shell is the *relative* (separator-avoiding) flower that a clique-tree
assembly may use at one node.  On `Fin κ ⊕ Fin t`:

* the hub is the clique `Fin κ` **minus the interior edges of a prescribed
  sub-clique `S₀`** (the parent separator: its edges belong to the level
  above, so the shell may not spend them);
* each port `x : Fin t` belongs to the territory `terr x` and is joined to the
  hub vertices of its separator `S (terr x)` by **cross edges only**: the
  private interiors of the territories are *not* part of the shell (they are
  the hubs of the next level down), so the ports are pairwise non-adjacent.

Consequently every triangle of the shell uses at least one hub edge, and the
shell is exactly the configuration in which the hub's edge capacity is
contested by many overlapping separators.

Two specialisations fix the calibration:

* `shell_empty_hole_full_sep_eq_CS` — with one territory, `S₀ = ∅` and
  `S₁ = K` the shell **is** the complete split graph `CS(κ, t)`, so
  `shell_gap_of_CS` is literally `cs_gap_linear_full`;
* `shell_no_ports_eq_hub` — with no ports the shell is the hub with a hole,
  i.e. `CS(κ − |S₀|, |S₀|)` again.

The results proved here:

* `shell_value_le` — the shell LP ceiling for an arbitrary feasible dual
  triple `(a, b, c)` (weights on the hub's interior edges, on its edges
  meeting the hole, and on the cross edges);
* `shell_gap` — **unconditional in the shell's shape** (any hole, any number
  of arbitrarily overlapping separators, any port counts):
  `value ≤ ν₃(shell) + 10·(κ − |S₀|) + (1/2)·Σ_i p_i s_i`, whose linear term
  counts only the hub vertices outside the hole, and so is independent of
  `|S₀|`, of the `s_i` and of the number of ports;
* `shell_gap_linear` — the linear form
  `value ≤ ν₃(shell) + 11·((κ − |S₀|) + Σ p_i)` whenever the cross mass
  `Σ_i p_i s_i` is at most `2((κ − |S₀|) + Σ p_i)`;
* `shell_gap_portRich` (in `BoundedCliqueGap/ShellRich.lean`) — the opposite extreme,
  closed **exactly** (gap `≤ 0`) by the greedy donation
  `exists_clique_donation`: if every hub edge is admissible for more than `2κ`
  ports, every hub edge becomes a triangle of its own.

The residual regime — a large cross mass that is nevertheless not port-rich —
is the same donation obstruction as in rung I1; see `REPORT_I.md`.
-/

namespace BoundedCliqueGap

open Finset

section ShellDef

variable {kappa t m : ℕ}

/-- The **shell**: the hub clique `Fin κ` with the interior of `S₀` deleted,
together with cross edges from each port to its separator.  Ports are pairwise
non-adjacent. -/
def shell (S0 : Finset (Fin kappa)) (terr : Fin t → Fin m)
    (S : Fin m → Finset (Fin kappa)) : SimpleGraph (Fin kappa ⊕ Fin t) where
  Adj u v :=
    match u, v with
    | Sum.inl a, Sum.inl b => a ≠ b ∧ ¬ (a ∈ S0 ∧ b ∈ S0)
    | Sum.inl a, Sum.inr y => a ∈ S (terr y)
    | Sum.inr x, Sum.inl b => b ∈ S (terr x)
    | Sum.inr _, Sum.inr _ => False
  symm := by
    intro u v h; cases u <;> cases v
    · exact ⟨Ne.symm h.1, fun hc => h.2 ⟨hc.2, hc.1⟩⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor; intro u h; cases u
    · exact h.1 rfl
    · exact h

variable (S0 : Finset (Fin kappa)) (terr : Fin t → Fin m) (S : Fin m → Finset (Fin kappa))

@[simp] lemma shell_adj_inl_inl {a b : Fin kappa} :
    (shell S0 terr S).Adj (Sum.inl a) (Sum.inl b) ↔ a ≠ b ∧ ¬ (a ∈ S0 ∧ b ∈ S0) := Iff.rfl

@[simp] lemma shell_adj_inr_inr {x y : Fin t} :
    ¬ (shell S0 terr S).Adj (Sum.inr x) (Sum.inr y) := id

instance : DecidableRel (shell S0 terr S).Adj := by
  intro u v
  cases u <;> cases v <;> (dsimp [shell]; infer_instance)

/-! ## The two calibrating specialisations -/

/-! ## The dual weight of the shell -/

/-- The dual weight on the edge slots of the shell: `a` on a hub edge avoiding
the hole, `b` on a hub edge meeting the hole, `c` on a cross edge. -/
noncomputable def shellW (a b c : ℚ) (S0 : Finset (Fin kappa)) :
    Sym2 (Fin kappa ⊕ Fin t) → ℚ :=
  Sym2.lift ⟨fun u v =>
    match u, v with
    | Sum.inl x, Sum.inl y => if x ∈ S0 ∨ y ∈ S0 then b else a
    | Sum.inl _, Sum.inr _ => c
    | Sum.inr _, Sum.inl _ => c
    | Sum.inr _, Sum.inr _ => 0, by
    rintro (x | x) (y | y) <;> first | rfl | simp [or_comm]⟩

variable (a b c : ℚ)

@[simp] lemma shellW_hub (x y : Fin kappa) :
    shellW (t := t) a b c S0 s(Sum.inl x, Sum.inl y) = if x ∈ S0 ∨ y ∈ S0 then b else a := rfl

@[simp] lemma shellW_cross (x : Fin kappa) (y : Fin t) :
    shellW a b c S0 s(Sum.inl x, Sum.inr y) = c := rfl

@[simp] lemma shellW_cross' (x : Fin kappa) (y : Fin t) :
    shellW a b c S0 s(Sum.inr y, Sum.inl x) = c := rfl

@[simp] lemma shellW_port (x y : Fin t) :
    shellW (kappa := kappa) a b c S0 s(Sum.inr x, Sum.inr y) = 0 := rfl

lemma shellW_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : Sym2 (Fin kappa ⊕ Fin t)) : 0 ≤ shellW a b c S0 e := by
  induction e with
  | _ u v =>
    cases u <;> cases v <;>
      simp only [shellW_hub, shellW_cross, shellW_cross', shellW_port] <;>
      first | assumption | exact le_rfl | (split_ifs <;> assumption)

/-- **Dual feasibility for the shell.**  The four inequalities `1 ≤ 3a`,
`1 ≤ a + 2b`, `1 ≤ a + 2c`, `1 ≤ b + 2c` say exactly that every triangle of
the shell carries total weight at least one: a hub triangle has either three
hole-free edges or one hole-free edge and two meeting the hole, and a port
triangle has one hub edge and two cross edges. -/
lemma shellW_triangle_ge (h3a : 1 ≤ 3 * a) (hab : 1 ≤ a + 2 * b)
    (hac : 1 ≤ a + 2 * c) (hbc : 1 ≤ b + 2 * c)
    (T : Finset (Fin kappa ⊕ Fin t)) (hT : IsTriangle (shell S0 terr S) T) :
    1 ≤ ∑ e ∈ triEdges T, shellW a b c S0 e := by
  have h3 := hT.1
  have hle : (privVerts T).card ≤ 3 := by have := card_hub_add_card_priv T; omega
  rcases hn : (privVerts T).card with _ | _ | _ | _ | n
  · -- three hub vertices: at most one lies in the hole
    obtain ⟨u, v, w, huv, huw, hvw, hTe⟩ := shape_priv_zero h3 hn
    have huT : Sum.inl u ∈ T := by rw [hTe]; simp
    have hvT : Sum.inl v ∈ T := by rw [hTe]; simp
    have hwT : Sum.inl w ∈ T := by rw [hTe]; simp
    have hadjuv := hT.2 _ huT _ hvT (by simpa using huv)
    have hadjuw := hT.2 _ huT _ hwT (by simpa using huw)
    have hadjvw := hT.2 _ hvT _ hwT (by simpa using hvw)
    rw [shell_adj_inl_inl] at hadjuv hadjuw hadjvw
    rw [sum_triEdges_three _ (by simpa using huv) (by simpa using huw) (by simpa using hvw) hTe]
    simp only [shellW_hub]
    by_cases hu : u ∈ S0
    · have hv : v ∉ S0 := fun hc => hadjuv.2 ⟨hu, hc⟩
      have hw : w ∉ S0 := fun hc => hadjuw.2 ⟨hu, hc⟩
      rw [if_pos (Or.inl hu), if_pos (Or.inl hu), if_neg (fun hc => hc.elim hv hw)]
      linarith
    · by_cases hv : v ∈ S0
      · have hw : w ∉ S0 := fun hc => hadjvw.2 ⟨hv, hc⟩
        rw [if_pos (Or.inr hv), if_neg (fun hc => hc.elim hu hw), if_pos (Or.inl hv)]
        linarith
      · by_cases hw : w ∈ S0
        · rw [if_neg (fun hc => hc.elim hu hv), if_pos (Or.inr hw), if_pos (Or.inr hw)]
          linarith
        · rw [if_neg (fun hc => hc.elim hu hv), if_neg (fun hc => hc.elim hu hw),
            if_neg (fun hc => hc.elim hv hw)]
          linarith
  · -- two hub vertices and one port
    obtain ⟨u, v, y, huv, hTe⟩ := shape_priv_one h3 hn
    rw [sum_triEdges_three _ (by simpa using huv) (by simp) (by simp) hTe]
    simp only [shellW_hub, shellW_cross]
    split_ifs <;> linarith
  · -- two ports in a triangle: impossible, ports are non-adjacent
    obtain ⟨u, x, y, hxy, hTe⟩ := shape_priv_two h3 hn
    have hxT : Sum.inr x ∈ T := by rw [hTe]; simp
    have hyT : Sum.inr y ∈ T := by rw [hTe]; simp
    exact absurd (hT.2 _ hxT _ hyT (by simpa using hxy)) (shell_adj_inr_inr S0 terr S)
  · obtain ⟨x, y, z, hxy, -, -, hTe⟩ := shape_priv_three h3 hn
    have hxT : Sum.inr x ∈ T := by rw [hTe]; simp
    have hyT : Sum.inr y ∈ T := by rw [hTe]; simp
    exact absurd (hT.2 _ hxT _ hyT (by simpa using hxy)) (shell_adj_inr_inr S0 terr S)
  · omega

/-! ## The three edge classes of the shell -/

/-- The hub edge slots avoiding the hole. -/
noncomputable def holeFreeEdgeSet (S0 : Finset (Fin kappa)) :
    Finset (Sym2 (Fin kappa ⊕ Fin t)) :=
  pairEdges (fun z : {a : Fin kappa // a ∉ S0} => (Sum.inl z.1 : Fin kappa ⊕ Fin t))

/-- The hub edge slots meeting the hole. -/
noncomputable def holeMeetEdgeSet (S0 : Finset (Fin kappa)) :
    Finset (Sym2 (Fin kappa ⊕ Fin t)) :=
  (S0 ×ˢ (Finset.univ \ S0)).image (fun q => s(Sum.inl q.1, Sum.inl q.2))

lemma card_holeFreeEdgeSet :
    (holeFreeEdgeSet (t := t) S0).card = (kappa - S0.card).choose 2 := by
  classical
  rw [holeFreeEdgeSet, card_pairEdges (f := fun z : {a : Fin kappa // a ∉ S0} =>
    (Sum.inl z.1 : Fin kappa ⊕ Fin t)) (fun z z' hz => Subtype.ext (Sum.inl_injective hz))]
  congr 1
  rw [Fintype.card_subtype]
  have h : (univ.filter (fun a : Fin kappa => a ∉ S0)) = univ \ S0 := by
    ext a; simp
  rw [h, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]

lemma card_holeMeetEdgeSet_le :
    (holeMeetEdgeSet (t := t) S0).card ≤ S0.card * (kappa - S0.card) := by
  classical
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]

lemma holeFree_weight (e : Sym2 (Fin kappa ⊕ Fin t)) (he : e ∈ holeFreeEdgeSet (t := t) S0) :
    shellW a b c S0 e = a := by
  obtain ⟨x, y, -, rfl⟩ := mem_pairEdges_iff.1 he
  rw [shellW_hub, if_neg]
  rintro (h | h)
  · exact x.2 h
  · exact y.2 h

lemma holeMeet_weight (e : Sym2 (Fin kappa ⊕ Fin t)) (he : e ∈ holeMeetEdgeSet (t := t) S0) :
    shellW a b c S0 e = b := by
  classical
  simp only [holeMeetEdgeSet, Finset.mem_image, Finset.mem_product] at he
  obtain ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩ := he
  rw [shellW_hub, if_pos (Or.inl hx)]

lemma cross_weight (i : Fin m) (e : Sym2 (Fin kappa ⊕ Fin t))
    (he : e ∈ crossEdgeSet terr S i) : shellW a b c S0 e = c := by
  classical
  simp only [crossEdgeSet, Finset.mem_image, Finset.mem_product] at he
  obtain ⟨⟨u, x⟩, -, rfl⟩ := he
  rfl

/-- The edges of the shell are covered by the three classes. -/
lemma shell_edges_subset :
    (shell S0 terr S).edgeFinset ⊆
      (holeFreeEdgeSet (t := t) S0 ∪ holeMeetEdgeSet (t := t) S0)
        ∪ univ.biUnion (fun i => crossEdgeSet terr S i) := by
  classical
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e with
  | _ u v =>
    have hadj : (shell S0 terr S).Adj u v := he
    cases u with
    | inl x =>
      cases v with
      | inl y =>
        obtain ⟨hne, hnot⟩ := hadj
        refine Finset.mem_union_left _ ?_
        by_cases hx : x ∈ S0
        · have hy : y ∉ S0 := fun hy => hnot ⟨hx, hy⟩
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, by simp [hy]⟩, rfl⟩
        · by_cases hy : y ∈ S0
          · refine Finset.mem_union_right _ ?_
            refine Finset.mem_image.2 ⟨(y, x), Finset.mem_product.2 ⟨hy, by simp [hx]⟩, ?_⟩
            exact Sym2.eq_swap
          · exact Finset.mem_union_left _
              (mem_pairEdges_iff.2 ⟨⟨x, hx⟩, ⟨y, hy⟩, by simpa using hne, rfl⟩)
      | inr y =>
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨terr y, mem_univ _, ?_⟩)
        exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hadj, mem_privSet_iff.2 rfl⟩, rfl⟩
    | inr x =>
      cases v with
      | inl y =>
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨terr x, mem_univ _, ?_⟩)
        refine Finset.mem_image.2 ⟨(y, x), Finset.mem_product.2 ⟨hadj, mem_privSet_iff.2 rfl⟩, ?_⟩
        exact Sym2.eq_swap
      | inr y => exact absurd hadj (shell_adj_inr_inr S0 terr S)

/-- **The shell LP ceiling.**  For any feasible dual triple `(a,b,c)`. -/
theorem shell_value_le (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h3a : 1 ≤ 3 * a) (hab : 1 ≤ a + 2 * b) (hac : 1 ≤ a + 2 * c) (hbc : 1 ≤ b + 2 * c)
    (F : FracPacking (shell S0 terr S)) :
    F.value ≤ a * (((kappa - S0.card).choose 2 : ℕ) : ℚ)
      + b * ((S0.card : ℚ) * ((kappa - S0.card : ℕ) : ℚ))
      + c * ∑ i : Fin m, ((privCard terr i : ℚ) * (sepCard S i : ℚ)) := by
  classical
  have hnn : ∀ e : Sym2 (Fin kappa ⊕ Fin t), 0 ≤ shellW a b c S0 e :=
    shellW_nonneg (t := t) S0 a b c ha hb hc
  refine le_trans (value_le_weight_sum (shellW a b c S0) (fun e _ => hnn e)
    (shellW_triangle_ge S0 terr S a b c h3a hab hac hbc) F) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (shell_edges_subset S0 terr S)
    (fun e _ _ => hnn e)) ?_
  refine le_trans (sumQ_union_le _ _ _ hnn) ?_
  have h1 : ∑ e ∈ (holeFreeEdgeSet (t := t) S0 ∪ holeMeetEdgeSet (t := t) S0),
      shellW a b c S0 e
      ≤ a * (((kappa - S0.card).choose 2 : ℕ) : ℚ)
        + b * ((S0.card : ℚ) * ((kappa - S0.card : ℕ) : ℚ)) := by
    refine le_trans (sumQ_union_le _ _ _ hnn) ?_
    have e1 : ∑ e ∈ holeFreeEdgeSet (t := t) S0, shellW a b c S0 e
        = a * (((kappa - S0.card).choose 2 : ℕ) : ℚ) := by
      rw [Finset.sum_congr rfl (fun e he => holeFree_weight S0 a b c e he), Finset.sum_const,
        card_holeFreeEdgeSet, nsmul_eq_mul, mul_comm]
    have e2 : ∑ e ∈ holeMeetEdgeSet (t := t) S0, shellW a b c S0 e
        ≤ b * ((S0.card : ℚ) * ((kappa - S0.card : ℕ) : ℚ)) := by
      rw [Finset.sum_congr rfl (fun e he => holeMeet_weight S0 a b c e he), Finset.sum_const,
        nsmul_eq_mul]
      have := card_holeMeetEdgeSet_le (t := t) S0
      have hcast : ((holeMeetEdgeSet (t := t) S0).card : ℚ)
          ≤ (S0.card : ℚ) * ((kappa - S0.card : ℕ) : ℚ) := by exact_mod_cast this
      nlinarith
    linarith
  have h2 : ∑ e ∈ univ.biUnion (fun i => crossEdgeSet terr S i), shellW a b c S0 e
      ≤ c * ∑ i : Fin m, ((privCard terr i : ℚ) * (sepCard S i : ℚ)) := by
    refine le_trans (sumQ_biUnion_le _ _ _ hnn) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.sum_congr rfl (fun e he => cross_weight S0 terr S a b c i e he), Finset.sum_const,
      card_crossEdgeSet, nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_rfl
  linarith

/-! ## The shell's own packing number: the hub with a hole -/

/-- The hub with the hole `S₀` removed is a copy of the complete split graph
`CS(κ − |S₀|, |S₀|)` inside the shell: the non-hole hub vertices form a clique,
the hole vertices are pairwise non-adjacent and joined to all of them. -/
lemma nu3_CS_le_nu3_shell :
    nu3 (CS (Fin (kappa - S0.card)) (Fin S0.card)) ≤ nu3 (shell S0 terr S) := by
  classical
  have hcard : (S0ᶜ : Finset (Fin kappa)).card = kappa - S0.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  set ec : Fin (kappa - S0.card) ≃ {a : Fin kappa // a ∈ S0ᶜ} :=
    (finCongr hcard.symm).trans (S0ᶜ).equivFin.symm with hec
  set eh : Fin S0.card ≃ {a : Fin kappa // a ∈ S0} := S0.equivFin.symm with heh
  have hcn : ∀ j, (ec j).1 ∉ S0 := by
    intro j; exact Finset.mem_compl.1 (ec j).2
  have hhn : ∀ j, (eh j).1 ∈ S0 := fun j => (eh j).2
  refine nu3_le_of_embedding
    ⟨fun z => Sum.elim (fun j => (Sum.inl (ec j).1 : Fin kappa ⊕ Fin t))
      (fun j => (Sum.inl (eh j).1 : Fin kappa ⊕ Fin t)) z, ?_⟩ ?_
  · rintro (j | j) (j' | j') hz <;> simp only [Sum.elim_inl, Sum.elim_inr] at hz
    · have h : (ec j).1 = (ec j').1 := by injection hz
      exact congrArg Sum.inl (ec.injective (Subtype.ext h))
    · have h : (ec j).1 = (eh j').1 := by injection hz
      exact absurd (by rw [h]; exact hhn j') (hcn j)
    · have h : (eh j).1 = (ec j').1 := by injection hz
      exact absurd (by rw [← h]; exact hhn j) (hcn j')
    · have h : (eh j).1 = (eh j').1 := by injection hz
      exact congrArg Sum.inr (eh.injective (Subtype.ext h))
  · rintro (j | j) (j' | j') hadj <;>
      simp only [Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr]
    · exact ⟨fun hcon => (CS_adj_inl_inl.1 hadj) (ec.injective (Subtype.ext hcon)),
        fun hc => (hcn j) hc.1⟩
    · exact ⟨fun hc => (hcn j) (by rw [hc]; exact hhn j'), fun hc => (hcn j) hc.1⟩
    · exact ⟨fun hc => (hcn j') (by rw [← hc]; exact hhn j), fun hc => (hcn j') hc.2⟩
    · exact absurd hadj (by simp)

/-! ## The shell gap -/

/-- **The shell gap, unconditional in the shell's shape.**  For an arbitrary
hole `S₀`, arbitrarily overlapping separators and arbitrary port counts,
`value ≤ ν₃(shell) + 10·(κ − |S₀|) + (1/2)·Σ_i p_i s_i`.  The linear term
counts only the hub vertices *outside* the hole — it is independent of `|S₀|`,
of the `s_i` and of the number of ports; the last term is the cross mass, the
residual donation term discussed in `REPORT_I.md`. -/
theorem shell_gap (F : FracPacking (shell S0 terr S)) :
    F.value ≤ (nu3 (shell S0 terr S) : ℚ) + 10 * ((kappa - S0.card : ℕ) : ℚ)
      + (1 / 2) * ∑ i : Fin m, ((privCard terr i : ℚ) * (sepCard S i : ℚ)) := by
  classical
  have hnuCS : (nu3 (CS (Fin (kappa - S0.card)) (Fin S0.card)) : ℚ)
      ≤ (nu3 (shell S0 terr S) : ℚ) := by
    exact_mod_cast nu3_CS_le_nu3_shell S0 terr S
  have hpk : ((kappa - S0.card : ℕ) : ℚ) ≤ (kappa : ℚ) := by
    exact_mod_cast Nat.sub_le kappa S0.card
  have hcross : (0 : ℚ) ≤ ∑ i : Fin m, ((privCard terr i : ℚ) * (sepCard S i : ℚ)) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hkappa : (0 : ℚ) ≤ (kappa : ℚ) := by positivity
  by_cases hcase : S0.card ≤ kappa - S0.card
  · have h := shell_value_le S0 terr S (1/3) (1/3) (1/3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) F
    have hlow := nu3_CS_portPoor_ge (kappa - S0.card) S0.card hcase
    rw [cast_choose_two] at h
    linarith
  · have h := shell_value_le S0 terr S 1 0 (1/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) F
    have hlow : (((kappa - S0.card).choose 2 : ℕ) : ℚ)
        ≤ (nu3 (CS (Fin (kappa - S0.card)) (Fin S0.card)) : ℚ) := by
      exact_mod_cast nu3_CS_ge_choose (Nat.le_of_lt (Nat.lt_of_not_le hcase))
    linarith

end ShellDef

/-! ## Axiom audit -/

end BoundedCliqueGap
