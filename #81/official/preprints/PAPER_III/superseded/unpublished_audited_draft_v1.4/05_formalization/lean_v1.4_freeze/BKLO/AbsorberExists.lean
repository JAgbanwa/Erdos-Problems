/-
# Absorber existence for every triangle-divisible edge set (BKLO §8.1).

This is the combinatorial heart of §8 — the `F`-expansion construction, for `F = K₃` — carried out
in the edge-set model over the vertex type `ℕ`, so that **fresh vertices are available**.  (They are
essential: over a fixed finite vertex type the statement fails.)

The route:

1. `veblen` — a loopless edge set with all degrees even is an edge-disjoint union of cycles.
2. `split_group` — the family of cycles splits into groups of at most three cycles, each of total
   length divisible by `3` (which is what an absorber requires).
3. `hasAbs_group` — a group is handled by iterating one *round*: relocate the group onto fresh
   vertices (`hasAbs_relocate`) and shorten every cycle (`round_reduce`).  Triangles are peeled off
   (they are decomposable), and the process terminates at a group of `4`- and `5`-cycles, i.e. at
   `C₄ ⊎ C₅`, `3·C₄` or `3·C₅`, which the explicit gadgets of `BKLO.Gadgets` absorb.
4. `hasAbs_fam`, `absorber_of_triDivisible` — assembling the groups with `isAbsorber_union`.

The corrected form of the skeleton's `ExpansionChain` (see `BKLO.Refutations` for why the original
is false) is `ExpansionChainNat`, proved at the end.
-/
import BKLO.Families
import BKLO.Veblen
import BKLO.Degeneracy

open Finset

namespace BKLO

/-- The total length of the cycles of length `≥ 6`: the measure that the reduction round
decreases. -/
def bigLen (L : List (List ℕ)) : ℕ := ((L.filter (fun l => 6 ≤ l.length)).map List.length).sum

/-! ### Permutation invariance -/

theorem cycFamEdges_perm {L L' : List (List ℕ)} (h : L.Perm L') :
    cycFamEdges L = cycFamEdges L' := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [cycFamEdges_cons, cycFamEdges_cons, ih]
  | swap x y l =>
    simp only [cycFamEdges_cons]
    ext e; simp only [Finset.mem_union]; tauto
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem totalLen_perm {L L' : List (List ℕ)} (h : L.Perm L') : totalLen L = totalLen L' :=
  (h.map List.length).sum_eq

theorem bigLen_perm {L L' : List (List ℕ)} (h : L.Perm L') : bigLen L = bigLen L' := by
  unfold bigLen
  exact ((h.filter _).map _).sum_eq

theorem EdgeDisjFam.perm {L L' : List (List ℕ)} (h : L.Perm L') (hf : EdgeDisjFam L) :
    EdgeDisjFam L' :=
  ⟨fun l hl => hf.nodup l (h.mem_iff.2 hl), fun l hl => hf.three l (h.mem_iff.2 hl),
    (List.Perm.pairwise_iff (fun hd => hd.symm) h).1 hf.pdisj⟩

theorem EdgeDisjFam.sublist {L L' : List (List ℕ)} (h : L'.Sublist L) (hf : EdgeDisjFam L) :
    EdgeDisjFam L' :=
  ⟨fun l hl => hf.nodup l (h.mem hl), fun l hl => hf.three l (h.mem hl), hf.pdisj.sublist h⟩

theorem cycFamEdges_append (L L' : List (List ℕ)) :
    cycFamEdges (L ++ L') = cycFamEdges L ∪ cycFamEdges L' := by
  induction L with
  | nil => simp
  | cons l L ih =>
    rw [List.cons_append, cycFamEdges_cons, cycFamEdges_cons, ih, Finset.union_assoc]

theorem cycFamEdges_append_disjoint {L L' : List (List ℕ)} (h : EdgeDisjFam (L ++ L')) :
    Disjoint (cycFamEdges L) (cycFamEdges L') := by
  induction L with
  | nil => simp
  | cons l L ih =>
    rw [cycFamEdges_cons]
    refine Finset.disjoint_union_left.2 ⟨?_, ih h.tail⟩
    refine disjoint_cycFamEdges (fun l' hl' => ?_)
    exact (List.pairwise_cons.1 h.pdisj).1 l' (List.mem_append_right _ hl')

theorem totalLen_append (L L' : List (List ℕ)) :
    totalLen (L ++ L') = totalLen L + totalLen L' := by
  simp [totalLen]

theorem bigLen_le_of_sublist {L L' : List (List ℕ)} (h : L'.Sublist L) : bigLen L' ≤ bigLen L := by
  have key : ∀ {X Y : List ℕ}, X.Sublist Y → X.sum ≤ Y.sum := by
    intro X Y hXY
    induction hXY with
    | slnil => simp
    | cons a _ ih => simp only [List.sum_cons]; omega
    | cons₂ a _ ih => simp only [List.sum_cons]; omega
  have hs : (((L'.filter (fun l => 6 ≤ l.length)).map List.length)).Sublist
      (((L.filter (fun l => 6 ≤ l.length)).map List.length)) :=
    (List.Sublist.filter _ h).map _
  exact key hs

/-- Some bound exceeds every vertex of every cycle of a family. -/
theorem exists_bound (L : List (List ℕ)) : ∃ b, ∀ l ∈ L, ∀ v ∈ l, v < b := by
  classical
  refine ⟨L.flatten.toFinset.sup id + 1, fun l hl v hv => ?_⟩
  have : v ≤ L.flatten.toFinset.sup id :=
    Finset.le_sup (f := id) (List.mem_toFinset.2 (List.mem_flatten.2 ⟨l, hl, hv⟩))
  omega

/-! ### Splitting the family into small groups -/

/-- **Grouping.**  A nonempty family of cycles whose total length is divisible by `3` splits off a
nonempty group of at most three cycles whose total length is again divisible by `3`: take a cycle of
length divisible by `3` if there is one, else a cycle of length `≡ 1` together with one of length
`≡ 2`, else three cycles of the same residue. -/
theorem split_group {L : List (List ℕ)} (hne : L ≠ []) (hdvd : 3 ∣ totalLen L) :
    ∃ G R : List (List ℕ), L.Perm (G ++ R) ∧ G ≠ [] ∧ G.length ≤ 3 ∧ 3 ∣ totalLen G := by
  classical
  by_cases h0 : ∃ l ∈ L, l.length % 3 = 0
  · obtain ⟨l, hl, h⟩ := h0
    exact ⟨[l], L.erase l, List.perm_cons_erase hl, by simp, by simp,
      by simp only [totalLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega⟩
  push_neg at h0
  by_cases h12 : ∃ l₁ ∈ L, ∃ l₂ ∈ L.erase l₁, l₁.length % 3 = 1 ∧ l₂.length % 3 = 2
  · obtain ⟨l₁, hl₁, l₂, hl₂, e₁, e₂⟩ := h12
    refine ⟨[l₁, l₂], (L.erase l₁).erase l₂, ?_, by simp, by simp, ?_⟩
    · exact (List.perm_cons_erase hl₁).trans ((List.perm_cons_erase hl₂).cons l₁)
    · simp only [totalLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  push_neg at h12
  -- every cycle has the same nonzero residue mod `3`
  have hsame : ∀ x ∈ L, ∀ y ∈ L, x.length % 3 = y.length % 3 := by
    intro x hx y hy
    have hx0 := h0 x hx
    have hy0 := h0 y hy
    by_contra hne'
    have hxy : x ≠ y := by rintro rfl; exact hne' rfl
    rcases Nat.lt_or_ge (x.length % 3) (y.length % 3) with hlt | hge
    · have h1 : x.length % 3 = 1 := by omega
      have h2 : y.length % 3 = 2 := by omega
      exact h12 x hx y ((List.mem_erase_of_ne hxy.symm).2 hy) h1 h2
    · have h1 : y.length % 3 = 1 := by omega
      have h2 : x.length % 3 = 2 := by omega
      exact h12 y hy x ((List.mem_erase_of_ne hxy).2 hx) h1 h2
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact absurd rfl hne
  · exfalso
    have ha0 := h0 a (by simp)
    simp only [totalLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hdvd
    omega
  · exfalso
    have ha0 := h0 a (by simp)
    have hab := hsame a (by simp) b (by simp)
    simp only [totalLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hdvd
    omega
  · have ha0 := h0 a (by simp)
    have hab := hsame a (by simp) b (by simp)
    have hac := hsame a (by simp) c (by simp)
    refine ⟨[a, b, c], t, List.Perm.refl _, by simp, by simp, ?_⟩
    simp only [totalLen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-! ### The measure decreases -/

@[simp] theorem bigLen_nil : bigLen [] = 0 := rfl

theorem bigLen_cons (l : List ℕ) (L : List (List ℕ)) :
    bigLen (l :: L) = (if 6 ≤ l.length then l.length else 0) + bigLen L := by
  by_cases h : 6 ≤ l.length <;> simp [bigLen, h]

theorem bigLen_le_of_forall₂ {G G' : List (List ℕ)}
    (h : List.Forall₂ (fun l l' => (l.length ≤ 5 → l'.length ≤ 5) ∧
      (6 ≤ l.length → l'.length < l.length)) G G') : bigLen G' ≤ bigLen G := by
  induction h with
  | nil => simp
  | @cons l l' A B hp _ ih =>
    rw [bigLen_cons, bigLen_cons]
    rcases Nat.lt_or_ge l.length 6 with hc | hc
    · have := hp.1 (by omega); split_ifs <;> omega
    · have := hp.2 hc; split_ifs <;> omega

theorem bigLen_lt {G G' : List (List ℕ)}
    (h : List.Forall₂ (fun l l' => (l.length ≤ 5 → l'.length ≤ 5) ∧
      (6 ≤ l.length → l'.length < l.length)) G G')
    (hex : ∃ l ∈ G, 6 ≤ l.length) : bigLen G' < bigLen G := by
  revert hex
  induction h with
  | nil => intro hex; simp at hex
  | @cons l l' A B hp ht ih =>
    intro hex
    rw [bigLen_cons, bigLen_cons]
    have hmono : (if 6 ≤ l'.length then l'.length else 0) ≤
        (if 6 ≤ l.length then l.length else 0) := by
      rcases Nat.lt_or_ge l.length 6 with hc | hc
      · have := hp.1 (by omega); split_ifs <;> omega
      · have := hp.2 hc; split_ifs <;> omega
    obtain ⟨x, hx, hx6⟩ := hex
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h1 := hp.2 hx6
      have h2 := bigLen_le_of_forall₂ ht
      split_ifs <;> omega
    · have := ih ⟨x, hx', hx6⟩
      omega

theorem three_dvd_of_forall₂ {G G' : List (List ℕ)}
    (h : List.Forall₂ (fun l l' => 3 ∣ l.length + l'.length) G G') (hG : 3 ∣ totalLen G) :
    3 ∣ totalLen G' := by
  have key : ∀ {A B : List (List ℕ)},
      List.Forall₂ (fun l l' => 3 ∣ l.length + l'.length) A B → 3 ∣ totalLen A + totalLen B := by
    intro A B hAB
    induction hAB with
    | nil => simp
    | cons hp _ ih => simp only [totalLen_cons]; omega
  have := key h
  omega

/-! ### The group recursion -/

/-- **A group of at most three cycles has an absorber.**  Strong induction on the pair
(`bigLen`, `totalLen`): triangles are peeled off, a cycle of length `≥ 6` triggers a reduction
round, and otherwise we are at one of the three terminal gadgets. -/
theorem hasAbs_group : ∀ (m t : ℕ) (G : List (List ℕ)) (b : ℕ),
    bigLen G ≤ m → totalLen G ≤ t → EdgeDisjFam G → (∀ l ∈ G, ∀ v ∈ l, v < b) →
    G.length ≤ 3 → 3 ∣ totalLen G → HasAbs b (cycFamEdges G) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
    intro t
    induction t using Nat.strong_induction_on with
    | _ t IHt =>
      intro G b hm ht hed hb hcard hdvd
      by_cases hnil : G = []
      · subst hnil; simpa using hasAbs_empty b
      by_cases h3 : ∃ l ∈ G, l.length = 3
      · -- peel off a triangle
        obtain ⟨l, hl, hl3⟩ := h3
        have hperm : G.Perm (l :: G.erase l) := List.perm_cons_erase hl
        set G' := G.erase l with hG'
        have hsub : G'.Sublist G := List.erase_sublist
        have hed' : EdgeDisjFam G' := hed.sublist hsub
        have hedc : EdgeDisjFam (l :: G') := hed.perm hperm
        have hdisj : Disjoint (cycEdges l) (cycFamEdges G') := by
          have := cycFamEdges_append_disjoint (L := [l]) (L' := G') (by simpa using hedc)
          simpa using this
        have hlen : totalLen G = l.length + totalLen G' := by
          rw [totalLen_perm hperm]; simp
        have hbelow_l : Below b (cycEdges l) := by
          intro v hv
          exact hb l hl v (List.mem_toFinset.1 (supp_cycEdges l hv))
        have hbelow_G' : Below b (cycFamEdges G') := by
          intro v hv
          have := supp_cycFamEdges G' hv
          rw [List.mem_toFinset, List.mem_flatten] at this
          obtain ⟨l', hl', hv'⟩ := this
          exact hb l' (hsub.mem hl') v hv'
        have hcyc : TriDecomp (cycEdges l) := triDecomp_cyc3 (hed.nodup l hl) hl3
        have key : HasAbs b (cycEdges l ∪ cycFamEdges G') := by
          refine hasAbs_union hbelow_l hbelow_G' hdisj (hasAbs_of_triDecomp hcyc) ?_
          intro b' hbb
          refine IHt (totalLen G') ?_ G' b' (le_trans (bigLen_le_of_sublist hsub) hm) le_rfl hed'
            ?_ ?_ ?_
          · omega
          · exact fun l' hl' v hv => lt_of_lt_of_le (hb l' (hsub.mem hl') v hv) hbb
          · exact le_trans (List.Sublist.length_le hsub) hcard
          · omega
        · rw [cycFamEdges_perm hperm]
          simpa using key
      · by_cases h6 : ∃ l ∈ G, 6 ≤ l.length
        · -- one reduction round
          have h4 : ∀ l ∈ G, 4 ≤ l.length := by
            intro l hl
            have := hed.three l hl
            rcases Nat.lt_or_ge l.length 4 with h | h
            · exact absurd ⟨l, hl, by omega⟩ h3
            · exact h
          obtain ⟨G', b', hbb, hvd', hmem', hall, htrans⟩ := round_reduce hed hb h4
          refine htrans ?_
          have hedG' : EdgeDisjFam G' := hvd'.toEdgeDisj
          refine IHm (bigLen G') ?_ (totalLen G') G' b' le_rfl le_rfl hedG' ?_ ?_ ?_
          · refine lt_of_lt_of_le ?_ hm
            exact bigLen_lt (hall.imp (fun _ _ h => ⟨h.2.1, h.2.2⟩)) h6
          · exact fun l hl v hv => (hmem' l hl v hv).2
          · rw [← hall.length_eq]; exact hcard
          · exact three_dvd_of_forall₂ (hall.imp (fun _ _ h => h.1)) hdvd
        · -- terminal: all cycles have length 4 or 5
          refine terminal_group hed hb ?_ hcard hdvd
          intro l hl
          have h3' := hed.three l hl
          have : ¬ (l.length = 3) := fun h => h3 ⟨l, hl, h⟩
          have : ¬ (6 ≤ l.length) := fun h => h6 ⟨l, hl, h⟩
          omega

/-! ### The whole family -/

theorem hasAbs_fam : ∀ (n : ℕ) (L : List (List ℕ)) (b : ℕ), L.length ≤ n → EdgeDisjFam L →
    (∀ l ∈ L, ∀ v ∈ l, v < b) → 3 ∣ totalLen L → HasAbs b (cycFamEdges L) := by
  intro n
  induction n with
  | zero =>
    intro L b hn _ _ _
    have : L = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hn)
    subst this; simpa using hasAbs_empty b
  | succ n IH =>
    intro L b hn hed hb hdvd
    by_cases hnil : L = []
    · subst hnil; simpa using hasAbs_empty b
    obtain ⟨G, R, hperm, hGne, hGcard, hGdvd⟩ := split_group hnil hdvd
    have hedGR : EdgeDisjFam (G ++ R) := hed.perm hperm
    have hedG : EdgeDisjFam G := hedGR.sublist (List.sublist_append_left _ _)
    have hedR : EdgeDisjFam R := hedGR.sublist (List.sublist_append_right _ _)
    have hbGR : ∀ l ∈ G ++ R, ∀ v ∈ l, v < b := by
      intro l hl v hv
      exact hb l (hperm.mem_iff.2 hl) v hv
    have hlenR : R.length < L.length := by
      have := hperm.length_eq
      simp only [List.length_append] at this
      have : 0 < G.length := List.length_pos_of_ne_nil hGne
      omega
    have hdvdR : 3 ∣ totalLen R := by
      have := totalLen_perm hperm
      rw [totalLen_append] at this
      omega
    have hdisj : Disjoint (cycFamEdges G) (cycFamEdges R) := cycFamEdges_append_disjoint hedGR
    have hbelowG : Below b (cycFamEdges G) := by
      intro v hv
      have := supp_cycFamEdges G hv
      rw [List.mem_toFinset, List.mem_flatten] at this
      obtain ⟨l, hl, hv'⟩ := this
      exact hbGR l (List.mem_append_left _ hl) v hv'
    have hbelowR : Below b (cycFamEdges R) := by
      intro v hv
      have := supp_cycFamEdges R hv
      rw [List.mem_toFinset, List.mem_flatten] at this
      obtain ⟨l, hl, hv'⟩ := this
      exact hbGR l (List.mem_append_right _ hl) v hv'
    have key : HasAbs b (cycFamEdges G ∪ cycFamEdges R) := by
      refine hasAbs_union hbelowG hbelowR hdisj ?_ ?_
      · exact hasAbs_group (bigLen G) (totalLen G) G b le_rfl le_rfl hedG
          (fun l hl => hbGR l (List.mem_append_left _ hl)) hGcard hGdvd
      · intro b' hbb
        refine IH R b' (by omega) hedR ?_ hdvdR
        exact fun l hl v hv => lt_of_lt_of_le (hbGR l (List.mem_append_right _ hl) v hv) hbb
    rw [cycFamEdges_perm hperm, cycFamEdges_append]
    exact key

/-! ### The main theorem -/

/-- **Absorber existence (BKLO Lemma 8.8, `F = K₃`).**  Every loopless triangle-divisible edge set
has an absorber.  Fresh vertices are used, which is why the statement is over `ℕ`. -/
theorem absorber_of_triDivisible {H : Finset (Sym2 ℕ)} (hloop : ∀ e ∈ H, ¬ e.IsDiag)
    (hdiv : TriDivisible H) : ∃ A : Finset (Sym2 ℕ), IsAbsorber A H := by
  obtain ⟨L, hed, hL⟩ := veblen H hloop hdiv.1
  obtain ⟨b, hb⟩ := exists_bound L
  have hdvd : 3 ∣ totalLen L := by
    rw [← card_cycFamEdges hed, hL]; exact hdiv.2
  obtain ⟨A, hA, -, -, -⟩ := hasAbs_fam L.length L b le_rfl hed hb hdvd
  exact ⟨A, hL ▸ hA⟩

/-- **Absorber existence with degeneracy control (BKLO Lemma 8.8 with bounded rooted
degeneracy).**  Every loopless triangle-divisible edge set living below `b` has an absorber which
uses no new vertex below `b`, has no edge inside the absorbed set, and is `9`-degenerate in the
order of `ℕ`.

The bound `9` is exactly what the triangle threshold `9/10` supports: in a host graph with
`δ(G) ≥ (9/10 + ε)n` every set of at most `9` vertices has a linear common neighbourhood, so such an
absorber embeds greedily (`BKLO.exists_embedding`). -/
theorem sparseAbsorberExistence_nine : SparseAbsorberExistence 9 := by
  intro b H hloop hbelow hdiv
  obtain ⟨L, hed, hL⟩ := veblen H hloop hdiv.1
  have hb : ∀ l ∈ L, ∀ v ∈ l, v < b := by
    intro l hl v hv
    refine hbelow v ?_
    rw [← hL]
    exact mem_supp_cycFamEdges hl (by have := hed.three l hl; omega) hv
  have hdvd : 3 ∣ totalLen L := by
    rw [← card_cycFamEdges hed, hL]; exact hdiv.2
  obtain ⟨A, hA, ht, hs, hn⟩ := hasAbs_fam L.length L b le_rfl hed hb hdvd
  refine ⟨A, ⟨hL ▸ hA, ht, ?_, hn⟩⟩
  intro v hv
  rcases hs v hv with hx | hx
  · exact Or.inl (hL ▸ hx)
  · exact Or.inr hx

/-- **The corrected expansion chain.**  This is the skeleton's `BKLO.ExpansionChain` with the two
corrections forced by `BKLO.Refutations`: the vertex type is `ℕ` (so that the F-expansion
construction can use fresh vertices — over a fixed finite vertex type the statement is false), and
`H` is assumed loopless (a `Sym2` diagonal edge can never be covered by a triangle). -/
def ExpansionChainNat : Prop :=
  ∀ (H : Finset (Sym2 ℕ)), (∀ e ∈ H, ¬ e.IsDiag) → TriDivisible H →
    ∃ A' K : Finset (Sym2 ℕ), IsTransformer A' H K ∧ TriDecomp K ∧ Disjoint H K

theorem expansionChainNat : ExpansionChainNat := by
  intro H hloop hdiv
  obtain ⟨A, hd, hA, hAH⟩ := absorber_of_triDivisible hloop hdiv
  exact ⟨A, ∅, ⟨hd, by simp, hAH, by simpa using hA⟩, triDecomp_empty, by simp⟩

end BKLO
