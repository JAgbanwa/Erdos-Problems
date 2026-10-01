import E32.Consequences
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A square-root obstruction for distance to the optimal defect family

For n+s=3q and 1≤d≤q/2, shift the combined core from q to q+d.
The exact unrestricted partition deficit is d²+choose(d,2), whereas every
optimal template differs in at least nd/4 edges, provided 2s+2≤q.
The lower bound uses edge counts, hence allows arbitrary relabellings.
No optimality of the stability constants is claimed.
-/
namespace PaperIV.OptimalTemplateObstruction
open Finset PaperIV.FarRounding PaperIV.DefectComparatorGraph
  PaperIV.DefectTargetArithmetic PaperIV.RootedSimplicialDefect
open scoped symmDiff

def displacementDeficit (d : ℕ) : ℕ := d*d + d.choose 2

theorem two_mul_displacementDeficit (d : ℕ) :
    2*displacementDeficit d+d=3*d*d := by
  have hc := E32.two_mul_choose_two_int d
  have he : (2*displacementDeficit d+d : ℕ) = 3*d*d := by
    zify
    unfold displacementDeficit
    push_cast
    nlinarith
  exact he

theorem deficit_bounds (d : ℕ) :
    d*d ≤ displacementDeficit d ∧ displacementDeficit d ≤ 2*d*d := by
  have hc : d.choose 2 ≤ d*d := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  unfold displacementDeficit
  constructor
  · omega
  · nlinarith

private theorem partition_card {n : ℕ} {C D H : Finset (Fin n)}
    (hCD : Disjoint C D) (hCH : Disjoint C H) (hDH : Disjoint D H)
    (cover : ∀ x, x ∈ C ∨ x ∈ D ∨ x ∈ H) :
    C.card+D.card+H.card=n := by
  have hu : C ∪ D ∪ H = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    have hx := cover x
    tauto
  have hc := congrArg card hu
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hCH,hDH⟩),
    card_union_of_disjoint hCD, card_univ, Fintype.card_fin] at hc
  exact hc

private theorem edge_card_le_add_edit {V : Type*} [DecidableEq V]
    (A B : Finset V) :
    A.card ≤ B.card + PaperIV.EditMetric.editDist A B := by
  have h : A.card ≤ (A \ B).card+B.card := Finset.card_le_card_sdiff_add_card
  have hs : A \ B ⊆ A ∆ B := by
    intro x hx
    exact mem_symmDiff.mpr (Or.inl (mem_sdiff.mp hx))
  have hc := card_le_card hs
  unfold PaperIV.EditMetric.editDist
  omega

private theorem shifted_arithmetic
    (n s q d c h c0 h0 : ℕ) (hn : n+s=3*q)
    (hq : 2*s+2 ≤ q) (hd : 2*d ≤ q)
    (hc : c+s=q+d) (hh : c+s+h=n)
    (hc0 : c0+s=q) (hh0 : c0+s+h0=n) :
    ((c+s)*h-c.choose 2)+displacementDeficit d =
      (c0+s)*h0-c0.choose 2 ∧
    4*(c0.choose 2+(c0+s)*h0)+n*d ≤
      4*(c.choose 2+(c+s)*h) := by
  have hch : c ≤ h := by omega
  have hch0 : c0 ≤ h0 := by omega
  have hb := (E32.choose_two_le_mul hch).trans
    (Nat.mul_le_mul_right h (show c ≤ c+s by omega))
  have hb0 := (E32.choose_two_le_mul hch0).trans
    (Nat.mul_le_mul_right h0 (show c0 ≤ c0+s by omega))
  have cn := E32.two_mul_choose_two_int c
  have cn0 := E32.two_mul_choose_two_int c0
  have dn := E32.two_mul_choose_two_int d
  have zn : (n : ℤ)+s=3*q := by exact_mod_cast hn
  have zq : 2*(s : ℤ)+2 ≤ q := by exact_mod_cast hq
  have zd : 2*(d : ℤ) ≤ q := by exact_mod_cast hd
  have zc : (c : ℤ)+s=q+d := by exact_mod_cast hc
  have zh : (c : ℤ)+s+h=n := by exact_mod_cast hh
  have zc0 : (c0 : ℤ)+s=q := by exact_mod_cast hc0
  have zh0 : (c0 : ℤ)+s+h0=n := by exact_mod_cast hh0
  have zce : (c : ℤ) = q+d-s := by omega
  have zhe : (h : ℤ) = 2*q-s-d := by omega
  have zc0e : (c0 : ℤ) = q-s := by omega
  have zh0e : (h0 : ℤ) = 2*q-s := by omega
  have zne : (n : ℤ) = 3*q-s := by omega
  rw [zce] at cn
  rw [zc0e] at cn0
  constructor
  · have he : ((((c+s)*h-c.choose 2)+displacementDeficit d : ℕ) : ℤ) =
        (((c0+s)*h0-c0.choose 2 : ℕ) : ℤ) := by
      unfold displacementDeficit
      push_cast [Nat.cast_sub hb, Nat.cast_sub hb0]
      rw [zce,zhe,zc0e,zh0e]
      nlinarith only [cn,cn0,dn]
    exact_mod_cast he
  · have he : (4*(c0.choose 2+(c0+s)*h0)+n*d : ℤ) ≤
        4*(c.choose 2+(c+s)*h) := by
      have hz : 0 ≤ (d : ℤ)*(5*(q : ℤ)-7*s-2*d-2) :=
        mul_nonneg (Int.natCast_nonneg d) (by omega)
      rw [zce,zhe,zc0e,zh0e,zne]
      nlinarith only [cn,cn0,hz]
    exact_mod_cast he

private def initial (n a : ℕ) : Finset (Fin n) :=
  univ.filter fun x => x.val < a

private theorem card_initial (n a : ℕ) (ha : a ≤ n) :
    (initial n a).card = a := by
  have himg : (initial n a).image Fin.val = range a := by
    ext m
    simp only [initial, mem_image, mem_filter, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨x,hx,rfl⟩; exact hx
    · intro hm; exact ⟨⟨m,by omega⟩,hm,rfl⟩
  calc
    (initial n a).card = ((initial n a).image Fin.val).card :=
      (card_image_of_injective _ Fin.val_injective).symm
    _ = a := by rw [himg, card_range]

/-- The comparison family is nonempty in the entire range of the witnesses. -/
theorem optimal_family_nonempty (n s q : ℕ)
    (hn : n+s=3*q) (hq : 2*s+2 ≤ q) :
    ∃ T : SimpleGraph (Fin n), E32.IsAdmissibleExtremal T s := by
  classical
  let C := initial n (q-s)
  let U := initial n q
  let D := U \ C
  let H := Uᶜ
  have hCU : C ⊆ U := by
    intro x hx
    simp only [C,U,initial,mem_filter,mem_univ,true_and] at *
    omega
  have hC : C.card=q-s := card_initial n _ (by omega)
  have hU : U.card=q := card_initial n _ (by omega)
  have hD : D.card=s := by rw [card_sdiff_of_subset hCU,hU,hC]; omega
  refine ⟨defSplitGraph C D H,C,D,H,disjoint_sdiff_self_right,
    disjoint_compl_right.mono_left hCU,
    disjoint_compl_right.mono_left sdiff_subset,?_,hD,rfl,?_⟩
  · intro x
    simp only [D,H,mem_sdiff,mem_compl]
    tauto
  · unfold E32.NearestCore
    rw [Fintype.card_fin,hC,abs_le]
    omega

/-- Exact witnesses for every fixed defect. Both the partition lower bound and
the comparison family allow unrestricted pieces and arbitrary vertex labels. -/
theorem shifted_template_witness (n s q d : ℕ)
    (hn : n+s=3*q) (hq : 2*s+2 ≤ q)
    (hd1 : 1 ≤ d) (hd : 2*d ≤ q) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      RootedDefectAt G s ∧
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        Q.size + displacementDeficit d = defectTarget s n ∧
        (∀ R : CliquePartition G, Q.size ≤ R.size) ∧
        ∀ (T : SimpleGraph (Fin n)) [DecidableRel T.Adj],
          E32.IsAdmissibleExtremal T s →
          n*d ≤ 4*PaperIV.EditMetric.editDist G.edgeFinset T.edgeFinset := by
  classical
  let C := initial n (q+d-s)
  let U := initial n (q+d)
  let D := U \ C
  let H := Uᶜ
  have hCU : C ⊆ U := by
    intro x hx
    simp only [C,U,initial,mem_filter,mem_univ,true_and] at *
    omega
  have hC : C.card=q+d-s := card_initial n _ (by omega)
  have hU : U.card=q+d := card_initial n _ (by omega)
  have hD : D.card=s := by rw [card_sdiff_of_subset hCU,hU,hC]; omega
  have hH : H.card=n-(q+d) := by simp [H,card_compl,hU]
  have hCD : Disjoint C D := disjoint_sdiff_self_right
  have hCH : Disjoint C H := disjoint_compl_right.mono_left hCU
  have hDH : Disjoint D H := disjoint_compl_right.mono_left sdiff_subset
  have hcover : ∀ x : Fin n, x ∈ C ∨ x ∈ D ∨ x ∈ H := by
    intro x
    simp only [D,H,mem_sdiff,mem_compl]
    tauto
  have hc : C.card+s=q+d := by omega
  have hh : C.card+s+H.card=n := by omega
  have hCle : C.card ≤ H.card := by omega
  let G := defSplitGraph C D H
  have hG : RootedDefectAt G s :=
    PaperIV.DefectComparatorRootedDefect.rootedDefectAt_defSplitGraph
      hCD hDH hCH hcover (by omega)
  obtain ⟨Q,hQ4,hQ⟩ := E32.exists_extremal_partition hCH (by omega) hCle
  have hl : ∀ R : CliquePartition G, E32.rootBaseline C D H ≤ R.size := by
    intro R
    exact PaperIV.DefectComparatorLower.cliquePartition_size_ge_defect_baseline
      hCD hDH (disjoint_union_left.mpr ⟨hCH,hDH⟩) R
  have hQeq : Q.size=E32.rootBaseline C D H := le_antisymm hQ (hl Q)
  have hbase : q*(n-q)-(q-s).choose 2=defectTarget s n := by
    have hb := PaperIV.DefectSharpPublication.comparator_baseline_eq_target n s (by omega)
    have he : (n+s+1)/3=q := by omega
    simpa only [he] using hb
  have ha := shifted_arithmetic n s q d C.card H.card (q-s) (n-q)
    hn hq hd hc hh (by omega) (by omega)
  refine ⟨G,inferInstance,hG,Q,hQ4,?_,?_,?_⟩
  · rw [hQeq,E32.rootBaseline,hD]
    simpa [Nat.sub_add_cancel (show s ≤ q by omega),hbase] using ha.1
  · intro R; rw [hQeq]; exact hl R
  · intro T instT hT
    obtain ⟨C',D',H',hCD',hCH',hDH',hcov',hD',hTeq,hnear⟩ := hT
    have hsum := partition_card hCD' hCH' hDH' hcov'
    have hopt : C'.card+s=q := by
      unfold E32.NearestCore at hnear
      rw [Fintype.card_fin,abs_le] at hnear
      omega
    have hc' : C'.card=q-s := by omega
    have hh' : H'.card=n-q := by omega
    have eG : G.edgeFinset.card=C.card.choose 2+(C.card+s)*H.card := by
      simpa only [PaperIV.Model.graphEdges,hD] using
        card_graphEdges_defSplitGraph hCD (disjoint_union_left.mpr ⟨hCH,hDH⟩)
    have eT : T.edgeFinset.card=(q-s).choose 2+q*(n-q) := by
      subst T
      have hi : instT = defSplitGraphDecidableRel C' D' H' := Subsingleton.elim _ _
      cases hi
      simpa only [PaperIV.Model.graphEdges,hc',hD',hh',
        Nat.sub_add_cancel (show s ≤ q by omega)] using
        card_graphEdges_defSplitGraph hCD' (disjoint_union_left.mpr ⟨hCH',hDH'⟩)
    have he := edge_card_le_add_edit G.edgeFinset T.edgeFinset
    rw [eG,eT] at he
    have hb := ha.2
    rw [Nat.sub_add_cancel (show s ≤ q by omega)] at hb
    omega

/-- Explicit square-root lower bound, with the *exact* partition deficit. -/
theorem shifted_template_sqrt_witness (n s q d : ℕ)
    (hn : n+s=3*q) (hq : 2*s+2 ≤ q)
    (hd1 : 1 ≤ d) (hd : 2*d ≤ q) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      RootedDefectAt G s ∧
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        Q.size + displacementDeficit d = defectTarget s n ∧
        (∀ R : CliquePartition G, Q.size ≤ R.size) ∧
        ∀ (T : SimpleGraph (Fin n)) [DecidableRel T.Adj],
          E32.IsAdmissibleExtremal T s →
          (n : ℝ)*Real.sqrt (displacementDeficit d)/8 ≤
            (PaperIV.EditMetric.editDist G.edgeFinset T.edgeFinset : ℝ) := by
  obtain ⟨G,inst,hG,Q,hQ4,hQ,hl,hfar⟩ := shifted_template_witness n s q d hn hq hd1 hd
  letI := inst
  refine ⟨G,inst,hG,Q,hQ4,hQ,hl,?_⟩
  intro T _ hT
  have hbd := (deficit_bounds d).2
  have hb : (displacementDeficit d : ℝ) ≤ 2*(d : ℝ)^2 := by
    have hb' : (displacementDeficit d : ℝ) ≤ 2*(d : ℝ)*(d : ℝ) := by
      exact_mod_cast hbd
    nlinarith only [hb']
  have hs : Real.sqrt (displacementDeficit d) ≤ 2*(d : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (d : ℝ)]
  have hf : (n : ℝ)*d ≤ 4*(PaperIV.EditMetric.editDist G.edgeFinset T.edgeFinset : ℝ) := by
    exact_mod_cast hfar T hT
  have hm := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ n by positivity)
  linarith

/-- Even deficit one has unbounded edit distance to the entire optimal family,
at arbitrarily large orders, for every fixed rooted defect. -/
theorem no_linear_optimal_template_bound (s A N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      RootedDefectAt G s ∧
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        Q.size+1=defectTarget s n ∧
        (∀ R : CliquePartition G, Q.size ≤ R.size) ∧
        ∀ (T : SimpleGraph (Fin n)) [DecidableRel T.Adj],
          E32.IsAdmissibleExtremal T s →
            A < PaperIV.EditMetric.editDist G.edgeFinset T.edgeFinset := by
  let q := 2*s+2+4*A+N
  let n := 3*q-s
  obtain ⟨G,inst,hG,Q,hQ4,hQ,hl,hfar⟩ :=
    shifted_template_witness n s q 1 (by dsimp [n,q]; omega)
      (by dsimp [q]; omega) (by omega) (by dsimp [q]; omega)
  letI := inst
  refine ⟨n,by dsimp [n,q]; omega,G,inst,hG,Q,hQ4,?_,hl,?_⟩
  · simpa [displacementDeficit] using hQ
  · intro T _ hT
    have hf := hfar T hT
    dsimp [n,q] at hf
    omega

#print axioms shifted_template_witness
#print axioms shifted_template_sqrt_witness
#print axioms no_linear_optimal_template_bound
end PaperIV.OptimalTemplateObstruction
