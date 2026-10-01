import PaperIV.MarkedQuotaTypedGain
import PaperIV.TrianglePairingSums
import PaperIV.TrianglePairingSplit

/-!
# RC01: triangle pairing fed to the proved marked-quota gate

This module replaces the historical `PartitionQuotaNibbleAt` residue.  Two
resource-disjoint triangle supports are coupled into one real `6`-set, and the
proved additive marked-quota gate is applied with the genuine `K4` supports as
the marked family.  No coloured nibble is assumed.
-/

namespace PaperIV.MarkedQuotaPairing

open Finset
open PaperIV.TrianglePairingDefs
open PaperIV.TrianglePairingSums

variable {W : Type*} [DecidableEq W]

theorem bigWeight_nonneg {H₃ H₄ : Finset (Finset W)} {w : Finset W → ℝ} {t : ℝ}
    (hw : ∀ T, 0 ≤ w T) (ht : 0 ≤ t) (T : Finset W) :
    0 ≤ bigWeight H₃ H₄ w t T := by
  rw [bigWeight]
  split
  · exact hw T
  · exact pairWeight_nonneg hw ht T

theorem sum_bigWeight_filter {H₃ H₄ : Finset (Finset W)} (w : Finset W → ℝ) (t : ℝ)
    (hdisj : Disjoint H₄ (pairFam H₃)) (p : Finset W → Prop) [DecidablePred p] :
    ∑ T ∈ (bigFam H₃ H₄).filter p, bigWeight H₃ H₄ w t T
      = (∑ T ∈ H₄.filter p, w T) + ∑ P ∈ (pairFam H₃).filter p, pairWeight H₃ w t P := by
  classical
  have hsplit : (bigFam H₃ H₄).filter p = H₄.filter p ∪ (pairFam H₃).filter p := by
    rw [bigFam, Finset.filter_union]
  have hd : Disjoint (H₄.filter p) ((pairFam H₃).filter p) :=
    Finset.disjoint_filter_filter hdisj
  rw [hsplit, Finset.sum_union hd]
  congr 1
  · refine Finset.sum_congr rfl fun T hT => ?_
    rw [bigWeight, if_pos (Finset.mem_filter.1 hT).1]
  · refine Finset.sum_congr rfl fun P hP => ?_
    have hPn : P ∉ H₄ := fun h =>
      (Finset.disjoint_left.1 hdisj) h (Finset.mem_filter.1 hP).1
    rw [bigWeight, if_neg hPn]

theorem sum_bigWeight_sdiff {H₃ H₄ : Finset (Finset W)} (w : Finset W → ℝ) (t : ℝ)
    (hdisj : Disjoint H₄ (pairFam H₃)) :
    ∑ T ∈ bigFam H₃ H₄ \ H₄, bigWeight H₃ H₄ w t T
      = ∑ P ∈ pairFam H₃, pairWeight H₃ w t P := by
  classical
  have hset : bigFam H₃ H₄ \ H₄ = pairFam H₃ := by
    ext P
    simp only [bigFam, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hn⟩
      · exact absurd h hn
      · exact h
    · intro h
      exact ⟨Or.inr h, fun hc => (Finset.disjoint_left.1 hdisj) hc h⟩
  rw [hset]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hPn : P ∉ H₄ := fun hc => (Finset.disjoint_left.1 hdisj) hc hP
  rw [bigWeight, if_neg hPn]

theorem sum_bigWeight_four {H₃ H₄ : Finset (Finset W)} (w : Finset W → ℝ) (t : ℝ) :
    ∑ T ∈ H₄, bigWeight H₃ H₄ w t T = ∑ T ∈ H₄, w T := by
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [bigWeight, if_pos hT]

set_option maxHeartbeats 4000000 in
/-- The complete probabilistic pairing step.  Its conclusion is already the
typed objective needed after unfolding: an unmarked selected 6-set represents
two triangles and is therefore worth `4`; a marked selected 6-set is a `K4`
and is worth `5`. -/
theorem paired_typed_gain (β ε : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H₃ H₄ : Finset (Finset W)) (w : Finset W → ℝ) (Exc : Finset W),
        NibblePort.Hypergraph.IsUniform H₃ 3 →
        NibblePort.Hypergraph.IsUniform H₄ 6 →
        Disjoint H₄ (pairFam H₃) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, (∑ T ∈ H₃.filter (fun T => v ∈ T), w T)
            + (∑ T ∈ H₄.filter (fun T => v ∈ T), w T) ≤ 1) →
        (∀ v : W, v ∉ Exc → 1 - γ ≤ (∑ T ∈ H₃.filter (fun T => v ∈ T), w T)
            + (∑ T ∈ H₄.filter (fun T => v ∈ T), w T)) →
        (Exc.card : ℝ) ≤ η * (Fintype.card W : ℝ) →
        (∀ x z : W, x ≠ z → (∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T)
            + (∑ T ∈ H₄.filter (fun T => x ∈ T ∧ z ∈ T), w T) ≤ γ) →
        C ≤ ∑ T ∈ H₃, w T →
        ∃ M : Finset (Finset W),
          NibblePort.Hypergraph.IsMatching (bigFam H₃ H₄) M ∧
          (1 - β) * (2 * (∑ T ∈ H₃, w T) + 5 * (∑ T ∈ H₄, w T) - 6)
              - 5 * (ε * (Fintype.card W : ℝ))
            ≤ 4 * ((M.filter (fun T => T ∉ H₄)).card : ℝ)
              + 5 * ((M.filter (fun T => T ∈ H₄)).card : ℝ) := by
  classical
  obtain ⟨γ₀, hγ₀, η₀, hη₀, hmain⟩ :=
    MarkedQuotaTypedGain.typed_gain_additive β ε hβ hβ1 hε
  refine ⟨γ₀ / 2, by linarith, η₀, hη₀, 6 / γ₀, by positivity, ?_⟩
  intro W _ _ H₃ H₄ w Exc h3 h4 hdisj hw hload hlow hExc hcod hmass
  set t : ℝ := ∑ T ∈ H₃, w T with ht_def
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) hmass
  have hthr : 3 / t ≤ γ₀ / 2 := by
    rw [div_le_div_iff₀ htpos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ hγ₀] at hmass
    linarith
  have honet : 1 / t ≤ γ₀ / 2 := by
    have h1 : 1 / t ≤ 3 / t := by
      apply div_le_div_of_nonneg_right _ htpos.le
      norm_num
    linarith
  have hload3 : ∀ v : W, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T ≤ 1 := by
    intro v
    have h4nn : (0 : ℝ) ≤ ∑ T ∈ H₄.filter (fun T => v ∈ T), w T :=
      Finset.sum_nonneg fun T _ => hw T
    linarith [hload v]
  have hbigload : ∀ v : W,
      ∑ T ∈ (bigFam H₃ H₄).filter (fun T => v ∈ T), bigWeight H₃ H₄ w t T ≤ 1 := by
    intro v
    rw [sum_bigWeight_filter w t hdisj (fun T => v ∈ T)]
    have hp := pairs_load_le (H₃ := H₃) (w := w) (t := t) hw htpos
      (le_of_eq ht_def.symm) v
    linarith [hload v]
  have hbiglow : ∀ v : W, v ∉ Exc →
      1 - γ₀ ≤ ∑ T ∈ (bigFam H₃ H₄).filter (fun T => v ∈ T), bigWeight H₃ H₄ w t T := by
    intro v hv
    rw [sum_bigWeight_filter w t hdisj (fun T => v ∈ T)]
    have hp := pairs_load_ge (H₃ := H₃) (w := w) (t := t) h3 hw htpos
      (le_of_eq ht_def) hload3 v
    linarith [hlow v hv]
  have hbigcod : ∀ x z : W, x ≠ z →
      ∑ T ∈ (bigFam H₃ H₄).filter (fun T => x ∈ T ∧ z ∈ T),
          bigWeight H₃ H₄ w t T ≤ γ₀ := by
    intro x z hxz
    rw [sum_bigWeight_filter w t hdisj (fun T => x ∈ T ∧ z ∈ T)]
    have hp := pairs_codeg_le (H₃ := H₃) (w := w) (t := t) hw htpos ht_def hload3 x z
    linarith [hcod x z hxz]
  have hpair : (t - 3) / 2 ≤
      ∑ T ∈ bigFam H₃ H₄ \ H₄, bigWeight H₃ H₄ w t T := by
    rw [sum_bigWeight_sdiff w t hdisj]
    exact pairs_mass_ge h3 hw htpos ht_def hload3
  obtain ⟨M, hM, hgain⟩ :=
    hmain (bigFam H₃ H₄) H₄ (bigWeight H₃ H₄ w t) Exc t
      Finset.subset_union_left (bigFam_uniform h3 h4)
      (bigWeight_nonneg hw htpos.le) hbigload hbiglow hExc hbigcod hpair
  refine ⟨M, hM, ?_⟩
  rw [sum_bigWeight_four w t] at hgain
  simpa [ht_def] using hgain

set_option maxHeartbeats 4000000 in
/-- **The probabilistic pairing step over the slack nibble.**

Identical bookkeeping to `paired_typed_gain`, but fed by
`PaperIV.MarkedQuotaTypedGain.typed_gain_slack`.  There is therefore **no
lower-load hypothesis and no exceptional set**; the remaining instance
hypotheses are the joint upper loads, the joint weighted codegrees and the
constant lower bound on the triangle mass.  The extra price is the additive
constant `5 * D`. -/
theorem paired_typed_gain_slack (β ε : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H₃ H₄ : Finset (Finset W)) (w : Finset W → ℝ),
        NibblePort.Hypergraph.IsUniform H₃ 3 →
        NibblePort.Hypergraph.IsUniform H₄ 6 →
        Disjoint H₄ (pairFam H₃) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, (∑ T ∈ H₃.filter (fun T => v ∈ T), w T)
            + (∑ T ∈ H₄.filter (fun T => v ∈ T), w T) ≤ 1) →
        (∀ x z : W, x ≠ z → (∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T)
            + (∑ T ∈ H₄.filter (fun T => x ∈ T ∧ z ∈ T), w T) ≤ γ) →
        C ≤ ∑ T ∈ H₃, w T →
        ∃ M : Finset (Finset W),
          NibblePort.Hypergraph.IsMatching (bigFam H₃ H₄) M ∧
          (1 - β) * (2 * (∑ T ∈ H₃, w T) + 5 * (∑ T ∈ H₄, w T) - 6)
              - 5 * (ε * (Fintype.card W : ℝ)) - 5 * D
            ≤ 4 * ((M.filter (fun T => T ∉ H₄)).card : ℝ)
              + 5 * ((M.filter (fun T => T ∈ H₄)).card : ℝ) := by
  classical
  obtain ⟨γ₀, hγ₀, D, hD, hmain⟩ :=
    MarkedQuotaTypedGain.typed_gain_slack β ε hβ hβ1 hε
  refine ⟨γ₀ / 2, by linarith, 6 / γ₀, by positivity, D, hD, ?_⟩
  intro W _ _ H₃ H₄ w h3 h4 hdisj hw hload hcod hmass
  set t : ℝ := ∑ T ∈ H₃, w T with ht_def
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) hmass
  have hthr : 3 / t ≤ γ₀ / 2 := by
    rw [div_le_div_iff₀ htpos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ hγ₀] at hmass
    linarith
  have honet : 1 / t ≤ γ₀ / 2 := by
    have h1 : 1 / t ≤ 3 / t := by
      apply div_le_div_of_nonneg_right _ htpos.le
      norm_num
    linarith
  have hload3 : ∀ v : W, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T ≤ 1 := by
    intro v
    have h4nn : (0 : ℝ) ≤ ∑ T ∈ H₄.filter (fun T => v ∈ T), w T :=
      Finset.sum_nonneg fun T _ => hw T
    linarith [hload v]
  have hbigload : ∀ v : W,
      ∑ T ∈ (bigFam H₃ H₄).filter (fun T => v ∈ T), bigWeight H₃ H₄ w t T ≤ 1 := by
    intro v
    rw [sum_bigWeight_filter w t hdisj (fun T => v ∈ T)]
    have hp := pairs_load_le (H₃ := H₃) (w := w) (t := t) hw htpos
      (le_of_eq ht_def.symm) v
    linarith [hload v]
  have hbigcod : ∀ x z : W, x ≠ z →
      ∑ T ∈ (bigFam H₃ H₄).filter (fun T => x ∈ T ∧ z ∈ T),
          bigWeight H₃ H₄ w t T ≤ γ₀ := by
    intro x z hxz
    rw [sum_bigWeight_filter w t hdisj (fun T => x ∈ T ∧ z ∈ T)]
    have hp := pairs_codeg_le (H₃ := H₃) (w := w) (t := t) hw htpos ht_def hload3 x z
    linarith [hcod x z hxz]
  have hpair : (t - 3) / 2 ≤
      ∑ T ∈ bigFam H₃ H₄ \ H₄, bigWeight H₃ H₄ w t T := by
    rw [sum_bigWeight_sdiff w t hdisj]
    exact pairs_mass_ge h3 hw htpos ht_def hload3
  obtain ⟨M, hM, hgain⟩ :=
    hmain (bigFam H₃ H₄) H₄ (bigWeight H₃ H₄ w t) t
      Finset.subset_union_left (bigFam_uniform h3 h4)
      (bigWeight_nonneg hw htpos.le) hbigload hbigcod hpair
  refine ⟨M, hM, ?_⟩
  rw [sum_bigWeight_four w t] at hgain
  simpa [ht_def] using hgain

end PaperIV.MarkedQuotaPairing
