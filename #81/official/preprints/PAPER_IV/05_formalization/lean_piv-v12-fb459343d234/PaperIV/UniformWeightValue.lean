import PaperIV.SplitUniformIncidence

/-!
# Objective value of the uniform split weighting

Independently of capacity, the uniformly distributed masses have exactly the
expected mixed-packing gain.  The adapter to `FarRounding.FracPacking` will use
this identity after it establishes that the three literal families are included
in the canonical item family.
-/

namespace PaperIV.UniformWeightValue

open Finset
open PaperIV.SplitUniformIncidence

variable {V : Type*} [DecidableEq V]

theorem uniformWeight_nonneg {F : Finset (Finset V)} (hF : F.Nonempty)
    {m : ℚ} (hm : 0 ≤ m) : 0 ≤ uniformWeight F m := by
  unfold uniformWeight
  have hcard : (0 : ℚ) < F.card := by
    exact_mod_cast (Finset.card_pos.mpr hF)
  positivity

theorem uniformWeight_empty (m : ℚ) : uniformWeight (∅ : Finset (Finset V)) m = 0 := by
  simp [uniformWeight]

theorem empty_family_weight_sum (m : ℚ) :
    ∑ _K ∈ (∅ : Finset (Finset V)), uniformWeight (∅ : Finset (Finset V)) m = 0 := by
  simp

theorem split_uniform_gain_value
    (Core Hosts : Finset V) (u v w : ℚ)
    (h3 : (famK3 Core Hosts).Nonempty)
    (h4 : (famK4 Core Hosts).Nonempty)
    (h4c : (famK4core Core).Nonempty) :
    (∑ K ∈ famK3 Core Hosts, 2 * uniformWeight (famK3 Core Hosts) u) +
      (∑ K ∈ famK4 Core Hosts, 5 * uniformWeight (famK4 Core Hosts) v) +
      (∑ K ∈ famK4core Core, 5 * uniformWeight (famK4core Core) w) =
      2 * u + 5 * v + 5 * w := by
  have hu : ∑ _K ∈ famK3 Core Hosts, uniformWeight (famK3 Core Hosts) u = u :=
    sum_uniformWeight h3 u
  have hv : ∑ _K ∈ famK4 Core Hosts, uniformWeight (famK4 Core Hosts) v = v :=
    sum_uniformWeight h4 v
  have hw : ∑ _K ∈ famK4core Core, uniformWeight (famK4core Core) w = w :=
    sum_uniformWeight h4c w
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hu, hv, hw] <;> ring

end PaperIV.UniformWeightValue
