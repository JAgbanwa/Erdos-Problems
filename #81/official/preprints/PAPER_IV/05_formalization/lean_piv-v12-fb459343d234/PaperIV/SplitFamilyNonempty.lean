import PaperIV.SplitUniformIncidence

/-!
# Nonemptiness of split-item families in the nondegenerate regime
-/

namespace PaperIV.SplitFamilyNonempty

open PaperIV.SplitUniformIncidence

variable {V : Type*} [DecidableEq V]

theorem famK3_nonempty {Core Hosts : Finset V}
    (hk : 2 ≤ Core.card) (hh : 0 < Hosts.card) :
    (famK3 Core Hosts).Nonempty := by
  obtain ⟨s, hs⟩ := Finset.powersetCard_nonempty.2 hk
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hh
  exact ⟨insert z s, mem_hostFam.mpr ⟨s, hs, z, hz, rfl⟩⟩

theorem famK4_nonempty {Core Hosts : Finset V}
    (hk : 3 ≤ Core.card) (hh : 0 < Hosts.card) :
    (famK4 Core Hosts).Nonempty := by
  obtain ⟨s, hs⟩ := Finset.powersetCard_nonempty.2 hk
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hh
  exact ⟨insert z s, mem_hostFam.mpr ⟨s, hs, z, hz, rfl⟩⟩

theorem famK4core_nonempty {Core : Finset V} (hk : 4 ≤ Core.card) :
    (famK4core Core).Nonempty :=
  Finset.powersetCard_nonempty.2 hk

end PaperIV.SplitFamilyNonempty
