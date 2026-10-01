import PaperIV.SplitUniformIncidence

/-!
# Disjointness of the three selected split-item families

The canonical fractional-packing adapter assigns one uniform mass to each of
the three families.  These lemmas guarantee that no clique receives two such
masses.
-/

namespace PaperIV.SplitFamilyDisjoint

open Finset
open PaperIV.SplitUniformIncidence

variable {V : Type*} [DecidableEq V]

theorem disjoint_famK3_famK4 {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    Disjoint (famK3 Core Hosts) (famK4 Core Hosts) := by
  rw [Finset.disjoint_left]
  intro t ht3 ht4
  have h3 := (famK3_isClique hd ht3).2
  have h4 := (famK4_isClique hd ht4).2
  omega

theorem disjoint_famK3_famK4core {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    Disjoint (famK3 Core Hosts) (famK4core Core) := by
  rw [Finset.disjoint_left]
  intro t ht3 ht4
  have h3 := (famK3_isClique hd ht3).2
  have h4 := (famK4core_isClique (Hosts := Hosts) ht4).2
  omega

theorem disjoint_famK4_famK4core {Core Hosts : Finset V} (hd : Disjoint Core Hosts) :
    Disjoint (famK4 Core Hosts) (famK4core Core) := by
  rw [Finset.disjoint_left]
  intro t ht4 htcore
  obtain ⟨s, hs, z, hz, hzt⟩ := mem_hostFam.mp ht4
  subst t
  rw [famK4core, Finset.mem_powersetCard] at htcore
  exact (Finset.disjoint_left.mp hd (htcore.1 (Finset.mem_insert_self z s))) hz

end PaperIV.SplitFamilyDisjoint
