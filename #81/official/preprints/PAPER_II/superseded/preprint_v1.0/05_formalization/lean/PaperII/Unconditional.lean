import PaperII.L12
import PaperII.Dirac1
import PaperII.IsChordalCopy

/-!
# Paper II — Theorem 1.2, UNCONDITIONAL (Path 2, Fase 5)

Assemble the chordal interface from the standard definition `IsChordal` and state Theorem 1.2 with
`IsChordal` as its only chordality hypothesis — no `ChordalStructure` bundle, no `A2Transfer`.

* `chordalStructure_of_isChordal` — build the `ChordalStructure` bundle from `IsChordal`
  (A1 `chordal_induce` + A3a `dirac_simplicial` ⇒ `simplicial_hereditary`; A3b via `Dirac.rdirac2`).
* `a2Transfer` — discharge the `A2Transfer` hypothesis (`chordal_classCopy` + the `isChordal` field).
* `theorem_1_2` — the unconditional statement, proven by feeding the above to
  `theorem_1_2_of_chordalStructure` (the former conditional theorem).
-/

open scoped BigOperators

namespace PaperII

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Build the chordal bundle from the standard definition (Path 2). -/
def chordalStructure_of_isChordal {G : SimpleGraph V} (hG : IsChordal G) : ChordalStructure G where
  isChordal := hG
  simplicial_hereditary := by
    -- A1 (`isChordal_induce`) makes each nonempty induced subgraph chordal; A3a
    -- (`dirac_simplicial`) then gives it a simplicial vertex.
    classical
    intro W hW
    haveI : Fintype ↥W := (W.toFinite).fintype
    exact dirac_simplicial (G.induce W) (isChordal_induce G hG W) hW.to_subtype
  two_nonadj_simplicial := by
    -- A3b via the Dirac engine `rdirac2U` at `S = U = univ`: relative-simplicial existence on every
    -- nonempty subset (A1 `isChordal_induce` + A3a `dirac_simplicial`, bridged by
    -- `rsimplicial_of_induce_simplicial`), `univ` relatively connected (from `G.Connected`), and
    -- `univ` not a clique (from non-completeness). `isSimplicial_of_rsimplicial` returns to the
    -- absolute notion since all neighbours lie in `univ`.
    classical
    intro hConn hNotComplete
    have hRSH : ∀ T : Finset V, T ⊆ Finset.univ → T.Nonempty → ∃ a ∈ T, RSimplicial G T a := by
      intro T _ hTne
      obtain ⟨w0, hw0⟩ := hTne
      haveI : Nonempty ↥(T : Set V) := ⟨⟨w0, by simpa using hw0⟩⟩
      obtain ⟨z, hz⟩ := dirac_simplicial (G.induce (T : Set V)) (isChordal_induce G hG (T : Set V)) this
      exact ⟨z.val, by have := z.property; rwa [Finset.mem_coe] at this,
        rsimplicial_of_induce_simplicial G T z hz⟩
    have hRConn : RConn G Finset.univ := by
      intro a _ b _
      have hreach : G.Reachable a b := hConn.preconnected a b
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      exact hreach.mono (fun x y hxy => ⟨Finset.mem_univ x, Finset.mem_univ y, hxy⟩)
    have hNC : ¬ ∀ a ∈ Finset.univ, ∀ b ∈ Finset.univ, a ≠ b → G.Adj a b := by
      intro hc
      exact hNotComplete (fun u v huv => hc u (Finset.mem_univ u) v (Finset.mem_univ v) huv)
    obtain ⟨a, _, b, _, hab, hnadj, hsa, hsb⟩ :=
      rdirac2U G Finset.univ hRSH Finset.univ.card Finset.univ (Finset.Subset.refl _) rfl hRConn hNC
    exact ⟨a, b, hab, hnadj,
      isSimplicial_of_rsimplicial G (fun c _ => Finset.mem_univ c) hsa,
      isSimplicial_of_rsimplicial G (fun c _ => Finset.mem_univ c) hsb⟩

/-- Discharge `A2Transfer`: copying toward a clique-neighbourhood target preserves chordality, now
recovered from the standard definition via the `isChordal` field. -/
def a2Transfer : A2Transfer V :=
  fun H _ A B hCS hB => chordalStructure_of_isChordal (chordal_classCopy H A B hCS.isChordal hB)

/-- **Theorem 1.2 (UNCONDITIONAL).** Chordality hypothesis is the standard `IsChordal`; no
`ChordalStructure`, no `A2Transfer`. -/
theorem theorem_1_2 (n : ℕ) (hn : 1 ≤ n) :
    (∀ {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
        Fintype.card W = n → IsChordal G →
        phiTau G ≤ (((2 * (n : ℤ) + 1) ^ 2 / 24 : ℤ) : ℝ))
    ∧
    (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
        Fintype.card W = n ∧ IsChordal G ∧
        phiTau G = (((2 * (n : ℤ) + 1) ^ 2 / 24 : ℤ) : ℝ)) := by
  -- Discharge the conditional theorem's hypotheses: `A2Transfer` via `a2Transfer`, and each
  -- `ChordalStructure` via `chordalStructure_of_isChordal` (∀) / the bundle's `isChordal` field (∃).
  have hA2 : ∀ {W : Type} [Fintype W] [DecidableEq W], A2Transfer W := @a2Transfer
  obtain ⟨hUp, hEx⟩ := theorem_1_2_of_chordalStructure n hn hA2
  refine ⟨?_, ?_⟩
  · intro W _ _ G _ hcard hchord
    exact hUp G hcard (chordalStructure_of_isChordal hchord)
  · obtain ⟨W, fW, dW, G, dRW, hcard, ⟨hCS⟩, hval