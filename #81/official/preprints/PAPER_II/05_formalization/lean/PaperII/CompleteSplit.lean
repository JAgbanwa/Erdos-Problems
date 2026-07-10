import PaperII.Model

/-!
# Paper II — Complete-split graph (ledger D4)

`completeSplit p q = S_{p,q} = K_p ∨ \overline{K_q}`: a clique side `Fin p`, an independent side
`Fin q`, and all `p*q` cross edges. Realized on `Fin p ⊕ Fin q` via `SimpleGraph.fromRel`.
-/

open scoped BigOperators

namespace PaperII

/-- Underlying relation of the complete-split graph (symmetrized by `fromRel`). -/
def csRel (p q : ℕ) : (Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → Prop := fun x y =>
  match x, y with
  | Sum.inl a, Sum.inl b => a ≠ b
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => False

instance (p q : ℕ) (x y) : Decidable (csRel p q x y) := by
  cases x <;> cases y <;> unfold csRel <;> infer_instance

/-- Ledger D4: the complete-split graph `S_{p,q}` on `Fin p ⊕ Fin q`. -/
def completeSplit (p q : ℕ) : SimpleGraph (Fin p ⊕ Fin q) := SimpleGraph.fromRel (csRel p q)

instance (p q : ℕ) : DecidableRel (completeSplit p q).Adj := fun x y =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj _ x y).symm

@[simp] theorem completeSplit_inl_inl (p q : ℕ) (a b : Fin p) :
    (completeSplit p q).Adj (Sum.inl a) (Sum.inl b) ↔ a ≠ b := by
  rw [completeSplit, SimpleGraph.fromRel_adj]
  refine ⟨fun h => ?_, fun h => ⟨by simpa using h, Or.inl h⟩⟩
  simpa using h.1

@[simp] theorem completeSplit_inl_inr (p q : ℕ) (a : Fin p) (b : Fin q) :
    (completeSplit p q).Adj (Sum.inl a) (Sum.inr b) := by
  rw [completeSplit, SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inl trivial⟩

@[simp] theorem completeSplit_inr_inl (p q : ℕ) (a : Fin q) (b : Fin p) :
    (completeSplit p q).Adj (Sum.inr a) (Sum.inl b) := by
  rw [completeSplit, SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inl trivial⟩

@[simp] theorem completeSplit_inr_inr (p q : ℕ) (a b : Fin q) :
    ¬ (completeSplit p q).Adj (Sum.inr a) (Sum.inr b) := by
  rw [completeSplit, SimpleGraph.fromRel_adj]
  