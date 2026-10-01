import PaperIV
import PaperIV.Erdos81AllOrders
import PaperIV.PaperTheorems

/-! Public-release regression checks: literal, assumption-free exported types.
These tests do not change or replace any frozen mathematical source. -/
open PaperIV.FarRounding

example :
    ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n + b :=
  PaperIV.Erdos81AllOrders.erdos81_all_orders_additive

example :
    ∃ C : ℚ, 0 ≤ C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        PaperIV.FarRounding.IsChordal G →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
            (Q.size : ℚ) ≤ (n : ℚ)^2 / 6 + C * (n : ℚ) :=
  PaperIV.Erdos81AllOrders.erdos81_all_orders

example :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n :=
  PaperIV.Erdos81Unconditional.erdos81_cliquePartition

#print PaperIV.Erdos81AllOrders.erdos81_all_orders_additive
#print PaperIV.Erdos81AllOrders.erdos81_all_orders
#print PaperIV.Erdos81Unconditional.erdos81_cliquePartition
#print PaperIV.PaperTheorems.erdos81_max_eq
#print PaperIV.FarRounding.CliquePartition
#print PaperIV.FarRounding.CliquePartition.OrderAtMost
#print PaperIV.FarRounding.IsChordal
#print PaperIV.targetSize
#print axioms PaperIV.Erdos81AllOrders.erdos81_all_orders_additive
#print axioms PaperIV.Erdos81AllOrders.erdos81_all_orders
#print axioms PaperIV.Erdos81Unconditional.erdos81_cliquePartition
#print axioms PaperIV.PaperTheorems.erdos81_max_eq
