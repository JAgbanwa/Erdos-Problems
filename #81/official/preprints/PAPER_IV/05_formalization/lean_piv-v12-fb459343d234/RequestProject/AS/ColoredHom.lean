module

public import RequestProject.AS.Defs

/-!
# Colored homomorphisms and the function `Ψ_𝓕` (Definitions 4.3, 4.5, 4.6 of Alon–Shapira)

A *colored complete graph* on `k` vertices is a vertex colouring (`true` = black, `false` = white)
together with an edge colouring by `Fin 3` (`0` = white, `1` = black, `2` = grey).

A *colored homomorphism* `F ↦c R` is a map `φ : V(F) → V(R)` such that for distinct `u, v`:
* if `φ u = φ v = t` then `uv ∈ E(F)` iff `t` is black;
* if `φ u ≠ φ v` then edges of `F` are not mapped to white edges, and non-edges of `F` are not
  mapped to black edges.

`Ψ_𝓕(k)` is the maximum, over all colored complete graphs `R` on `k` vertices for which some
member of `𝓕` has a colored homomorphism into `R`, of the size of the smallest such member.
-/

@[expose] public section

open Finset

open scoped Classical

namespace AlonShapira

/-- A colored complete graph on `Fin k`: vertex colours (`true` = black) and edge colours
(`0` = white, `1` = black, `2` = grey). -/
abbrev CGraph (k : ℕ) := (Fin k → Bool) × (Fin k → Fin k → Fin 3)

/-- **Definition 4.3 (colored homomorphism).** -/
def IsCHom {f k : ℕ} (F : SimpleGraph (Fin f)) (R : CGraph k) (φ : Fin f → Fin k) : Prop :=
  ∀ a b, a ≠ b →
    (φ a = φ b → (F.Adj a b ↔ R.1 (φ a) = true)) ∧
    (φ a ≠ φ b → (F.Adj a b → R.2 (φ a) (φ b) ≠ 0) ∧ (¬ F.Adj a b → R.2 (φ a) (φ b) ≠ 1))

/-- Some member of `𝓕` of size `f` has a colored homomorphism into `R`. -/
def HasCHom (𝓕 : GraphFamily) {k : ℕ} (R : CGraph k) (f : ℕ) : Prop :=
  ∃ F ∈ 𝓕 f, ∃ φ : Fin f → Fin k, IsCHom F R φ

/-- The size of the smallest member of `𝓕` with a colored homomorphism into `R` (`0` if none). -/
noncomputable def minCHomSize (𝓕 : GraphFamily) {k : ℕ} (R : CGraph k) : ℕ :=
  if h : ∃ f, HasCHom 𝓕 R f then Nat.find h else 0

/-- **Definition 4.6 (the function `Ψ_𝓕`).** -/
noncomputable def Psi (𝓕 : GraphFamily) (k : ℕ) : ℕ :=
  (univ : Finset (CGraph k)).sup fun R => minCHomSize 𝓕 R

/-- If some member of `𝓕` has a colored homomorphism into `R` (on `k` vertices), then so does a
member of size at most `Ψ_𝓕(k)`. -/
theorem exists_small_chom (𝓕 : GraphFamily) {k : ℕ} (R : CGraph k) (h : ∃ f, HasCHom 𝓕 R f) :
    ∃ f ≤ Psi 𝓕 k, HasCHom 𝓕 R f := by
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  have : minCHomSize 𝓕 R = Nat.find h := by simp [minCHomSize, h]
  rw [← this]
  exact Finset.le_sup (f := fun R => minCHomSize 𝓕 R) (mem_univ R)

end AlonShapira
