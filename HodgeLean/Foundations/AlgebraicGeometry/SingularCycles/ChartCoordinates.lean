import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Defs

/-! # Complex linear coordinates on product charts

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

/-- Concatenating tangent and normal coordinates is a complex continuous linear equivalence.
Source: Mathlib, Fin.append and finite-dimensional continuous linear equivalences. -/
def chartProductEquiv (r k : ℕ) :
    ((Fin r → ℂ) × (Fin k → ℂ)) ≃L[ℂ] (Fin (r + k) → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun p => Fin.append p.1 p.2
    invFun := fun v => (fun i => v (Fin.castAdd k i), fun j => v (Fin.natAdd r j))
    left_inv := by
      intro p
      apply Prod.ext <;> funext i <;> simp
    right_inv := by
      intro v
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    map_add' := by
      intro p q
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    map_smul' := by
      intro a p
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp }

/-- The concatenated coordinate map retains its tangent coordinates.
Source: Mathlib, Fin.append_left. -/
theorem chartProductEquiv_castAdd (r k : ℕ) (p : (Fin r → ℂ) × (Fin k → ℂ)) (i : Fin r) :
    chartProductEquiv r k p (Fin.castAdd k i) = p.1 i := by
  exact Fin.append_left _ _ i

end AlgebraicGeometry.SingularCycles
