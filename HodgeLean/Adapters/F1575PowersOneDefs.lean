import HodgeLean.Adapters.F1575PowersDescent

/-! # Definitions for the F-1575 all-powers spec (FROZEN)

This file is part of the frozen spec for `docs/briefs/f1575-powers-fix.md`. Do not edit it.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace HodgeLean.Adapters
open RealDefs

/-- The multiplicity-one flattening `H¹ ⊗ ℚ^1 → H¹`, `x ⊗ c ↦ c 0 • x`.
Source: Mathlib `TensorProduct.rid` and `LinearEquiv.funUnique`. -/
def powerOneFlatten (X : Over (Spec ↧ℂ)) : HQ X 1 ⊗[ℚ] (Fin 1 → ℚ) →ₗ[ℚ] HQ X 1 :=
  (TensorProduct.rid ℚ (HQ X 1)).toLinearMap ∘ₗ
    LinearMap.lTensor (HQ X 1) (LinearEquiv.funUnique (Fin 1) ℚ ℚ).toLinearMap

example (X : Over (Spec ↧ℂ)) (x : HQ X 1) (c : Fin 1 → ℚ) :
    powerOneFlatten X (x ⊗ₜ[ℚ] c) = c 0 • x := by
  simp [powerOneFlatten]

end HodgeLean.Adapters
