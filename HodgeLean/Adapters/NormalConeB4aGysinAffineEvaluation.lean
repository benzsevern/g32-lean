import HodgeLean.Adapters.NormalConeB4aGysinSectionEvaluation
import HodgeLean.Adapters.NormalConeB4aGysinAffineStalk
import HodgeConjecture.Mathlib.AlgebraicGeometry.Over.Basic

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- Evaluation at a complex point as an algebra map on affine sections. -/
def a3b4a_gysin_affine_evaluation
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.Opens)
    (w : ComplexPoint (Over.mk q)) (hw : w.underlying ∈ U) :
    letI : Algebra ℂ Γ(X, U) := overSpecAlgebra (Over.mk q) U
    Γ(X, U) →ₐ[ℂ] ℂ := by
  letI : Algebra ℂ Γ(X, U) := overSpecAlgebra (Over.mk q) U
  refine {
    toRingHom := (Point.evaluationHom (X := Over.mk q) U ⟨w, hw⟩).hom
    commutes' := ?_ }
  intro c
  change Point.evaluationHom U ⟨w, hw⟩ (a3b4a_gysin_sectionConst q U c) = c
  rw [Point.evaluationHom_apply]
  exact a3b4a_gysin_evaluate_sectionConst q U w hw c

end HodgeLean.Adapters
