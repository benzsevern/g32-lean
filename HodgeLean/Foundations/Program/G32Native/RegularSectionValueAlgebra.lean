import HodgeLean.Foundations.Program.G32Native.ChosenChartPointDerivative

/-! # Original complex algebra maps from regular section evaluation -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Value at the original point is a map of the original complex section
algebras, using the original regular germ map. -/
def regularSectionValueAlgHom (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W)
    (U : W.left.Opens) (hp : p ∈ Point.overOpen U) :
    letI := overSpecAlgebra W U
    Γ(W.left, U) →ₐ[ℂ] ℂ := by
  letI := overSpecAlgebra W U
  refine {
    toRingHom := (s2e_nativeAnalyticGerm_value d).comp
      (s2e_regularSection_nativeAnalyticGerm W d p U hp)
    commutes' := ?_ }
  intro c
  change s2e_nativeAnalyticGerm_value d
    (s2e_regularSection_nativeAnalyticGerm W d p U hp (algebraMap ℂ Γ(W.left, U) c)) = c
  rw [regularGermMap_complexConstants]
  rfl

/-- The scalar-compatible point map retains evaluation of each original
regular section at the original point. -/
theorem regularSectionValueAlgHom_apply (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W)
    (U : W.left.Opens) (hp : p ∈ Point.overOpen U) (r : Γ(W.left, U)) :
    letI := overSpecAlgebra W U
    regularSectionValueAlgHom W d p U hp r = Point.evaluate U r p := by
  exact s2e_regularSection_nativeAnalyticGerm_value W d p U hp r

#print axioms regularSectionValueAlgHom_apply
#print axioms regularSectionValueAlgHom
end HodgeLean.Foundations.Program.G32Native
