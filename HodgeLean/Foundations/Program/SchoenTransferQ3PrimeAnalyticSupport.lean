import HodgeLean.Foundations.Program.SchoenTransferQ3SupportPointLift
import HodgeLean.Adapters.CycleClassFlatPullbackDefs

/-! The exact original analytic range of the retained reduced prime component. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original reduced prime-component inclusion has exactly the analytic
support defined by its original scheme-theoretic prime closure. -/
theorem s4_q3_prime_component_complex_range
    (X : Over (Spec ↧ℂ)) (p : X.left) :
    let C : Over (Spec ↧ℂ) := Over.mk ((ccm3_primeIdeal X.left p).subschemeι ≫ X.hom)
    let i : C ⟶ X := Over.homMk (ccm3_primeIdeal X.left p).subschemeι rfl
    Set.range (Point.map i) = Point.underlying ⁻¹' closure ({p} : Set X.left) := by
  let C : Over (Spec ↧ℂ) := Over.mk ((ccm3_primeIdeal X.left p).subschemeι ≫ X.hom)
  let i : C ⟶ X := Over.homMk (ccm3_primeIdeal X.left p).subschemeι rfl
  letI : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion (ccm3_primeIdeal X.left p).subschemeι)
  change Set.range (Point.map i) = _
  rw [ComplexPoint.range_map_of_closedImmersion]
  ext y
  change (y.underlying ∈ Set.range (ccm3_primeIdeal X.left p).subschemeι) ↔ _
  rw [Scheme.IdealSheafData.range_subschemeι]
  change (y.underlying ∈ ((ccm3_primeIdeal X.left p).support : Set X.left)) ↔ _
  rw [ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

end HodgeLean.Foundations.Program
