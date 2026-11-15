import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Foundations.SegreProjective

/-! Scheme and group instances for every actual power, including the point at exponent zero. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- All five scope instances for an arbitrary exponent, without power-specific premises. -/
theorem g3_actual_power_instances (r : ℕ) :
    Nonempty (GrpObj (g3_power A r)) ∧ IsCommMonObj (g3_power A r) ∧
    IsIntegral (g3_power A r).left ∧ Smooth (g3_power A r).hom ∧
    IsProjective (g3_power A r).hom := by
  exact ⟨⟨inferInstance⟩, inferInstance, inferInstance, inferInstance, inferInstance⟩

#print axioms g3_actual_power_instances
#print axioms HodgeLean.Foundations.spec_g3b_isIntegral_power
#print axioms HodgeLean.Foundations.spec_g3c_isProjective_power

end HodgeLean.Adapters
