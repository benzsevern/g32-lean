import HodgeLean.Foundations.Program.UniversalFamilyB60cRationalTransport

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Rational intertwining of quadratic actions persists after complex scalar extension. -/
theorem b60c_complex_action_intertwines (P Q : g32t_Sixfold)
    (e : HQ P.X 1 ≃ₗ[ℚ] HQ Q.X 1)
    (he : ∀ x, e (P.W.J x) = Q.W.J (e x)) (x : ℂ ⊗[ℚ] HQ P.X 1) :
    (LinearEquiv.baseChange ℚ ℂ _ _ e) ((P.W.J.baseChange ℂ) x) =
      (Q.W.J.baseChange ℂ) ((LinearEquiv.baseChange ℚ ℂ _ _ e) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x => simp only [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, he]

#print axioms b60c_complex_action_intertwines

end HodgeLean.Foundations.Program
