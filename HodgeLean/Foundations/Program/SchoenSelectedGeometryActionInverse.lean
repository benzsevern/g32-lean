import HodgeLean.Adapters.AbelianHomPullback

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Pullbacks of inverse elements of an algebraic action are inverse operators. -/
theorem s0_algebraic_action_inverse
    {H : Type*} [Group H]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (a : H → (X ⟶ X)) (ha : a 1 = 𝟙 X)
    (hm : ∀ u v, a (u * v) = a v ≫ a u) (u : H) (n : ℕ) :
    homPullback (a u) n * homPullback (a u⁻¹) n = 1 ∧
      homPullback (a u⁻¹) n * homPullback (a u) n = 1 := by
  constructor
  · rw [Module.End.mul_eq_comp, ← spec_homPullback_comp, ← hm,
      inv_mul_cancel, ha, spec_homPullback_id, Module.End.one_eq_id]
  · rw [Module.End.mul_eq_comp, ← spec_homPullback_comp, ← hm,
      mul_inv_cancel, ha, spec_homPullback_id, Module.End.one_eq_id]

#print axioms s0_algebraic_action_inverse
end HodgeLean.Foundations.Program
