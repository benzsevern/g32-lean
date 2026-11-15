import HodgeLean.Foundations.Program.G32SelectedRealizationModelSum
import HodgeLean.Foundations.Program.G32SelectedRealizationCentre

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem g32y_retained_groupRing_action {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a) :
    homPullback (∏ a, (f a).hom ^ b4b_projectorCoeff a) 1 = g32x_projector D t := by
  classical
  rw [g32y_homPullback_prod]
  simp only [hf, g32x_deck]
  change (∑ a, (b4b_projectorCoeff a : ℚ) • g32x_operator D t
    (b4_latticeAct ℂ a⁻¹)) = g32x_operator D t (b4_groupEnd ℂ b4b_projectorCoeff)
  rw [b4_groupEnd, g32x_operator, g32y_modelOperator_sum]
  change (∑ a, (b4b_projectorCoeff a : ℚ) • g32x_operator D t
    (b4_latticeAct ℂ a⁻¹)) = ∑ a, (b4b_projectorCoeff a : ℚ) • g32x_operator D t
      (b4_latticeAct ℂ a)
  conv_lhs => rw [← Equiv.sum_comp (Equiv.inv g32p_G)]
  simp only [Equiv.inv_apply, inv_inv, b63l_projectorCoeff_inverse]

end HodgeLean.Foundations.Program
