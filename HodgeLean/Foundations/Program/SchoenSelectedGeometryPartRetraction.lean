import HodgeLean.Foundations.Program.SchoenSelectedGeometrySupplierCurve
import HodgeLean.Foundations.Program.G32SelectedRealizationSecond
import HodgeLean.Foundations.Program.G32SelectedProp46
import HodgeLean.Foundations.Program.RiemannSurfaceQuotient
import HodgeLean.Adapters.CycleClassPullbackDefs
import HodgeLean.Foundations.Program.UniversalFamilyB60cIsogeny
import HodgeLean.Foundations.Program.CycleFoundationsPullback

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem s0_part_retract
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S) :
    homPullback P.incl 1 ∘ₗ homPullback P.proj 1 = (P.N : ℚ) • LinearMap.id := by
  rw [← spec_homPullback_comp, P.retract, ← zpow_natCast,
    spec_homPullback_zpow, spec_homPullback_id, Int.cast_natCast]

theorem s0_part_proj_injective
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S) :
    Function.Injective (homPullback P.proj 1) := by
  intro x y h
  have hh := congrArg (homPullback P.incl 1) h
  have hr := s0_part_retract J aut S P
  have hx := LinearMap.congr_fun hr x
  have hy := LinearMap.congr_fun hr y
  change homPullback P.incl 1 (homPullback P.proj 1 x) = (P.N : ℚ) • x at hx
  change homPullback P.incl 1 (homPullback P.proj 1 y) = (P.N : ℚ) • y at hy
  rw [hx, hy] at hh
  exact smul_right_injective _ (show (P.N : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr P.N_pos.ne') hh

#print axioms s0_part_retract
#print axioms s0_part_proj_injective
end HodgeLean.Foundations.Program
