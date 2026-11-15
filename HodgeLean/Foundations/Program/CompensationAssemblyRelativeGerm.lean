import HodgeLean.Foundations.Program.CompensationAssemblyPrimeSurfaceTrace
import HodgeLean.Adapters.KleimanProduct

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cq_component_relative_germ_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ℕ) (hx : Order.coheight x = p) (a : ComplexPoint X)
    (haS : a ∈ cycleComponentAnalyticClosedSupport X x)
    (haB : a ∈ (ccm5_componentBoundary X 1 (fun _ => x)).compl) :
    Function.Injective (fun u => ccm5_supportGerm X
      (cycleComponentAnalyticClosedSupport X x) (2 * p) a
      ((ccm16_supportedComparison X (cycleComponentAnalyticClosedSupport X x)
        (2 * p)).symm u)) := by
  intro u v h
  apply (ccm16_supportedComparison X (cycleComponentAnalyticClosedSupport X x)
    (2 * p)).symm.injective
  exact hc9k_supportedClass_eq_of_generic_germs X (Fin 1) p (fun _ => x)
    (fun _ => hx) (cycleComponentAnalyticClosedSupport X x) (by simp only [iSup_const])
    (2 * p) rfl (fun _ => a) (fun _ => haS)
    (fun _ => by
      change a ∈ (ccm5_componentBoundary X (Fintype.card (Fin 1)) (fun _ => x)).compl
      rw [Fintype.card_fin]
      exact haB)
    _ _ (fun _ => h)

end HodgeLean.Foundations.Program
