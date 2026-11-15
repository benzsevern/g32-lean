import HodgeLean.Foundations.Program.G32Native.EulerModel.ComponentComparison
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11Normalization

/-! # Exact normalized component classes under the multiplicative comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The multiplicative comparison retains the exact absolute class of the supplied normalized component coclass. -/
theorem normalized_component_cupComparison
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [IsIntegral W.left] [Smooth W.hom] [IsProjective W.hom]
    (ι : Q ⟶ W) (k : ℕ) (hcod : Order.coheight (ι.left (genericPoint Q.left)) = k)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c) :
    cupComparison W (2 * k) (cycleComponentSheafClass W (ι.left (genericPoint Q.left)) hcod) =
      s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c := by
  let (U : TopologicalSpace.Opens (ComplexPoint W)) : ParacompactSpace U := openParacompactSpace W U
  apply (spec_singularToFieldCohomology_bijective ℚ W (2 * k)).injective
  rw [bh11_cupComparison_eq_raw, singularToFieldCohomology_rationalCohomologyLinearEquivSingular]
  exact (normalized_component_class_comparison ι k hcod c hc).symm

#print axioms normalized_component_cupComparison
end HodgeLean.Foundations.Program.G32Native.EulerModel
