import HodgeLean.Foundations.Program.G32Native.EulerModel.IntersectionCycle
import HodgeLean.Foundations.Program.SchoenTransferQ3AbsoluteComparison
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers

/-! # The specified normalized component class under the singular comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual supplied normalized representative maps to its canonical component class. -/
theorem normalized_component_class_comparison
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [IsIntegral W.left] [Smooth W.hom] [IsProjective W.hom]
    (ι : Q ⟶ W) (k : ℕ) (hcod : Order.coheight (ι.left (genericPoint Q.left)) = k)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c) :
    singularToFieldCohomology ℚ W (2 * k)
      (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) =
        cycleComponentSheafClass W (ι.left (genericPoint Q.left)) hcod := by
  classical
  have hpure : ∀ p ∈ (s2e_componentCycle ι ℚ).support, Order.coheight p = k := by
    intro p hp
    rw [s2e_componentCycle_support] at hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact hcod
  have h := s4_q3_normalized_class_to_cycleClass W (s2e_componentCycle ι ℚ) k hpure c hc
  simpa only [s2e_componentCycle, prime_single_cycleClass W k _ hcod, one_smul] using h

#print axioms normalized_component_class_comparison
end HodgeLean.Foundations.Program.G32Native.EulerModel
