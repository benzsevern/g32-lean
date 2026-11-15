import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateIdealEvaluationIso
import HodgeLean.Foundations.Program.G32Native.PairedC3CyclicKernelIso

/-! # The supplied hyperplane quotient has its actual coordinate ideal kernel -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Every generating quotient arrow to the untwisted hyperplane module
has a kernel isomorphic to the actual negative twisting line.
Source: Hartshorne, Algebraic Geometry, II.5.12, the ideal sequence of a closed subscheme. -/
theorem paired_c3_route_n_quotient_kernel_aux
    (k : ℕ) (j : Fin (k + 1)) (Q : (pairedC3Proj k).Modules)
    (eQ : Q ≅ pairedC3HyperplaneQuotient k j)
    (q : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ Q) (hq : Epi q) :
    Nonempty (pairedC3NegativeLine k ≅ kernel q) := by
  let p := pairedC3HyperplaneUnit k j ≫ eQ.inv
  letI := hq
  letI : Epi (pairedC3HyperplaneUnit k j) := paired_c3_hyperplane_unit_epi k j
  letI : Epi p := inferInstance
  letI := paired_c3_coordinate_ideal_evaluation_isIso k j
  exact ⟨asIso (pairedC3CoordinateIdealEvaluation k j) ≪≫
    (pairedC3HyperplaneKernelNativeIso k j Q eQ).symm ≪≫ pairedC3CyclicKernelIso p q⟩

end HodgeLean.Foundations.Program.G32Native
