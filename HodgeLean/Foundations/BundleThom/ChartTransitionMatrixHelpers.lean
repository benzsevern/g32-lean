import HodgeLean.Foundations.BundleThom.LocalNormalOrientationHelpers
import HodgeLean.Foundations.BundleThom.LinearChartTransitionHelpers

/-! # Actual matrix families for complex bundle chart transitions

Matrix coordinates retain the supplied pair of linear trivializations and their actual overlap.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Bundle
namespace HodgeLean.Foundations.BundleThom

variable {B : Type} [TopologicalSpace B] (k : ℕ) (E : B → Type)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
variable (e e' : Trivialization (Fin k → ℂ) (TotalSpace.proj : TotalSpace (Fin k → ℂ) E → B))
variable [e.IsLinear ℂ] [e'.IsLinear ℂ]

/-- The actual coordinate transition matrix on the supplied chart overlap.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex transition functions. -/
def i1_chartTransitionMatrix (b : ↥(e.baseSet ∩ e'.baseSet)) : Matrix (Fin k) (Fin k) ℂ :=
  LinearMap.toMatrix' (e.coordChangeL ℂ e' b.1).toLinearMap

/-- The actual transition matrix acts by the supplied chart coordinate change.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex transition functions. -/
theorem i1_chartTransitionMatrix_mulVec (b : ↥(e.baseSet ∩ e'.baseSet)) (v : Fin k → ℂ) :
    (i1_chartTransitionMatrix k E e e' b).mulVec v = e.coordChangeL ℂ e' b.1 v :=
  LinearMap.toMatrix'_mulVec _ v

/-- The actual matrix family of two linear charts is continuous on their overlap.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex transition functions. -/
theorem i1_chartTransitionMatrix_continuous : Continuous (i1_chartTransitionMatrix k E e e') := by
  have hc := continuousOn_iff_continuous_domRestrict.mp
    (i1_linearChartTransition_continuousOn k E e e')
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun b : ↥(e.baseSet ∩ e'.baseSet) =>
    (e.coordChangeL ℂ e' b.1 (Pi.single j 1)) i)
  exact (continuous_apply i).comp (hc.clm_apply continuous_const)

/-- Every actual transition matrix on the supplied overlap has nonzero complex determinant.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, invertibility of transitions. -/
theorem i1_chartTransitionMatrix_det_ne_zero (b : ↥(e.baseSet ∩ e'.baseSet)) :
    (i1_chartTransitionMatrix k E e e' b).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  apply (e.coordChangeL ℂ e' b.1).injective
  simpa only [i1_chartTransitionMatrix_mulVec] using hvw

end HodgeLean.Foundations.BundleThom
