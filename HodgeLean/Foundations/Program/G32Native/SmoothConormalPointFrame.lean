import HodgeLean.Foundations.Program.G32Native.ModulePointFrame
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Dimensions of actual smooth conormal point fibres -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Actual local smooth conormal frames give an identification of the
actual point fibre of the conormal with its expected number of coefficients. -/
def smoothConormalPointFrameEquiv (Q W : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom] [SmoothOfRelativeDimension (n + k) W.hom]
    (i : Q ⟶ W) [IsClosedImmersion i.left] (x : ComplexPoint Q) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj (Conormal.sheaf i.left)) ≃ₗ[ℂ] (Fin k → ℂ) := by
  let h := s2e_smooth_closedImmersion_conormal_frames Q W n k i x.underlying
  let U := Classical.choose h
  have hx := (Classical.choose_spec h).1
  let e := Classical.choice (Classical.choose_spec h).2
  exact modulePointFrameEquiv (Conormal.sheaf i.left) U x hx k
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫ e)

/-- The actual dual conormal point fibre has the expected complex dimension. -/
theorem smoothNormalPoint_finrank (Q W : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom] [SmoothOfRelativeDimension (n + k) W.hom]
    (i : Q ⟶ W) [IsClosedImmersion i.left] (x : ComplexPoint Q) :
    Module.finrank ℂ (normalFibreOfModule (Conormal.sheaf i.left) x) = k := by
  unfold normalFibreOfModule
  rw [Subspace.dual_finrank_eq, (smoothConormalPointFrameEquiv Q W n k i x).finrank_eq,
    Module.finrank_fin_fun]

/-- The actual dual conormal point fibre is finite dimensional over the
original complex scalar field. -/
theorem smoothNormalPoint_finiteDimensional (Q W : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom] [SmoothOfRelativeDimension (n + k) W.hom]
    (i : Q ⟶ W) [IsClosedImmersion i.left] (x : ComplexPoint Q) :
    FiniteDimensional ℂ (normalFibreOfModule (Conormal.sheaf i.left) x) := by
  let e := smoothConormalPointFrameEquiv Q W n k i x
  letI := FiniteDimensional.of_injective e.toLinearMap e.injective
  unfold normalFibreOfModule
  infer_instance

#print axioms smoothNormalPoint_finiteDimensional
#print axioms smoothNormalPoint_finrank
#print axioms smoothConormalPointFrameEquiv
end HodgeLean.Foundations.Program.G32Native
