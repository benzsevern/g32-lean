import HodgeLean.Foundations.Program.CycleFoundationsIntegration
import HodgeLean.RealDefs.FiniteBettiCompact

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An actual complex point normalizes a rational top cohomology coordinate on a smooth projective variety.
Source: the normalized nonzero point class, fundamental class and rational top rank one. -/
theorem s4_selected_point_top_coordinate
    (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (a : ℕ) (hA : TopologicalSpace.dim A.left = a) (e : ComplexPoint A) :
    ∃ (hec : Order.coheight e.underlying = a) (I : HQ A (2 * a) ≃ₗ[ℚ] ℚ),
      I (cycleComponentSheafClass A e.underlying hec) = 1 := by
  letI : SmoothOfRelativeDimension a A.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
    rwa [hA] at h
  letI := (finbetti_finiteBetti A).finite (2 * a)
  have hclosed : IsClosed ({e.underlying} : Set A.left) :=
    ((pointEquivClosedPoint A.hom) ⟨e.left, by simp⟩).2
  have hec : Order.coheight e.underlying = a :=
    SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := A.hom) e.underlying hclosed
  let t := cycleComponentSheafClass A e.underlying hec
  obtain ⟨w, hw⟩ := j5c_exists_complexFundamentalClass A a
  have ht : t ≠ 0 := cycleComponentSheafClass_ne_zero_of_fundamentalClass A a e.underlying hec w hw
  have hr : Module.finrank ℚ (HQ A (2 * a)) = 1 := j5d_finrank_HQ_top complexPointsPreconnected A a
  let E : HQ A (2 * a) ≃ₗ[ℚ] ℚ := LinearEquiv.ofFinrankEq (R := ℚ) (HQ A (2 * a)) ℚ (by simpa using hr)
  have hEt : E t ≠ 0 := fun h => ht (E.injective (h.trans E.map_zero.symm))
  let I := E.trans (LinearEquiv.smulOfNeZero ℚ ℚ (E t)⁻¹ (inv_ne_zero hEt))
  refine ⟨hec, I, ?_⟩
  change (E t)⁻¹ * E t = 1
  exact inv_mul_cancel₀ hEt

#print axioms s4_selected_point_top_coordinate
end HodgeLean.Foundations.Program
