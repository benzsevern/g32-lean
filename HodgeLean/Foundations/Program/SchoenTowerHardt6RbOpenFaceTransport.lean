import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Hull

/-! Intrinsic open faces are preserved by finite-dimensional linear coordinate changes. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_open_face_linear_transport {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
    (e : E ≃L[ℝ] F) (s : Finset E) :
    intrinsicInterior ℝ (convexHull ℝ (↑(s.image e) : Set F)) =
      e '' intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)) := by
  let a := e.toLinearEquiv.toAffineEquiv
  have hh : convexHull ℝ (↑(s.image e) : Set F) =
      a '' convexHull ℝ (↑s : Set E) := by
    rw [Finset.coe_image]
    exact (a.toAffineMap.image_convexHull _).symm
  rw [hh, a.intrinsicInterior_image]
  rfl

end HodgeLean.Foundations.Program
