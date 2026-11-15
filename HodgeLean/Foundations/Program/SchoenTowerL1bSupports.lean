import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A principal ideal restriction detects its support by evaluation at complex points. -/
theorem s2v_l1b_evaluate_zero_iff_support
    (X : Over (Spec ↧ℂ)) (I : X.left.IdealSheafData)
    (U : X.left.affineOpens) (u : Γ(X.left, U))
    (hu : I.ideal U = Ideal.span {u})
    (y : ComplexPoint X) (hy : y ∈ Point.overOpen U.1) :
    Point.evaluate U.1 u y = 0 ↔ y.underlying ∈ I.support := by
  rw [I.mem_support_iff_of_mem hy, hu, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
  change Point.evaluate U.1 u y = 0 ↔ y ∉ Point.overOpen (X.left.basicOpen u)
  rw [Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero u y hy, not_not]

/-- Joint coordinate vanishing detects the actual sum of the selected ideals. -/
theorem s2v_l1b_evaluate_pair_zero_iff_support
    (X : Over (Spec ↧ℂ)) (I J : X.left.IdealSheafData)
    (U : X.left.affineOpens) (u v : Γ(X.left, U))
    (hu : I.ideal U = Ideal.span {u}) (hv : J.ideal U = Ideal.span {v})
    (y : ComplexPoint X) (hy : y ∈ Point.overOpen U.1) :
    (Point.evaluate U.1 u y = 0 ∧ Point.evaluate U.1 v y = 0) ↔
      y.underlying ∈ (I ⊔ J).support := by
  rw [s2v_l1b_evaluate_zero_iff_support X I U u hu y hy,
    s2v_l1b_evaluate_zero_iff_support X J U v hv y hy,
    Scheme.IdealSheafData.support_sup]
  rfl

end HodgeLean.Foundations.Program
