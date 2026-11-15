import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import HodgeLean.Foundations.Program.SchoenTowerL1bChartAlgebra
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Binomial charts commute with extension of the coefficient ring.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Extension of coefficients in a binomial chart is its tensor base change,
with the actual coefficient map and the chart ratio retained. -/
theorem s2v_l1b_chart_tensor_equiv
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (u v : R) :
    ∃ e : (s2v_L1bChart u v ⊗[R] A) ≃+*
        s2v_L1bChart (algebraMap R A u) (algebraMap R A v),
      (∀ a, e (Algebra.TensorProduct.includeRight a) =
        Ideal.Quotient.mk _ (Polynomial.C a)) ∧
      e (Algebra.TensorProduct.includeLeftRingHom (R := R) (B := A) (Ideal.Quotient.mk _ Polynomial.X)) =
        Ideal.Quotient.mk _ Polynomial.X := by
  obtain ⟨e, heC, heX⟩ := AlgebraicGeometry.RegularPairChart.baseChangeEquiv (S := A) u v
  let c := Algebra.TensorProduct.comm R (s2v_L1bChart u v) A
  refine ⟨c.toRingEquiv.trans e.toRingEquiv, ?_, ?_⟩
  · intro a
    exact heC a
  · exact heX


end HodgeLean.Foundations.Program
