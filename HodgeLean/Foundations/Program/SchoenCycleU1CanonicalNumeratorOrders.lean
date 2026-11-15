import HodgeLean.Foundations.Program.SchoenCycleU1CoordinateOrders
import HodgeLean.Foundations.Program.SchoenCycleU1DifferentialChartCoordinate
import HodgeLean.Foundations.Program.SchoenCycleCanonicalFamily

/-! # Actual differential divisor orders dominated by coordinate numerators -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Manifold
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual canonical coefficient order is bounded by the coordinate
numerator order whenever the coordinate is regular in the differential line.
The tuple equality retains the full canonical divisor multiplicities.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, local divisor orders;
HodgeLean, `s2e_holomorphic_divisor_order_on_chart`. -/
theorem s2e_u1_canonical_coordinate_numerator_order_bound
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) (hθ : θ ≠ 0)
    (p : ComplexPoint Z) (z : ℂ)
    (ht : extChartAt 𝓘(ℂ, Fin 1 → ℂ) p p +
      b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) z ∈
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) p).target)
    {N : ℕ} (x : Fin N → ComplexPoint Z)
    (hdiv : b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
      ∑ i, Finsupp.single (x i) (1 : ℤ))
    (c : ComplexPoint Z → ℂ)
    (hg : AnalyticAt ℂ (fun w => c (s2e_u1_differentialChartCurve Z p w)) z)
    (hg' : deriv (fun w => c (s2e_u1_differentialChartCurve Z p w)) z ≠ 0) :
    analyticOrderAt (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p) z ≤
      analyticOrderAt (fun w =>
        (∏ i : Fin N, (Polynomial.X - Polynomial.C (c (x i)))).eval
          (c (s2e_u1_differentialChartCurve Z p w))) z := by
  classical
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  obtain ⟨d, hd, hD⟩ := s2e_holomorphic_divisor_order_on_chart
    (Module.finrank_fin_fun (n := 1) ℂ) θ hθ p z ht
  have hm := congrArg (fun D : ComplexPoint Z →₀ ℤ =>
    D (s2e_u1_differentialChartCurve Z p z)) hdiv
  rw [← s2e_tuple_integer_divisor] at hm
  simp only [Finsupp.mapRange_apply, Multiset.toFinsupp_apply, Multiset.coe_count,
    s2e_tuple_count_eq_fiber_card] at hm
  have hc : d = Fintype.card {i : Fin N // x i = s2e_u1_differentialChartCurve Z p z} := by
    exact_mod_cast hD.trans hm
  rw [hd, hc]
  exact s2e_u1_coordinate_polynomial_analyticOrder_lower_bound x c _ z hg hg'
    (s2e_u1_differentialChartCurve Z p z) rfl

/-- At a support-separated base divisor the actual coordinate numerator and
native canonical coefficient have exactly the same finite order.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, local divisor multiplicities. -/
theorem s2e_u1_canonical_coordinate_numerator_base_order
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) (hθ : θ ≠ 0)
    (p : ComplexPoint Z) {N : ℕ} (x : Fin N → ComplexPoint Z)
    (hdiv : b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
      ∑ i, Finsupp.single (x i) (1 : ℤ))
    (c : ComplexPoint Z → ℂ) (hsep : ∀ i, c (x i) = c p ↔ x i = p)
    (hg : AnalyticAt ℂ (fun w => c (s2e_u1_differentialChartCurve Z p w)) 0)
    (hg' : deriv (fun w => c (s2e_u1_differentialChartCurve Z p w)) 0 ≠ 0) :
    analyticOrderAt (fun w =>
      (∏ i : Fin N, (Polynomial.X - Polynomial.C (c (x i)))).eval
        (c (s2e_u1_differentialChartCurve Z p w))) 0 =
      analyticOrderAt (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p) 0 := by
  classical
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  have hzero : s2e_u1_differentialChartCurve Z p 0 = p := by
    rw [s2e_u1_differentialChartCurve_reparam, mul_zero, s2e_u1_nativeCurve_zero]
  have hsep' (i : Fin N) : c (x i) = c (s2e_u1_differentialChartCurve Z p 0) ↔ x i = p := by
    simpa only [hzero] using hsep i
  rw [s2e_u1_coordinate_polynomial_analyticOrder_of_separation x c _ 0 hg hg' p hsep']
  obtain ⟨d, hd, hD⟩ := s2e_holomorphic_divisor_analytic_order
    (Module.finrank_fin_fun (n := 1) ℂ) θ hθ p
  have hm := congrArg (fun D : ComplexPoint Z →₀ ℤ => D p) hdiv
  rw [← s2e_tuple_integer_divisor] at hm
  simp only [Finsupp.mapRange_apply, Multiset.toFinsupp_apply, Multiset.coe_count,
    s2e_tuple_count_eq_fiber_card] at hm
  have hc : d = Fintype.card {i : Fin N // x i = p} := by exact_mod_cast hD.trans hm
  rw [hd, hc]

end HodgeLean.Foundations.Program
