import HodgeLean.Foundations.Program.SchoenCycleU1CanonicalNumeratorOrders
import HodgeLean.Foundations.Program.SchoenCycleU1RetainedNumerator
import HodgeLean.Foundations.Program.SchoenCycleU1StationaryNumeratorOrders
import HodgeLean.Foundations.Program.SchoenCycleU1LineCoefficients

/-! # Local variation divisibility from actual retained numerator jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Manifold Filter Topology
open HodgeLean.Adapters
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Program

/-- Actual retained divisor tuples, a regular support coordinate, and a
stationary quotient curve jet force analytic local divisibility of the
canonical differential variation, with arbitrary base multiplicities.
Source: ACGH, Geometry of Algebraic Curves I, Chapters I and IV;
Gunning--Rossi, Analytic Functions of Several Complex Variables, Chapter II, section B. -/
theorem s2e_u1_canonical_local_divisibility_of_retained_jet
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B)
    (U : Z.left.Opens) (V : B.left.Opens) (hVa : IsAffineOpen V)
    (hVU : γ.left ⁻¹ᵁ V ≤ s2e_u1_powerOpen Z N U) (s : Γ(Z.left, U))
    (Q : Polynomial Γ(B.left, V))
    (hQ : Q.map (γ.left.app V).hom = ∏ i : Fin N,
      (Polynomial.X - Polynomial.C (s2e_u1_coordinateSection Z B N γ U V hVU s i)))
    (θ δ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) (hθ : θ ≠ 0)
    (p : ComplexPoint Z) (hp : p.underlying ∈ U)
    (hs : deriv (fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)) 0 ≠ 0)
    (b : ℂ → ComplexPoint B)
    (hb : ∀ᶠ t in 𝓝 (0 : ℂ), (b t).underlying ∈ V)
    (hba : ∀ a : Γ(B.left, V), AnalyticAt ℂ (fun t => Point.evaluate V a (b t)) 0)
    (hb0 : (b 0).underlying ∈ V)
    (hjet : s2e_u1_curveJet B V hVa b hb hba =
      s2e_u1_curveJet B V hVa (fun _ => b 0)
        (Filter.Eventually.of_forall (fun _ => hb0)) (fun _ => analyticAt_const))
    (x0 : Fin N → ComplexPoint Z)
    (hdiv0 : b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
      ∑ i, Finsupp.single (x0 i) (1 : ℤ))
    (hbtuple : b 0 = Point.map γ (s2_lift N x0))
    (hsep : ∀ i, Point.evaluate U s (x0 i) = Point.evaluate U s p ↔ x0 i = p)
    (hfamily : ∀ᶠ t in 𝓝 (0 : ℂ), ∃ x : Fin N → ComplexPoint Z,
      (θ + t • δ) ≠ 0 ∧
      b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ) (θ + t • δ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) =
        ∑ i, Finsupp.single (x i) (1 : ℤ) ∧
      b t = Point.map γ (s2_lift N x)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) δ p =ᶠ[𝓝 0]
        (fun z => g z * HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p z) := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  let c : ℂ → ℂ := fun z => Point.evaluate U s (s2e_u1_differentialChartCurve Z p z)
  obtain ⟨hca, hcd⟩ := s2e_u1_differentialChartCurve_regular_coordinate Z p U hp s hs
  let F := s2e_u1_regularPolynomialNumerator B V Q b c
  have hFa : AnalyticAt ℂ F (0, 0) :=
    s2e_u1_regularPolynomialNumerator_analyticAt B V Q b c hba hca
  have hF0 : (fun z => F (0, z)) = (fun z =>
      (∏ i : Fin N, (Polynomial.X - Polynomial.C (Point.evaluate U s (x0 i)))).eval (c z)) := by
    funext z
    exact s2e_u1_regularPolynomialNumerator_retained_tuple Z B N γ U V hVU s Q hQ
      b c 0 z hb0 x0 hbtuple
  have hbase : analyticOrderAt (fun z => F (0, z)) 0 =
      analyticOrderAt (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p) 0 := by
    rw [hF0]
    exact s2e_u1_canonical_coordinate_numerator_base_order Z θ hθ p x0 hdiv0
      (Point.evaluate U s) hsep hca hcd
  have hline : ContinuousAt (fun z : ℂ =>
      extChartAt 𝓘(ℂ, Fin 1 → ℂ) p p +
        b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) z) 0 :=
    continuousAt_const.add (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).continuousAt
  have htarget0 : extChartAt 𝓘(ℂ, Fin 1 → ℂ) p p +
      b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 0 ∈
        (extChartAt 𝓘(ℂ, Fin 1 → ℂ) p).target := by
    simpa only [map_zero, add_zero] using mem_extChartAt_target p
  have htarget := hline.eventually ((isOpen_extChartAt_target p).mem_nhds htarget0)
  have hz := (hca.eventually_analyticAt.and (hca.deriv.continuousAt.eventually_ne hcd)).and htarget
  have hdom : ∀ᶠ tz in 𝓝 ((0, 0) : ℂ × ℂ),
      analyticOrderAt (fun z => HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p z +
        tz.1 * HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) δ p z) tz.2 ≤
          analyticOrderAt (fun z => F (tz.1, z)) tz.2 := by
    filter_upwards [continuousAt_fst.tendsto.eventually (hfamily.and hb),
      continuousAt_snd.tendsto.eventually hz] with tz ht hz
    obtain ⟨x, hne, hdiv, hbt⟩ := ht.1
    have heval : (fun z => F (tz.1, z)) = (fun z =>
        (∏ i : Fin N, (Polynomial.X - Polynomial.C (Point.evaluate U s (x i)))).eval (c z)) := by
      funext z
      exact s2e_u1_regularPolynomialNumerator_retained_tuple Z B N γ U V hVU s Q hQ
        b c tz.1 z ht.2 x hbt
    rw [heval]
    have hh := s2e_u1_canonical_coordinate_numerator_order_bound Z (θ + tz.1 • δ) hne p tz.2
      hz.2 x hdiv (Point.evaluate U s) hz.1.1 hz.1.2
    rw [s2e_u1_holomorphic_line_coefficient] at hh
    exact hh
  obtain ⟨d, hd, _⟩ := s2e_holomorphic_divisor_analytic_order
    (Module.finrank_fin_fun (n := 1) ℂ) θ hθ p
  exact s2e_u1_stationary_numerator_orders_divisibility _ _ F
    (RiemannRochEichler_loc_analytic (Module.finrank_fin_fun (n := 1) ℂ) θ p)
    (RiemannRochEichler_loc_analytic (Module.finrank_fin_fun (n := 1) ℂ) δ p)
    hFa hdom d (hbase.trans hd) hd
    (Filter.Eventually.of_forall
      (s2e_u1_regularPolynomialNumerator_stationary B V hVa Q b c hb hba hb0 hjet))

end HodgeLean.Foundations.Program
