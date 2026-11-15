import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeCoordinateAction
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientLocalCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartPeriod
import HodgeLean.Foundations.Program.SchoenTowerL1bActionPeriodicDerivative

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The actual curve action in the centered scalar native coordinate. -/
def s2v_l1b_action_nativeCoordinate
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (z : ℂ) : ℂ :=
  ComplexPoint.localChart Y 1 p (Point.map f (s2e_u1_nativeCurve Y p z)) 0 -
    ComplexPoint.localChart Y 1 p p 0

/-- An action fixing the marked point has a native coordinate germ fixing zero. -/
theorem s2v_l1b_action_nativeCoordinate_zero
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hfix : Point.map f p = p) :
    s2v_l1b_action_nativeCoordinate Y p f 0 = 0 := by
  rw [s2v_l1b_action_nativeCoordinate, s2e_u1_nativeCurve_zero, hfix, sub_self]

/-- The native coordinate germ of a morphism fixing its marked point is
complex analytic at zero. -/
theorem s2v_l1b_action_nativeCoordinate_analytic
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hfix : Point.map f p = p) :
    AnalyticAt ℂ (s2v_l1b_action_nativeCoordinate Y p f) 0 := by
  let C := ComplexPoint.localChart Y 1 p
  have hv := s2e_fixed_morphism_centered_coordinates_analytic Y 1 f p hfix
  have hE : AnalyticAt ℂ (fun z : ℂ => b6m_surfaceCoordinateEquiv z) 0 :=
    b6m_surfaceCoordinateEquiv.toContinuousLinearMap.analyticAt _
  have hc := hv.comp_of_eq hE (map_zero b6m_surfaceCoordinateEquiv)
  have hp := ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 1)).analyticAt _).comp hc
  change AnalyticAt ℂ (fun z : ℂ => C (Point.map f
    (C.symm (fun i => z + C p i))) 0 - C p 0) 0 at hp
  change AnalyticAt ℂ (fun z : ℂ => C (Point.map f
    (C.symm (fun i => C p i + z))) 0 - C p 0) 0
  convert hp using 1
  funext z
  rw [show (fun i : Fin 1 => C p i + z) = (fun i => z + C p i) from
    funext (fun i => add_comm _ _)]

/-- An actual finite period of the curve action becomes the same local
period of its centered native coordinate germ. -/
theorem s2v_l1b_action_nativeCoordinate_period
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hfix : Point.map f p = p)
    (N : ℕ) (hperiod : ∀ q : ComplexPoint Y, (Point.map f)^[N] q = q) :
    ∀ᶠ z : ℂ in 𝓝 0, (s2v_l1b_action_nativeCoordinate Y p f)^[N] z = z := by
  let C := s2v_l1b_action_nativePlaneChart Y p
  have hx : p ∈ C.source := s2v_l1b_action_nativePlaneChart_source Y p
  have ht := s2v_l1b_action_centered_chart_period_eventually C p hx (Point.map f)
    (Point.continuous_map f).continuousAt hfix N hperiod
  have he : (fun z => C (Point.map f (C.symm (z + C p))) - C p) =
      s2v_l1b_action_nativeCoordinate Y p f := by
    funext z
    exact s2v_l1b_action_centered_native_action Y p f z
  rwa [he] at ht

/-- The derivative of an actual periodic native action is nonzero. -/
theorem s2v_l1b_action_nativeCoordinate_derivative_ne_zero
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    (p : ComplexPoint Y) (f : Y ⟶ Y) (hfix : Point.map f p = p)
    (N : ℕ) (hN : 0 < N) (hperiod : ∀ q : ComplexPoint Y, (Point.map f)^[N] q = q) :
    deriv (s2v_l1b_action_nativeCoordinate Y p f) 0 ≠ 0 := by
  exact s2v_l1b_action_periodic_derivative_ne_zero _
    (s2v_l1b_action_nativeCoordinate_analytic Y p f hfix).differentiableAt
    (s2v_l1b_action_nativeCoordinate_zero Y p f hfix) N hN
    (s2v_l1b_action_nativeCoordinate_period Y p f hfix N hperiod)

end HodgeLean.Foundations.Program
