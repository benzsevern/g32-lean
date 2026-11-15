import HodgeLean.Foundations.Program.G32Native.CanonicalAbelOverlapComparison
import HodgeLean.Foundations.Program.G32Native.CanonicalPeriodDerivativeUniqueness

/-! # Derivatives of coherent lifts in a fixed ambient chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Quotient-germ equality survives passage to the original coordinates at the
point where the derivative is taken. -/
theorem canonicalPeriodQuotient_chart_germ (G : CanonicalAbelGeometry)
    (f g : ComplexPoint G.W → Fin (G.k + 1) → ℂ)
    (y : ComplexPoint G.W)
    (h : (fun w => canonicalPeriodQuotient G (f w)) =ᶠ[𝓝 y]
      (fun w => canonicalPeriodQuotient G (g w))) :
    (fun u => canonicalPeriodQuotient G
      (f ((localChart G.W (G.k + G.k) y).symm u)))
      =ᶠ[𝓝 (localChart G.W (G.k + G.k) y y)]
    (fun u => canonicalPeriodQuotient G
      (g ((localChart G.W (G.k + G.k) y).symm u))) := by
  let e := localChart G.W (G.k + G.k) y
  have hy : y ∈ e.source := mem_localChart_source _ _ _
  have ht : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    simpa only [ContinuousAt, e.left_inv hy] using (e.continuousAt_symm (e.map_source hy))
  exact h.comp_tendsto ht

#print axioms canonicalPeriodQuotient_chart_germ

/-- Coherent original lifts have the same derivative when both are read in the
chart at the second point. The fixed lift requires analyticity only at that
point of its own chart. -/
theorem canonicalChartAbelLift_fderiv_overlap (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x y : ComplexPoint G.Q)
    (hyx : Point.map G.ι y ∈
      (localChart G.W (G.k + G.k) (Point.map G.ι x)).source)
    (hx : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)))
    (hy : AnalyticAt ℂ (F y)
      (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)))
    (hq : (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
      =ᶠ[𝓝 (Point.map G.ι y)]
      (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w))) :
    fderiv ℂ (fun u => F x
      (localChart G.W (G.k + G.k) (Point.map G.ι x)
        ((localChart G.W (G.k + G.k) (Point.map G.ι y)).symm u)))
      (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)) =
    fderiv ℂ (F y)
      (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)) := by
  let ex := localChart G.W (G.k + G.k) (Point.map G.ι x)
  let ey := localChart G.W (G.k + G.k) (Point.map G.ι y)
  have hys : Point.map G.ι y ∈ ey.source := mem_localChart_source _ _ _
  have hyt : ey (Point.map G.ι y) ∈ ey.target := ey.map_source hys
  have htr : ey (Point.map G.ι y) ∈ (ey.symm.trans ex).source := by
    change ey (Point.map G.ι y) ∈ ey.target ∧ ey.symm (ey (Point.map G.ι y)) ∈ ex.source
    exact ⟨hyt, by simpa only [ey.left_inv hys] using hyx⟩
  have ha := analyticAt_localChart_transition G.W (G.k + G.k)
    (Point.map G.ι y) (Point.map G.ι x) htr
  have hfx : AnalyticAt ℂ (fun u => F x (ex (ey.symm u)))
      (ey (Point.map G.ι y)) := by
    apply AnalyticAt.comp ?_ ha
    change AnalyticAt ℂ (F x) (ex (ey.symm (ey (Point.map G.ι y))))
    rw [ey.left_inv hys]
    exact hx
  apply canonicalPeriodQuotient_fderiv_eq G hfx.differentiableAt hy.differentiableAt
  have hg := canonicalPeriodQuotient_chart_germ G _ _ _ hq
  have hi : ∀ᶠ u in 𝓝 (ey (Point.map G.ι y)), ey (ey.symm u) = u := by
    filter_upwards [ey.open_target.mem_nhds hyt] with u hu
    exact ey.right_inv hu
  filter_upwards [hg, hi] with u hu hiu
  change canonicalPeriodQuotient G (F x (ex (ey.symm u))) = _ at hu
  exact hu.trans (congrArg (fun v => canonicalPeriodQuotient G (F y v)) hiu)

#print axioms canonicalChartAbelLift_fderiv_overlap


/-- The coherence neighborhood can be shrunk so one original analytic lift
supplies the coordinate derivative at every component point in it. -/
theorem coherentPeriodLifts_fixedChart_neighbourhood (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (hanalytic : ∀ x : ComplexPoint G.Q, AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hoverlap : ∀ x : ComplexPoint G.Q, ∃ U : Set (ComplexPoint G.W),
      IsOpen U ∧ Point.map G.ι x ∈ U ∧
      ∀ y : ComplexPoint G.Q, Point.map G.ι y ∈ U →
        (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
          =ᶠ[𝓝 (Point.map G.ι y)]
        (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w)))
    (x : ComplexPoint G.Q) :
    ∃ U : Set (ComplexPoint G.W), IsOpen U ∧ Point.map G.ι x ∈ U ∧
      ∀ y : ComplexPoint G.Q, Point.map G.ι y ∈ U →
        Point.map G.ι y ∈ (localChart G.W (G.k + G.k) (Point.map G.ι x)).source ∧
        AnalyticAt ℂ (F x)
          (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)) ∧
        fderiv ℂ (fun u => F x
          (localChart G.W (G.k + G.k) (Point.map G.ι x)
            ((localChart G.W (G.k + G.k) (Point.map G.ι y)).symm u)))
          (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)) =
        fderiv ℂ (F y)
          (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)) := by
  let ex := localChart G.W (G.k + G.k) (Point.map G.ι x)
  have hxs : Point.map G.ι x ∈ ex.source := mem_localChart_source _ _ _
  have he : ∀ᶠ w in 𝓝 (Point.map G.ι x), AnalyticAt ℂ (F x) (ex w) :=
    (ex.continuousAt hxs).eventually (hanalytic x).eventually_analyticAt
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp he
  obtain ⟨U, hUo, hxU, hU⟩ := hoverlap x
  refine ⟨U ∩ (V ∩ ex.source), hUo.inter (hVo.inter ex.open_source),
    ⟨hxU, hxV, hxs⟩, ?_⟩
  intro y hy
  have hfy := hV hy.2.1
  exact ⟨hy.2.2, hfy,
    canonicalChartAbelLift_fderiv_overlap G F x y hy.2.2 hfy (hanalytic y) (hU y hy.1)⟩

#print axioms coherentPeriodLifts_fixedChart_neighbourhood


/-- A lift analytic at its original center has a continuous derivative field
in that fixed ambient chart on a neighborhood of the center. -/
theorem canonicalLift_fixedChart_derivative_continuousOn (G : CanonicalAbelGeometry)
    (F : (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.W)
    (hF : AnalyticAt ℂ F (localChart G.W (G.k + G.k) x x)) :
    ∃ U : Set (ComplexPoint G.W), IsOpen U ∧ x ∈ U ∧
      ContinuousOn (fun w => fderiv ℂ F (localChart G.W (G.k + G.k) x w)) U := by
  let e := localChart G.W (G.k + G.k) x
  have hxs : x ∈ e.source := mem_localChart_source _ _ _
  have he : ∀ᶠ w in 𝓝 x, AnalyticAt ℂ F (e w) :=
    (e.continuousAt hxs).eventually hF.eventually_analyticAt
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp he
  refine ⟨V ∩ e.source, hVo.inter e.open_source, ⟨hxV, hxs⟩, ?_⟩
  intro w hw
  have hd : ContinuousAt (fderiv ℂ F) (e w) :=
    ((hV hw.1).contDiffAt (n := 1)).continuousAt_fderiv (by simp)
  exact (hd.comp (e.continuousAt hw.2)).continuousWithinAt

#print axioms canonicalLift_fixedChart_derivative_continuousOn


/-- The original coefficient differential on an overlap is computed from the
fixed lift and the actual change of ambient coordinates. -/
theorem canonicalAbelDifferential_fixedChart (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x y : ComplexPoint G.Q)
    (hyx : Point.map G.ι y ∈
      (localChart G.W (G.k + G.k) (Point.map G.ι x)).source)
    (hx : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)))
    (hy : AnalyticAt ℂ (F y)
      (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)))
    (hq : (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
      =ᶠ[𝓝 (Point.map G.ι y)]
      (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w))) :
    canonicalAbelDifferential G F y =
      (coefficientDual G.k).comp
        ((fderiv ℂ (F x)
          (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y))).comp
          (fderiv ℂ (fun u => localChart G.W (G.k + G.k) (Point.map G.ι x)
            ((localChart G.W (G.k + G.k) (Point.map G.ι y)).symm u))
            (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)))).toLinearMap := by
  let ex := localChart G.W (G.k + G.k) (Point.map G.ι x)
  let ey := localChart G.W (G.k + G.k) (Point.map G.ι y)
  have hys : Point.map G.ι y ∈ ey.source := mem_localChart_source _ _ _
  have htr : ey (Point.map G.ι y) ∈ (ey.symm.trans ex).source := by
    change ey (Point.map G.ι y) ∈ ey.target ∧ ey.symm (ey (Point.map G.ι y)) ∈ ex.source
    exact ⟨ey.map_source hys, by simpa only [ey.left_inv hys] using hyx⟩
  have ha := analyticAt_localChart_transition G.W (G.k + G.k)
    (Point.map G.ι y) (Point.map G.ι x) htr
  have hx' : DifferentiableAt ℂ (F x) (ex (ey.symm (ey (Point.map G.ι y)))) := by
    rw [ey.left_inv hys]
    exact hx.differentiableAt
  have hd := (canonicalChartAbelLift_fderiv_overlap G F x y hyx hx hy hq).symm.trans
    (fderiv_comp (ey (Point.map G.ι y)) hx' ha.differentiableAt)
  have hd' : fderiv ℂ (F y) (ey (Point.map G.ι y)) =
      (fderiv ℂ (F x) (ex (Point.map G.ι y))).comp
        (fderiv ℂ (fun u => ex (ey.symm u)) (ey (Point.map G.ι y))) := by
    change fderiv ℂ (F y) (ey (Point.map G.ι y)) =
      (fderiv ℂ (F x) (ex (ey.symm (ey (Point.map G.ι y))))).comp
        (fderiv ℂ (fun u => ex (ey.symm u)) (ey (Point.map G.ι y))) at hd
    simpa only [ey.left_inv hys] using hd
  change (coefficientDual G.k).comp
    (fderiv ℂ (F y) (ey (Point.map G.ι y))).toLinearMap = _
  rw [hd']

#print axioms canonicalAbelDifferential_fixedChart

end HodgeLean.Foundations.Program.G32Native
