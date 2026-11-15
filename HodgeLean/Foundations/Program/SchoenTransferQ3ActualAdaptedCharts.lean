import HodgeLean.Foundations.Program.SchoenTransferQ3EtaleSupportChartDerivative
import HodgeLean.Foundations.Program.SchoenTransferQ3AdaptedNormalCharts

/-! Support-flattening charts adapted to the actual ambient tangential morphism. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
namespace HodgeLean.Foundations.Program

/-- An actual etale support restriction gives an ambient support-flattening
chart whose tangential part is the actual ambient morphism in the target chart. -/
theorem s4_q3_actual_support_adapted_normal_chart
    (X D T : Over (Spec ↧ℂ)) (i : D ⟶ X) (h : X ⟶ T) (r d : ℕ)
    [SmoothOfRelativeDimension r D.hom] [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension r T.hom] [IsClosedImmersion i.left]
    [Etale (i ≫ h).left] (z : ComplexPoint D) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin r → ℂ) × (Fin (d - r) → ℂ)),
      Point.map i z ∈ e.source ∧
      e.source ⊆ (closedImmersionHolomorphicFlatteningChart X D i r d z).source ∧
      (∀ y ∈ e.source, e y =
        (localChart T r (Point.map (i ≫ h) z) (Point.map h y),
          (closedImmersionHolomorphicFlatteningChart X D i r d z y).2)) ∧
      ∀ y ∈ e.source, y ∈ Set.range (Point.map i) ↔ (e y).2 = 0 := by
  let e0 := closedImmersionHolomorphicFlatteningChart X D i r d z
  let x := Point.map i z
  let G := fun y => localChart T r (Point.map (i ≫ h) z) (Point.map h y)
  have hx : x ∈ e0.source := closedImmersionHolomorphicFlatteningChart_mem_source X D i r d z
  have hx0 : (e0 x).2 = 0 := by
    simp only [e0, x, closedImmersionHolomorphicFlatteningChart_center]
  have hbij : Function.Bijective (fderiv ℂ (fun u => G (e0.symm (u, 0))) (e0 x).1) := by
    simpa only [e0, x, closedImmersionHolomorphicFlatteningChart_center, Prod.fst] using
      s4_q3_etale_support_tangential_derivative X D T i h r d z
  obtain ⟨e, hxe, hse, he⟩ := s4_q3_chart_adapted_to_tangential_map e0 x hx hx0 G
    (s4_q3_tangential_map_analytic_in_normal_chart X D T i h r d z) hbij
  refine ⟨e, hxe, hse, he, ?_⟩
  intro y hy
  have hn := congrArg Prod.snd (he y hy)
  change (e y).2 = (e0 y).2 at hn
  rw [hn]
  exact closedImmersionHolomorphicFlatteningChart_mem_range_iff X D i r d z y (hse hy)

/-- The retained actual tangential and canonical normal coordinate formula
is analytic in the original ambient chart at the support point. -/
theorem s4_q3_actual_adapted_chart_analytic
    (X D T : Over (Spec ↧ℂ)) (i : D ⟶ X) (h : X ⟶ T) (r d : ℕ)
    [SmoothOfRelativeDimension r D.hom] [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension r T.hom] [IsClosedImmersion i.left]
    (z : ComplexPoint D)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin (d - r) → ℂ)))
    (hx : Point.map i z ∈ e.source)
    (he : ∀ y ∈ e.source, e y =
      (localChart T r (Point.map (i ≫ h) z) (Point.map h y),
        (closedImmersionHolomorphicFlatteningChart X D i r d z y).2)) :
    AnalyticAt ℂ ((localChart X d (Point.map i z)).symm.trans e)
      (localChart X d (Point.map i z) (Point.map i z)) := by
  let x := Point.map i z
  let χ := localChart X d x
  let N := closedImmersionNormalCoordinateChange X D i r d z
  let G := fun y => localChart T r (Point.map (i ≫ h) z) (Point.map h y)
  have hxχ := mem_localChart_source X d x
  have hG : AnalyticAt ℂ (fun w => G (χ.symm w)) (χ x) := by
    dsimp only [G]
    rw [Point.map_comp_apply]
    exact analyticAt_inclusionInComplexCharts T X h d r x
  have hN : AnalyticAt ℂ N (χ x) :=
    analyticAt_closedImmersionNormalCoordinateChange X D i r d z
  have hA := hG.prod (analyticAt_snd.comp hN)
  have hc : ContinuousAt χ.symm (χ x) := χ.continuousAt_symm (χ.map_source hxχ)
  have hnear : ∀ᶠ w in 𝓝 (χ x), χ.symm w ∈ e.source := by
    apply hc.preimage_mem_nhds
    rw [χ.left_inv hxχ]
    exact e.open_source.mem_nhds hx
  have heq : (fun w => e (χ.symm w)) =ᶠ[𝓝 (χ x)]
      (fun w => (G (χ.symm w), (N w).2)) := by
    filter_upwards [hnear, χ.open_target.mem_nhds (χ.map_source hxχ)] with w hw ht
    rw [he _ hw]
    change (G (χ.symm w), (N (χ (χ.symm w))).2) = _
    rw [χ.right_inv ht]
  exact hA.congr heq.symm

end HodgeLean.Foundations.Program
