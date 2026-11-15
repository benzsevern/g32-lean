import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts

/-! The actual zero-normal support section of the canonical flattening chart. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
namespace HodgeLean.Foundations.Program

/-- The inverse normal-coordinate change on the zero-normal plane is
exactly the coordinate expression of the actual support embedding. -/
theorem s4_q3_closed_normal_inverse_zero
    (X D : Over (Spec ↧ℂ)) (i : D ⟶ X) (r d : ℕ)
    [SmoothOfRelativeDimension r D.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint D) (u : Fin r → ℂ) :
    (closedImmersionNormalCoordinateChange X D i r d z).symm (u, 0) =
      inclusionInComplexCharts X D i r d z u := by
  change (closedImmersionNormalChart X D i r d z)
    ((closedImmersionNormalCoordinatesLinearEquiv X D i r d z).symm (u, 0)) = _
  have he : (closedImmersionNormalCoordinatesLinearEquiv X D i r d z).symm (u, 0) =
      (u, 0) := by
    simp [closedImmersionNormalCoordinatesLinearEquiv]
  rw [he, closedImmersionNormalChart_apply]
  simp

/-- Near the chosen support point, the zero-normal section of the canonical
ambient chart is precisely the actual support chart followed by its embedding. -/
theorem s4_q3_support_chart_inverse_zero_eventually
    (X D : Over (Spec ↧ℂ)) (i : D ⟶ X) (r d : ℕ)
    [SmoothOfRelativeDimension r D.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint D) :
    (fun u => (closedImmersionHolomorphicFlatteningChart X D i r d z).symm (u, 0))
      =ᶠ[𝓝 (localChart D r z z)]
    (fun u => Point.map i ((localChart D r z).symm u)) := by
  let χD := localChart D r z
  let χX := localChart X d (Point.map i z)
  have hxD := mem_localChart_source D r z
  have hxX := mem_localChart_source X d (Point.map i z)
  have hc : ContinuousAt (fun u => Point.map i (χD.symm u)) (χD z) :=
    (Point.continuous_map i).continuousAt.comp (χD.continuousAt_symm (χD.map_source hxD))
  have hnear : ∀ᶠ u in 𝓝 (χD z), Point.map i (χD.symm u) ∈ χX.source := by
    apply hc.preimage_mem_nhds
    rw [χD.left_inv hxD]
    exact χX.open_source.mem_nhds hxX
  filter_upwards [hnear] with u hu
  rw [closedImmersionHolomorphicFlatteningChart_symm_apply, s4_q3_closed_normal_inverse_zero]
  change χX.symm (χX (Point.map i (χD.symm u))) = _
  exact χX.left_inv hu

end HodgeLean.Foundations.Program
