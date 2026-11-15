import HodgeLean.Foundations.QuotientDuality.LocalChartCalibration
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFibreParam
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

/-! Analytic transitions calibrate local chart classes using one regular point. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicTopology.Singular
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem chart_orientation_normalized_of_analytic_transition
    (X : TopCat.{0}) [T2Space X] (d : ℕ) (o : LocalRationalOrientation X (2 * d))
    (E F : OpenPartialHomeomorph X (Fin d → ℂ)) (x : X)
    (hx : x ∈ E.source) (hxF : x ∈ F.source)
    (hn : ∀ y (hy : y ∈ E.source), y ∈ chartOrientationNeighborhood d F x hxF →
      o.generator y = localClassOfChart d E y hy)
    (han : AnalyticOnNhd ℂ (fun v => F (E.symm v)) (E.symm.trans F).source) :
    o.generator x = localClassOfChart d F x hxF := by
  let U := chartOrientationNeighborhood d F x hxF
  let V := E.target ∩ E.symm ⁻¹' (U : Set X)
  have hV : IsOpen V := E.isOpen_inter_preimage_symm U.isOpen
  have hne : V.Nonempty := ⟨E x, E.map_source hx, by
    change E.symm (E x) ∈ U
    rw [E.left_inv hx]
    exact mem_chartOrientationNeighborhood d F x hxF⟩
  have hsub : V ⊆ (E.symm.trans F).source := by
    intro v hv
    exact ⟨hv.1, chartOrientationNeighborhood_subset_source d F x hxF hv.2⟩
  let g := fun v : Fin d → ℂ => F (E.symm v)
  have hinj : Set.InjOn g V := by
    intro v hv w hw heq
    apply E.symm.injOn hv.1 hw.1
    exact F.injOn (chartOrientationNeighborhood_subset_source d F x hxF hv.2)
      (chartOrientationNeighborhood_subset_source d F x hxF hw.2) heq
  have hfin : ∀ w, {v | v ∈ V ∧ g v = w}.Finite := by
    intro w
    apply Set.Subsingleton.finite
    intro v hv z hz
    exact hinj hv.1 hz.1 (hv.2.trans hz.2.symm)
  obtain ⟨v, hv, hderiv⟩ := ancrs_exists_injective_of_finite_fibres hV hne (han.mono hsub) hfin
  have hyE : E.symm v ∈ E.source := E.map_target hv.1
  have hyF : E.symm v ∈ F.source :=
    chartOrientationNeighborhood_subset_source d F x hxF hv.2
  have hd : HasFDerivAt g (fderiv ℂ g v) (E (E.symm v)) := by
    rw [E.right_inv hv.1]
    exact (han v (hsub hv)).differentiableAt.hasFDerivAt
  have he := localClassOfChart_eq_of_hasFDerivAt_transition d E F (E.symm v)
    hyE hyF (fderiv ℂ g v) hderiv hd
  exact chart_orientation_normalized_of_one_point X d o F x hxF (E.symm v) hv.2
    ((hn (E.symm v) hyE hv.2).trans he)

#print axioms chart_orientation_normalized_of_analytic_transition
end HodgeLean.Foundations.QuotientDuality
