import HodgeLean.Foundations.QuotientDuality.LocalHolomorphicCoordinateExpression
import HodgeLean.Foundations.QuotientDuality.LocalImmersionOrientationFamily
import HodgeLean.Foundations.QuotientDuality.LocalAnalyticChartCalibration

/-! Ambient holomorphic charts agree with the complex orientation of a smooth open immersion. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

variable (A X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : A ⟶ X) [IsOpenImmersion j.left]

theorem immersion_holomorphic_chart_transition_analytic
    (F : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (hF : ∀ i, (f4_analytification X).IsHolFun (fun y : F.source => F y i))
    (z : ComplexPoint A) :
    AnalyticOnNhd ℂ (fun v => F (((localChart A d z).lift_openEmbedding
      (HodgeLean.Foundations.ComplexTopology.openImmersion_points j)).symm v))
      (((localChart A d z).lift_openEmbedding
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points j)).symm.trans F).source := by
  have hp (i : Fin d) := (f4_map_isHom j).2 F.source F.open_source
    (fun y => F y i) (hF i)
  have ha := holomorphic_coordinates_localChart_analytic A d (fun y => F (Point.map j y))
    ((Point.map j) ⁻¹' F.source) (F.open_source.preimage (Point.continuous_map j)) hp z
  convert ha using 1 <;> rfl

theorem immersion_complex_orientation_holomorphic_chart
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (hn : ∀ z, o.generator (Point.map j z) = immersionComplexOrientation A X d j z)
    (F : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (hF : ∀ i, (f4_analytification X).IsHolFun (fun y : F.source => F y i))
    (z : ComplexPoint A) (hz : Point.map j z ∈ F.source) :
    o.generator (Point.map j z) = localClassOfChart d F (Point.map j z) hz := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  let hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  let E := (localChart A d z).lift_openEmbedding hj
  have hzE : Point.map j z ∈ E.source := ⟨z, mem_localChart_source A d z, rfl⟩
  apply chart_orientation_normalized_of_analytic_transition (TopCat.of (ComplexPoint X)) d o
    E F (Point.map j z) hzE hz
  · intro y hy _
    obtain ⟨t, ht, rfl⟩ := hy
    have hcan := complexLocalOrientation_eq_localClassOfChart_localChart A d z t ht
    have hlift := localClassOfChart_lift_openEmbedding (Point.map j) hj d (localChart A d z) t ht
    exact (hn t).trans ((congrArg (relativeHomologyMap ℚ (2 * d)
      (imagePointPairMap (TopCat.ofHom (Point.continuousMap j)) hj.injective t)) hcan).trans hlift)
  · exact immersion_holomorphic_chart_transition_analytic A X d j F hF z

#print axioms immersion_holomorphic_chart_transition_analytic
#print axioms immersion_complex_orientation_holomorphic_chart
end HodgeLean.Foundations.QuotientDuality
