import HodgeLean.Foundations.QuotientDuality.LocalImmersionOrientationFamily

/-! Holomorphic normalization determines the orientation on every smooth open immersion. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem normalized_orientation_on_smooth_immersion
    (A X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : A ⟶ X) [IsOpenImmersion j.left]
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (hn : ∀ (x : ComplexPoint X) (F : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
      (hx : x ∈ F.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : F.source => F y i)) →
      o.generator x = localClassOfChart d F x hx)
    (z : ComplexPoint A) :
    o.generator (Point.map j z) = immersionComplexOrientation A X d j z := by
  let hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  let E := localChart A d z
  have hz : z ∈ E.source := mem_localChart_source A d z
  have H := hn (Point.map j z) (E.lift_openEmbedding hj) ⟨z, hz, rfl⟩
    (immersion_localChart_coordinates_holomorphic A X j d z)
  refine H.trans ?_
  rw [← localClassOfChart_lift_openEmbedding (Point.map j) hj d E z hz]
  exact congrArg (relativeHomologyMap ℚ (2 * d)
    (imagePointPairMap (TopCat.ofHom (Point.continuousMap j)) hj.injective z))
    (complexLocalOrientation_eq_localClassOfChart_localChart A d z z hz).symm

#print axioms normalized_orientation_on_smooth_immersion
end HodgeLean.Foundations.QuotientDuality
