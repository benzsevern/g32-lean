import HodgeLean.Foundations.QuotientDuality.ModificationChartLocalDegree
import HodgeLean.Foundations.QuotientDuality.LocalImmersionHolomorphicCharts

/-! Complex-normalized generators have degree one on an algebraic isomorphism open. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem singletonFibre_map_complex_generators
    (A X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (oX : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (oY : LocalRationalOrientation (TopCat.of (ComplexPoint Y)) (2 * d))
    (hnX : ∀ (x : ComplexPoint X)
      (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)) (hx : x ∈ E.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : E.source => E y i)) →
      oX.generator x = localClassOfChart d E x hx)
    (hnY : ∀ (y : ComplexPoint Y)
      (E : OpenPartialHomeomorph (ComplexPoint Y) (Fin d → ℂ)) (hy : y ∈ E.source),
      (∀ i, (f4_analytification Y).IsHolFun (fun z : E.source => E z i)) →
      oY.generator y = localClassOfChart d E y hy)
    (j : A ⟶ X) [IsOpenImmersion j.left] (f : X ⟶ Y)
    [IsOpenImmersion (j ≫ f).left] (z : ComplexPoint A)
    (hf : ∀ x, Point.map f x = Point.map f (Point.map j z) → x = Point.map j z) :
    relativeHomologyMap ℚ (2 * d)
      (singletonFibrePairMap (TopCat.ofHom (Point.continuousMap f))
        (Point.map j z) (Point.map f (Point.map j z)) hf)
      (oX.generator (Point.map j z)) = oY.generator (Point.map f (Point.map j z)) := by
  let E := localChart A d z
  have hz := mem_localChart_source A d z
  let hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  let hk := HodgeLean.Foundations.ComplexTopology.openImmersion_points (j ≫ f)
  have hmaps : Point.map (j ≫ f) = (fun w => Point.map f (Point.map j w)) :=
    funext (Point.map_comp_apply j f)
  have hk' : IsOpenEmbedding (fun w => Point.map f (Point.map j w)) := by
    rw [← hmaps]
    exact hk
  have hX := hnX (Point.map j z) (E.lift_openEmbedding hj) ⟨z, hz, rfl⟩
    (immersion_localChart_coordinates_holomorphic A X j d z)
  have hY := hnY (Point.map (j ≫ f) z) (E.lift_openEmbedding hk) ⟨z, hz, rfl⟩
    (immersion_localChart_coordinates_holomorphic A Y (j ≫ f) d z)
  simp only [hmaps] at hY
  have hc := singletonFibre_map_lifted_chart_class
    (U := TopCat.of (ComplexPoint A))
    (TopCat.ofHom (Point.continuousMap f)) (Point.map j) hj hk' z hf d E hz
  rw [hX]
  exact hc.trans hY.symm

#print axioms singletonFibre_map_complex_generators
end HodgeLean.Foundations.QuotientDuality
