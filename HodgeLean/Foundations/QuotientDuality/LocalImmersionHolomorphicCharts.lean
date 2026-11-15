import HodgeLean.Foundations.QuotientDuality.LocalImmersionEvaluation
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis

/-! Smooth charts transported by algebraic open immersions have holomorphic coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem immersion_localChart_coordinates_holomorphic
    (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : ComplexPoint X) (i : Fin d) :
    (f4_analytification Y).IsHolFun
      (fun y : ((localChart X d x).lift_openEmbedding
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points j)).source =>
        (localChart X d x).lift_openEmbedding
          (HodgeLean.Foundations.ComplexTopology.openImmersion_points j) y i) := by
  let D := localEtaleCoordinates X d x
  let E := localChart X d x
  let hj := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  let V := D.ambientCoordinateOpen
  let t := D.ambientCoordinateSection i
  have hs : (E.lift_openEmbedding hj).source ⊆
      (Point.overOpen (j.left ''ᵁ V) : Set (ComplexPoint Y)) := by
    rintro y ⟨z, hz, rfl⟩
    have hm := mem_coordinateNeighborhood_of_mem_localChart_source X d x z hz
    have hv : z.underlying ∈ V := by
      simpa only [V, D, LocalEtaleCoordinates.ambientCoordinateOpen,
        Scheme.Opens.ι_image_top, Point.overOpen, Set.mem_setOf_eq] using hm
    change j.left z.underlying ∈ j.left ''ᵁ V
    exact ⟨z.underlying, hv, rfl⟩
  have hh := anrem_isHolFun_restrict (f4_analytification Y) hs
    (f4_isHolFun_evaluate Y (j.left ''ᵁ V) ((j.left.appIso V).inv t))
  have heq : (fun y : (E.lift_openEmbedding hj).source =>
      E.lift_openEmbedding hj y i) =
      (fun y : (E.lift_openEmbedding hj).source =>
        Point.evaluate (j.left ''ᵁ V) ((j.left.appIso V).inv t) y.val) := by
    funext y
    obtain ⟨z, hz, he⟩ := y.property
    have hy : y.val = Point.map j z := he.symm
    simp only [hy]
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply, evaluate_openImmersion]
    exact localChart_apply_component_eq_evaluate X d x z hz i
  change (f4_analytification Y).IsHolFun
    (fun y : (E.lift_openEmbedding hj).source => E.lift_openEmbedding hj y i)
  rw [heq]
  exact hh

#print axioms immersion_localChart_coordinates_holomorphic
end HodgeLean.Foundations.QuotientDuality
