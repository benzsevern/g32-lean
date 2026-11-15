import HodgeLean.Foundations.QuotientDuality.LocalHolomorphicCharts
import HodgeLean.Foundations.QuotientDuality.LocalChartEmbedding

/-! Smooth open-subscheme charts have holomorphic ambient coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem open_localChart_coordinates_holomorphic (X : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) (d : ℕ) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (x : ComplexPoint (openScheme X U)) (i : Fin d) :
    (f4_analytification X).IsHolFun
      (fun y : ((localChart (openScheme X U) d x).lift_openEmbedding
        (isOpenEmbedding_map_open X U)).source =>
        (localChart (openScheme X U) d x).lift_openEmbedding
          (isOpenEmbedding_map_open X U) y i) := by
  let Y := openScheme X U
  let D := localEtaleCoordinates Y d x
  let e := localChart Y d x
  let j := Point.map (openInclusion X U)
  let hj := isOpenEmbedding_map_open X U
  let V := D.ambientCoordinateOpen
  let t := D.ambientCoordinateSection i
  have hs : (e.lift_openEmbedding hj).source ⊆
      (Point.overOpen (U.ι ''ᵁ V) : Set (ComplexPoint X)) := by
    rintro y ⟨z, hz, rfl⟩
    have hm := mem_coordinateNeighborhood_of_mem_localChart_source Y d x z hz
    have hv : z ∈ Point.overOpen V := by
      simpa only [V, D, LocalEtaleCoordinates.ambientCoordinateOpen,
        Scheme.Opens.ι_image_top] using hm
    simpa [j, Point.overOpen] using hv
  have hh := anrem_isHolFun_restrict (f4_analytification X) hs
    (f4_isHolFun_evaluate X (U.ι ''ᵁ V) ((U.ι.appIso V).inv t))
  have heq : (fun y : (e.lift_openEmbedding hj).source =>
      e.lift_openEmbedding hj y i) =
      (fun y : (e.lift_openEmbedding hj).source =>
        Point.evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) y.val) := by
    funext y
    obtain ⟨z, hz, he⟩ := y.property
    have hy : y.val = j z := he.symm
    simp only [hy]
    change e.lift_openEmbedding hj (Point.map (openInclusion X U) z) i = _
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rw [evaluate_openEquiv]
    exact localChart_apply_component_eq_evaluate Y d x z hz i
  change (f4_analytification X).IsHolFun
    (fun y : (e.lift_openEmbedding hj).source => e.lift_openEmbedding hj y i)
  rw [heq]
  exact hh

#print axioms open_localChart_coordinates_holomorphic
end HodgeLean.Foundations.QuotientDuality
