import HodgeLean.Foundations.TubularEuler.ZeroDimChartHelpers
import HodgeLean.Foundations.BundleThom.ImmersionDefs
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Proofs

/-! # Ambient openness in transverse rank zero

The given factorization retains the same complex-point inclusion into the ambient scheme.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

theorem zeroRankImmersion_points_isOpenEmbedding
    {Q W : Over (Spec ↧ℂ)} (ι : Q ⟶ W)
    {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
    (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
    [SmoothOfRelativeDimension 0 (v ≫ W.hom)] :
    IsOpenEmbedding (Point.map ι : ComplexPoint Q → ComplexPoint W) := by
  let L := i1_smoothLift ι v j hj
  let I : Over.mk (v ≫ W.hom) ⟶ W := Over.homMk v rfl
  letI : IsClosedImmersion L.left := ‹IsClosedImmersion j›
  letI : IsOpenImmersion I.left := ‹IsOpenImmersion v›
  letI : SmoothOfRelativeDimension 0 (Over.mk (v ≫ W.hom)).hom :=
    ‹SmoothOfRelativeDimension 0 (v ≫ W.hom)›
  letI : DiscreteTopology (ComplexPoint (Over.mk (v ≫ W.hom))) :=
    complexPoint_discreteTopology_of_smooth_zero _
  have hL : IsOpenEmbedding (Point.map L) :=
    IsOpenEmbedding.of_isEmbedding_isOpenMap
      (ComplexPoint.isEmbedding_map_of_closedImmersion L) (fun _ _ => isOpen_discrete _)
  have hI := ComplexTopology.openImmersion_points_aux I
  have hLI : L ≫ I = ι := Over.OverMorphism.ext hj
  have he : Point.map ι = Point.map I ∘ Point.map L := by
    funext x
    rw [Function.comp_apply, ← Point.map_comp_apply, hLI]
  rw [he]
  exact hI.comp hL

#print axioms zeroRankImmersion_points_isOpenEmbedding

end HodgeLean.Foundations.TubularEuler
