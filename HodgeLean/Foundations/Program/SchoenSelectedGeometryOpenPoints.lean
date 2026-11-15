import HodgeLean.Foundations.Program.SchoenSelectedGeometrySpecSmoothPoint
import HodgeLean.Foundations.Program.SchoenSelectedGeometryOpenNonisolated

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
namespace HodgeLean.Foundations.Program

/-- An open immersion induces an open embedding of complex point spaces. -/
theorem s0_open_immersion_complex_embedding
    {X Y : Over (Spec ↧ℂ)} (i : X ⟶ Y) [IsOpenImmersion i.left] :
    IsOpenEmbedding (Point.map i) := by
  let U := i.left.opensRange
  have hr : Set.range i.left = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  let E := IsOpenImmersion.isoOfRangeEq i.left U.ι hr
  have hE : E.hom ≫ U.ι = i.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let e : X ≅ openScheme Y U := Over.isoMk E (by
    change E.hom ≫ (U.ι ≫ Y.hom) = X.hom
    rw [← Category.assoc, hE, Over.w i])
  have heq : i = e.hom ≫ openInclusion Y U := Over.OverMorphism.ext hE.symm
  rw [heq]
  exact (isOpenEmbedding_map_open Y U).comp (Point.isoMapHomeomorph e).isOpenEmbedding

#print axioms s0_open_immersion_complex_embedding
/-- A complex point in the image of an open immersion lifts to its source. -/
theorem s0_open_immersion_lift_complex_point
    {X Y : Over (Spec ↧ℂ)} (i : X ⟶ Y) [IsOpenImmersion i.left]
    (z : ComplexPoint Y) (hz : z.underlying ∈ Set.range i.left) :
    ∃ w : ComplexPoint X, Point.map i w = z := by
  have hr : Set.range z.left ⊆ Set.range i.left := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := Spec ↧ℂ) _ _
    subst p
    exact hz
  let l := IsOpenImmersion.lift i.left z.left hr
  have hl : l ≫ i.left = z.left := IsOpenImmersion.lift_fac _ _ _
  let w : ComplexPoint X := Over.homMk l (by
    rw [← Over.w i, ← Category.assoc, hl, Over.w z])
  exact ⟨w, Over.OverMorphism.ext hl⟩

#print axioms s0_open_immersion_lift_complex_point
end HodgeLean.Foundations.Program
