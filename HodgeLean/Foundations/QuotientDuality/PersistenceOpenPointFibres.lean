import HodgeLean.Foundations.QuotientDuality.PersistenceNormalizationOffCentre
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! Complex-point fibres from the specified open comparison. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_unique_complex_fibre_of_open_iso
    {X Y : Over (Spec ↧ℂ)} (w : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens)
    (hU : U = w.left ⁻¹ᵁ V) (E : U.toScheme ≅ V.toScheme)
    (hE : E.hom ≫ V.ι = U.ι ≫ w.left)
    (y : ComplexPoint Y) (hy : y ∈ Point.overOpen V) :
    ∃! x : ComplexPoint X, Point.map w x = y := by
  have hstr : E.hom ≫ (V.ι ≫ Y.hom) = U.ι ≫ X.hom := by
    rw [← Category.assoc, hE, Category.assoc, Over.w w]
  let e : openScheme X U ≅ openScheme Y V := Over.isoMk E hstr
  have hpoint (z : ComplexPoint (openScheme X U)) :
      (openEquiv Y V (Point.map e.hom z)).val =
        Point.map w (openEquiv X U z).val := by
    apply Over.OverMorphism.ext
    change (z.left ≫ E.hom) ≫ V.ι = (z.left ≫ U.ι) ≫ w.left
    rw [Category.assoc, hE, Category.assoc]
  let H := (openEquiv X U).symm.trans
    ((Point.isoMapHomeomorph e).toEquiv.trans (openEquiv Y V))
  have hH (z : {x : ComplexPoint X // x ∈ Point.overOpen U}) :
      (H z).val = Point.map w z.val := by
    exact (hpoint ((openEquiv X U).symm z)).trans
      (congrArg (fun t => Point.map w t.val) ((openEquiv X U).apply_symm_apply z))
  let u := H.symm ⟨y, hy⟩
  have hu : H u = ⟨y, hy⟩ := H.apply_symm_apply ⟨y, hy⟩
  refine ⟨u.val, (hH u).symm.trans (congrArg Subtype.val hu), ?_⟩
  intro x hx
  have hxU : x ∈ Point.overOpen U := by
    rw [hU]
    rw [← Point.mem_overOpen_map_iff w x V, hx]
    exact hy
  have heq : H ⟨x, hxU⟩ = H u := by
    rw [hu]
    apply Subtype.ext
    exact (hH ⟨x, hxU⟩).trans hx
  exact congrArg Subtype.val (H.injective heq)

end HodgeLean.Foundations.QuotientDuality
