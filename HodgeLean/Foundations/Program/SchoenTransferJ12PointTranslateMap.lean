import HodgeLean.Foundations.Program.SchoenTransferJ12PointTranslation

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Translating an actual map to an abelian variety by a complex point preserves every pullback degree.
Source: functoriality and the actual point translation action on abelian cohomology. -/
theorem s4_selected_point_translate_map_pullback
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (e : ComplexPoint A) (f : Y ⟶ A) (n : ℕ) :
    homPullback (((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) * f) n =
      homPullback f n := by
  let cA : A ⟶ Over.mk (𝟙 (Spec ↧ℂ)) := Over.homMk A.hom
  let cY : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ)) := Over.homMk Y.hom
  have hc : f ≫ cA = cY := by
    apply Over.OverMorphism.ext
    exact Over.w f
  have hmap : f ≫ ((cA ≫ e) * 𝟙 A) = (cY ≫ e) * f := by
    rw [MonObj.comp_mul, ← Category.assoc, hc, Category.comp_id]
  rw [← hmap, spec_homPullback_comp, s4_selected_point_translation_pullback A e n,
    LinearMap.comp_id]

#print axioms s4_selected_point_translate_map_pullback
end HodgeLean.Foundations.Program
