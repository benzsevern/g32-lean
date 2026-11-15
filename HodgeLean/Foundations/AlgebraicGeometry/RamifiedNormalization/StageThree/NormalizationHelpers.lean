import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.DeckHelpers
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageTwo.ChartHelpers

/-! # Normalization transport through scheme isomorphisms
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageThree

variable {X Y X' Y' : Scheme}

def normalizationCongr (f : X ⟶ Y) (g : X' ⟶ Y')
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (eX : X ≅ X') (eY : Y ≅ Y') (h : eX.hom ≫ g = f ≫ eY.hom) :
    f.normalization ≅ g.normalization := by
  let a := f.normalizationDesc (eX.hom ≫ g.toNormalization)
    (g.fromNormalization ≫ eY.inv) (by
      simp only [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc]
      rw [← Category.assoc, h, Category.assoc, eY.hom_inv_id, Category.comp_id])
  have hi : eX.inv ≫ f = g ≫ eY.inv := by
    apply (cancel_epi eX.hom).mp
    simp only [← Category.assoc, eX.hom_inv_id, Category.id_comp]
    rw [h, Category.assoc, eY.hom_inv_id, Category.comp_id]
  let b := g.normalizationDesc (eX.inv ≫ f.toNormalization)
    (f.fromNormalization ≫ eY.hom) (by
      simp only [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc]
      rw [← Category.assoc, hi, Category.assoc, eY.inv_hom_id, Category.comp_id])
  have ha : a ≫ g.fromNormalization = f.fromNormalization ≫ eY.hom := by
    apply (cancel_mono eY.inv).mp
    simp only [Category.assoc, eY.hom_inv_id, Category.comp_id]
    exact f.normalizationDesc_comp _ _ _
  have hb : b ≫ f.fromNormalization = g.fromNormalization ≫ eY.inv := by
    apply (cancel_mono eY.hom).mp
    simp only [Category.assoc, eY.inv_hom_id, Category.comp_id]
    exact g.normalizationDesc_comp _ _ _
  refine ⟨a, b, ?_, ?_⟩
  · apply Scheme.Hom.normalization.hom_ext (f := f) _ _ f.fromNormalization
    · simp [a, b, Category.assoc]
    · rw [Category.assoc, hb, ← Category.assoc, ha]
      simp only [Category.assoc, eY.hom_inv_id, Category.comp_id]
    · exact Category.id_comp _
  · apply Scheme.Hom.normalization.hom_ext (f := g) _ _ g.fromNormalization
    · simp [a, b, Category.assoc]
    · rw [Category.assoc, ha, ← Category.assoc, hb]
      simp only [Category.assoc, eY.inv_hom_id, Category.comp_id]
    · exact Category.id_comp _

theorem normalizationCongr_point (f : X ⟶ Y) (g : X' ⟶ Y')
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (eX : X ≅ X') (eY : Y ≅ Y') (h : eX.hom ≫ g = f ≫ eY.hom) :
    f.toNormalization ≫ (normalizationCongr f g eX eY h).hom =
      eX.hom ≫ g.toNormalization := by
  simp [normalizationCongr]

theorem normalizationCongr_base (f : X ⟶ Y) (g : X' ⟶ Y')
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (eX : X ≅ X') (eY : Y ≅ Y') (h : eX.hom ≫ g = f ≫ eY.hom) :
    (normalizationCongr f g eX eY h).hom ≫ g.fromNormalization =
      f.fromNormalization ≫ eY.hom := by
  apply (cancel_mono eY.inv).mp
  simp only [Category.assoc, eY.hom_inv_id, Category.comp_id]
  dsimp only [normalizationCongr]
  apply Scheme.Hom.normalizationDesc_comp

end AlgebraicGeometry.RamifiedNormalization.StageThree
