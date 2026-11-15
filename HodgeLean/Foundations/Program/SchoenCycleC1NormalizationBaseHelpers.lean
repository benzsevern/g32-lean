import Mathlib.AlgebraicGeometry.Normalization

/-! # Transport of relative normalization along a base isomorphism -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An isomorphism of bases compatible with the specified generic maps
identifies their actual relative normalizations. -/
theorem s2e_c1_normalization_base_iso {T X Y : Scheme}
    (f : T ⟶ Y) (g : T ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (e : X ≅ Y) (he : g ≫ e.hom = f) :
    ∃ E : g.normalization ≅ f.normalization,
      g.toNormalization ≫ E.hom = f.toNormalization ∧
      E.hom ≫ f.fromNormalization = g.fromNormalization ≫ e.hom := by
  have ha : g = f.toNormalization ≫ (f.fromNormalization ≫ e.inv) := by
    rw [← Category.assoc, f.toNormalization_fromNormalization, ← he,
      Category.assoc, e.hom_inv_id, Category.comp_id]
  have hb : f = g.toNormalization ≫ (g.fromNormalization ≫ e.hom) := by
    rw [← Category.assoc, g.toNormalization_fromNormalization, he]
  let a := g.normalizationDesc f.toNormalization (f.fromNormalization ≫ e.inv) ha
  let b := f.normalizationDesc g.toNormalization (g.fromNormalization ≫ e.hom) hb
  have ha1 : g.toNormalization ≫ a = f.toNormalization :=
    g.toNormalization_normalizationDesc _ _ ha
  have hb1 : f.toNormalization ≫ b = g.toNormalization :=
    f.toNormalization_normalizationDesc _ _ hb
  have ha2 : a ≫ f.fromNormalization ≫ e.inv = g.fromNormalization :=
    g.normalizationDesc_comp _ _ ha
  have hb2 : b ≫ g.fromNormalization ≫ e.hom = f.fromNormalization :=
    f.normalizationDesc_comp _ _ hb
  have ha3 : a ≫ f.fromNormalization = g.fromNormalization ≫ e.hom := by
    rw [← ha2, Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hb3 : b ≫ g.fromNormalization = f.fromNormalization ≫ e.inv := by
    rw [← hb2, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hab : a ≫ b = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext (f := g) _ _ g.fromNormalization
    · rw [← Category.assoc, ha1, hb1, Category.comp_id]
    · rw [Category.assoc, hb3, ← Category.assoc, ha3,
        Category.assoc, e.hom_inv_id, Category.comp_id]
    · exact Category.id_comp _
  have hba : b ≫ a = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext (f := f) _ _ f.fromNormalization
    · rw [← Category.assoc, hb1, ha1, Category.comp_id]
    · rw [Category.assoc, ha3, ← Category.assoc, hb3,
        Category.assoc, e.inv_hom_id, Category.comp_id]
    · exact Category.id_comp _
  exact ⟨⟨a, b, hab, hba⟩, ha1, ha3⟩

end HodgeLean.Foundations.Program
