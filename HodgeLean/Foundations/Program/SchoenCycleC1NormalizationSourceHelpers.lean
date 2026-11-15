import Mathlib.AlgebraicGeometry.Normalization

/-! # Change of source in relative normalization -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An isomorphism of the specified sources induces an isomorphism of the
actual relative normalizations, retaining both structural identities. -/
theorem s2e_c1_normalization_source_iso {X X' Y : Scheme}
    (f : X ⟶ Y) (g : X' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (e : X' ≅ X) (he : e.hom ≫ f = g) :
    ∃ E : g.normalization ≅ f.normalization,
      g.toNormalization ≫ E.hom = e.hom ≫ f.toNormalization ∧
      E.hom ≫ f.fromNormalization = g.fromNormalization := by
  have ha : g = (e.hom ≫ f.toNormalization) ≫ f.fromNormalization := by
    rw [Category.assoc, f.toNormalization_fromNormalization]
    exact he.symm
  have hb : f = (e.inv ≫ g.toNormalization) ≫ g.fromNormalization := by
    rw [Category.assoc, g.toNormalization_fromNormalization, ← he, e.inv_hom_id_assoc]
  let a := g.normalizationDesc (e.hom ≫ f.toNormalization) f.fromNormalization ha
  let b := f.normalizationDesc (e.inv ≫ g.toNormalization) g.fromNormalization hb
  have ha1 : g.toNormalization ≫ a = e.hom ≫ f.toNormalization :=
    g.toNormalization_normalizationDesc _ _ ha
  have hb1 : f.toNormalization ≫ b = e.inv ≫ g.toNormalization :=
    f.toNormalization_normalizationDesc _ _ hb
  have ha2 : a ≫ f.fromNormalization = g.fromNormalization := g.normalizationDesc_comp _ _ ha
  have hb2 : b ≫ g.fromNormalization = f.fromNormalization := f.normalizationDesc_comp _ _ hb
  have hab : a ≫ b = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext (f := g) _ _ g.fromNormalization
    · rw [← Category.assoc, ha1, Category.assoc, hb1, e.hom_inv_id_assoc, Category.comp_id]
    · rw [Category.assoc, hb2, ha2]
    · exact Category.id_comp _
  have hba : b ≫ a = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext (f := f) _ _ f.fromNormalization
    · rw [← Category.assoc, hb1, Category.assoc, ha1, e.inv_hom_id_assoc, Category.comp_id]
    · rw [Category.assoc, ha2, hb2]
    · exact Category.id_comp _
  exact ⟨⟨a, b, hab, hba⟩, ha1, ha2⟩

end HodgeLean.Foundations.Program
