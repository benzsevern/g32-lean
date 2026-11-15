import HodgeLean.Foundations.Program.SchoenTowerI2aNormalizationCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An isomorphism of sources over the same base transports relative normalization
and its specified projection.
Source: Mathlib, Scheme.Hom.normalizationDesc and Scheme.Hom.normalization.hom_ext. -/
theorem s2v_i2a_normalization_source_iso
    {X X' Y : Scheme} (f : X ⟶ Y) (g : X' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (e : X ≅ X') (he : e.hom ≫ g = f) :
    ∃ E : f.normalization ≅ g.normalization,
      E.hom ≫ g.fromNormalization = f.fromNormalization := by
  have hei : e.inv ≫ f = g := by rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let a := f.normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
    (by simpa only [Category.assoc, Scheme.Hom.toNormalization_fromNormalization] using he.symm)
  let b := g.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization
    (by simpa only [Category.assoc, Scheme.Hom.toNormalization_fromNormalization] using hei.symm)
  have ha : a ≫ g.fromNormalization = f.fromNormalization := by
    exact Scheme.Hom.normalizationDesc_comp ..
  have hb : b ≫ f.fromNormalization = g.fromNormalization := by
    exact Scheme.Hom.normalizationDesc_comp ..
  have hat : f.toNormalization ≫ a = e.hom ≫ g.toNormalization := by
    exact Scheme.Hom.toNormalization_normalizationDesc ..
  have hbt : g.toNormalization ≫ b = e.inv ≫ f.toNormalization := by
    exact Scheme.Hom.toNormalization_normalizationDesc ..
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
    · rw [← Category.assoc, hat, Category.assoc, hbt, ← Category.assoc,
        e.hom_inv_id, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, hb, ha]
    · exact Category.id_comp _
  · apply Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
    · rw [← Category.assoc, hbt, Category.assoc, hat, ← Category.assoc,
        e.inv_hom_id, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, ha, hb]
    · exact Category.id_comp _

end HodgeLean.Foundations.Program
