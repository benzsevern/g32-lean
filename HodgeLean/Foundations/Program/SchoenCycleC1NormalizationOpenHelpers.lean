import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationSourceHelpers

/-! # Actual normalization over an open base -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Corestricting the specified source to an open base identifies its
normalization with the actual open part of the original normalization. -/
theorem s2e_c1_normalization_corestrict_iso {T Y : Scheme}
    (f : T ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (U : Y.Opens) (g : T ⟶ U.toScheme)
    [QuasiCompact g] [QuasiSeparated g] (hg : g ≫ U.ι = f) :
    ∃ E : g.normalization ≅ (f.fromNormalization ⁻¹ᵁ U).toScheme,
      E.hom ≫ (f.fromNormalization ∣_ U) = g.fromNormalization ∧
      g.toNormalization ≫ E.hom ≫ (f.fromNormalization ⁻¹ᵁ U).ι = f.toNormalization := by
  let v : T ⟶ pullback f U.ι := pullback.lift (𝟙 T) g (by rw [Category.id_comp, hg])
  have hv1 : v ≫ pullback.fst f U.ι = 𝟙 T := pullback.lift_fst _ _ _
  have hv2 : v ≫ pullback.snd f U.ι = g := pullback.lift_snd _ _ _
  have hfg : pullback.fst f U.ι ≫ g = pullback.snd f U.ι := by
    rw [← cancel_mono U.ι, Category.assoc, hg, pullback.condition]
  let e : T ≅ pullback f U.ι :=
    { hom := v
      inv := pullback.fst f U.ι
      hom_inv_id := hv1
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, hv1, Category.comp_id, Category.id_comp]
        · rw [Category.assoc, hv2, hfg, Category.id_comp] }
  obtain ⟨E₀, hE₀, hbase⟩ :=
    s2e_c1_normalization_source_iso (pullback.snd f U.ι) g e hv2
  let E₁ := asIso (f.normalizationPullback U.ι)
  let E₂ := pullbackRestrictIsoRestrict f.fromNormalization U
  let E := E₀ ≪≫ E₁ ≪≫ E₂
  refine ⟨E, ?_, ?_⟩
  · change (E₀.hom ≫ f.normalizationPullback U.ι ≫ E₂.hom) ≫
      (f.fromNormalization ∣_ U) = g.fromNormalization
    rw [Category.assoc, Category.assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict,
      f.normalizationPullback_snd, hbase]
  · change g.toNormalization ≫ (E₀.hom ≫ f.normalizationPullback U.ι ≫ E₂.hom) ≫
      (f.fromNormalization ⁻¹ᵁ U).ι = f.toNormalization
    rw [Category.assoc, Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
      ← Category.assoc, hE₀, Category.assoc,
      f.toNormalization_normalizationPullback_fst, ← Category.assoc, hv1, Category.id_comp]

end HodgeLean.Foundations.Program
