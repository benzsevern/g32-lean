import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationBaseHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationOpenHelpers

/-! # Comparison of the actual covers over isomorphic open bases -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Compatible isomorphic open bases give an isomorphism between the actual
restricted normalization covers and carry their retained generic source maps. -/
theorem s2e_c1_normalization_open_base_iso {T X Y : Scheme}
    (f : T ⟶ X) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (U : X.Opens) (V : Y.Opens) (e : U.toScheme ≅ V.toScheme)
    (fU : T ⟶ U.toScheme) (gV : T ⟶ V.toScheme)
    [QuasiCompact fU] [QuasiSeparated fU] [QuasiCompact gV] [QuasiSeparated gV]
    (hf : fU ≫ U.ι = f) (hg : gV ≫ V.ι = g) (he : fU ≫ e.hom = gV) :
    ∃ (E : (f.fromNormalization ⁻¹ᵁ U).toScheme ≅ (g.fromNormalization ⁻¹ᵁ V).toScheme)
      (u : T ⟶ (f.fromNormalization ⁻¹ᵁ U).toScheme)
      (v : T ⟶ (g.fromNormalization ⁻¹ᵁ V).toScheme),
      IsDominant u ∧ E.hom ≫ (g.fromNormalization ∣_ V) = (f.fromNormalization ∣_ U) ≫ e.hom ∧
      u ≫ (f.fromNormalization ⁻¹ᵁ U).ι = f.toNormalization ∧
      v ≫ (g.fromNormalization ⁻¹ᵁ V).ι = g.toNormalization ∧ u ≫ E.hom = v := by
  obtain ⟨EL, hEL, hELsrc⟩ := s2e_c1_normalization_corestrict_iso f U fU hf
  obtain ⟨ER, hER, hERsrc⟩ := s2e_c1_normalization_corestrict_iso g V gV hg
  obtain ⟨EM, hEMsrc, hEM⟩ := s2e_c1_normalization_base_iso gV fU e he
  let E := EL.symm ≪≫ EM ≪≫ ER
  let u := fU.toNormalization ≫ EL.hom
  let v := gV.toNormalization ≫ ER.hom
  haveI : IsDominant u := by
    dsimp only [u]
    infer_instance
  refine ⟨E, u, v, inferInstance, ?_, hELsrc, hERsrc, ?_⟩
  · change (EL.inv ≫ EM.hom ≫ ER.hom) ≫ (g.fromNormalization ∣_ V) =
      (f.fromNormalization ∣_ U) ≫ e.hom
    rw [Category.assoc, Category.assoc, hER, hEM, ← Category.assoc,
      ← hEL, EL.inv_hom_id_assoc]
  · change (fU.toNormalization ≫ EL.hom) ≫ (EL.inv ≫ EM.hom ≫ ER.hom) =
      gV.toNormalization ≫ ER.hom
    rw [Category.assoc, EL.hom_inv_id_assoc, ← Category.assoc, hEMsrc]

end HodgeLean.Foundations.Program
