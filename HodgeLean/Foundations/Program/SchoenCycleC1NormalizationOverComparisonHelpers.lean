import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationComparisonHelpers
import HodgeLean.Foundations.Program.SchoenTowerDefs
import HodgeLean.Foundations.Program.SchoenCycleC11EtaleSmoothHelpers

/-! # Open normalization comparisons over the complex base -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The open normalization comparison is an actual complex-base cover
isomorphism over the specified open-base isomorphism. -/
theorem s2e_c1_normalization_open_over_iso {T : Scheme}
    (X Y : Over (Spec ↧ℂ)) (f : T ⟶ X.left) (g : T ⟶ Y.left)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (U : X.left.Opens) (V : Y.left.Opens)
    (e : openScheme X U ≅ openScheme Y V)
    (fU : T ⟶ U.toScheme) (gV : T ⟶ V.toScheme)
    [QuasiCompact fU] [QuasiSeparated fU] [QuasiCompact gV] [QuasiSeparated gV]
    (hf : fU ≫ U.ι = f) (hg : gV ≫ V.ι = g) (he : fU ≫ e.hom.left = gV) :
    ∃ E : openScheme (s2b_normalizationOver X f) (f.fromNormalization ⁻¹ᵁ U) ≅
      openScheme (s2b_normalizationOver Y g) (g.fromNormalization ⁻¹ᵁ V),
      E.hom ≫ s2e_c11_restricted_over_morphism (s2b_normalizationOver Y g) Y
        (s2b_normalizationMap Y g) V =
      s2e_c11_restricted_over_morphism (s2b_normalizationOver X f) X
        (s2b_normalizationMap X f) U ≫ e.hom := by
  obtain ⟨E, _, _, _, hbase, _, _, _⟩ := s2e_c1_normalization_open_base_iso f g U V
    ((Over.forget _).mapIso e) fU gV hf hg he
  let πX := s2e_c11_restricted_over_morphism (s2b_normalizationOver X f) X (s2b_normalizationMap X f) U
  let πY := s2e_c11_restricted_over_morphism (s2b_normalizationOver Y g) Y (s2b_normalizationMap Y g) V
  have hE : E.hom ≫ πY.left = πX.left ≫ e.hom.left := hbase
  have hstr : E.hom ≫ (openScheme (s2b_normalizationOver Y g) (g.fromNormalization ⁻¹ᵁ V)).hom =
      (openScheme (s2b_normalizationOver X f) (f.fromNormalization ⁻¹ᵁ U)).hom := by
    change E.hom ≫ (openScheme (s2b_normalizationOver Y g) ((s2b_normalizationMap Y g).left ⁻¹ᵁ V)).hom =
      (openScheme (s2b_normalizationOver X f) ((s2b_normalizationMap X f).left ⁻¹ᵁ U)).hom
    rw [← Over.w πY, ← Category.assoc, hE, Category.assoc, Over.w e.hom, Over.w πX]
  refine ⟨Over.isoMk E hstr, ?_⟩
  apply Over.OverMorphism.ext
  exact hE

end HodgeLean.Foundations.Program
