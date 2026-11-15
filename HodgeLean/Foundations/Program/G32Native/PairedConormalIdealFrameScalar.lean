import HodgeLean.Foundations.Program.G32Native.PairedConormalIdealCoefficients
import HodgeLean.Foundations.Curves.Picard.LineBundles.UnitComparisonForms

/-! # Literal scalar coefficients in actual ideal section frames -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles

/-- The actual local ideal-section map followed by any ideal row has the
literal affine row coefficient as its global unit scalar. -/
theorem conormal_ideal_restrict_frame_scalar {X : Scheme} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U)
    (φ : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ((localSectionHom (idealModule I) U.1 (idealSection I U a ha)) ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom).val.app (Opposite.op ⊤)
          (1 : Γ(U.1.toScheme, ⊤)) =
      U.1.topIso.inv (conormalIdealMapCoefficient I φ U a ha) := by
  change (U.1.ι.appIso ⊤).hom
    (φ.val.app (Opposite.op (U.1.ι ''ᵁ ⊤))
      ((localSectionHom (idealModule I) U.1 (idealSection I U a ha)).val.app
        (Opposite.op ⊤) (1 : Γ(U.1.toScheme, ⊤)))) = _
  rw [localSectionHom_app, map_one, one_smul]
  have hn := PresheafOfModules.naturality_apply φ.val
    (homOfLE (U.1.ι_image_le ⊤)).op (idealSection I U a ha)
  change φ.val.app (Opposite.op (U.1.ι ''ᵁ ⊤))
    ((idealModule I).presheaf.map (homOfLE (U.1.ι_image_le ⊤)).op
      (idealSection I U a ha)) =
    X.presheaf.map (homOfLE (U.1.ι_image_le ⊤)).op
      (φ.val.app (Opposite.op U.1) (idealSection I U a ha)) at hn
  rw [hn]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom, CommRingCat.id_apply]
  rfl

/-- The canonical restriction-to-pullback and unit comparisons retain the literal ideal-row scalar. -/
theorem conormal_ideal_pullback_frame_scalar {X : Scheme} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : Γ(X, U.1)) (ha : a ∈ I.ideal U)
    (φ : idealModule I ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (((localSectionHom (idealModule I) U.1 (idealSection I U a ha)) ≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app (idealModule I)).hom) ≫
        (Scheme.Modules.pullback U.1.ι).map φ ≫ (pullbackUnit U.1.ι).hom).val.app
          (Opposite.op ⊤) (1 : Γ(U.1.toScheme, ⊤)) =
      U.1.topIso.inv (conormalIdealMapCoefficient I φ U a ha) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback U.1.ι
  have hn := e.hom.naturality φ
  have he : ((localSectionHom (idealModule I) U.1 (idealSection I U a ha)) ≫
      (e.app (idealModule I)).hom) ≫ (Scheme.Modules.pullback U.1.ι).map φ ≫
        (pullbackUnit U.1.ι).hom =
      localSectionHom (idealModule I) U.1 (idealSection I U a ha) ≫
        (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom := by
    simp only [Category.assoc]
    erw [← reassoc_of% hn, ← restrictPullback_unit_hom]
  rw [he]
  exact conormal_ideal_restrict_frame_scalar I U a ha φ

end HodgeLean.Foundations.Program.G32Native
