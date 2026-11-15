import Mathlib.AlgebraicGeometry.Normalization

/-! # Affine charts of the retained relative normalization
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- On an affine open, the actual relative normalization is the spectrum of the integral closure, with its specified projection.
Source: Stacks Project, tag 035H; Mathlib, Scheme.Hom.normalizationObjIso and Scheme.Hom.fromNormalization_app. -/
theorem s2v_i2a_affine_normalization_square
    {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    ∃ e : pullback f.fromNormalization U.ι ≅
        Spec ↧(integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)),
      pullback.snd f.fromNormalization U.ι ≫ U.toSpecΓ =
        e.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)))) := by
  letI := (f.app U).hom.toAlgebra
  let E := (pullbackRestrictIsoRestrict f.fromNormalization U) ≪≫
    (hU.preimage f.fromNormalization).isoSpec ≪≫
    Scheme.Spec.mapIso (f.normalizationObjIso hU).symm.op
  refine ⟨E, ?_⟩
  dsimp only [E, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
  rw [IsAffineOpen.isoSpec_hom]
  change _ = (pullbackRestrictIsoRestrict f.fromNormalization U).hom ≫
    (f.fromNormalization ⁻¹ᵁ U).toSpecΓ ≫
      Spec.map (f.normalizationObjIso hU).inv ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))))
  rw [← Spec.map_comp]
  rw [← f.fromNormalization_app hU]
  rw [Scheme.Opens.toSpecΓ_naturality]
  rw [pullbackRestrictIsoRestrict_hom_morphismRestrict_assoc]

/-- If the field point lies in an affine open, its normalization chart uses that same field as its ambient algebra.
Source: Stacks Project, tag 035H; Mathlib, AlgEquiv.mapIntegralClosure and Scheme.ΓSpecIso. -/
theorem s2v_i2a_field_normalization_square
    {K : Type*} [Field K] {Y : Scheme}
    (f : Spec ↧K ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (U : Y.Opens) (hU : IsAffineOpen U) (hpre : f ⁻¹ᵁ U = ⊤) :
    let eS : Γ(Spec ↧K, f ⁻¹ᵁ U) ≅ ↧K :=
      (Spec ↧K).presheaf.mapIso (eqToIso hpre.symm).op ≪≫ Scheme.ΓSpecIso ↧K
    let φ : Γ(Y, U) →+* K := (f.app U ≫ eS.hom).hom
    letI := φ.toAlgebra
    ∃ e : pullback f.fromNormalization U.ι ≅
        Spec ↧(integralClosure Γ(Y, U) K),
      pullback.snd f.fromNormalization U.ι ≫ U.toSpecΓ =
        e.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) K))) := by
  let eS : Γ(Spec ↧K, f ⁻¹ᵁ U) ≅ ↧K :=
    (Spec ↧K).presheaf.mapIso (eqToIso hpre.symm).op ≪≫ Scheme.ΓSpecIso ↧K
  let φ : Γ(Y, U) →+* K := (f.app U ≫ eS.hom).hom
  letI := φ.toAlgebra
  letI := (f.app U).hom.toAlgebra
  let E : Γ(Spec ↧K, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, U)] K :=
    { eS.commRingCatIsoToRingEquiv with commutes' r := rfl }
  let EI := E.mapIntegralClosure
  obtain ⟨eN, heN⟩ := s2v_i2a_affine_normalization_square f U hU
  refine ⟨eN ≪≫ Scheme.Spec.mapIso EI.toRingEquiv.symm.toCommRingCatIso.op, ?_⟩
  change _ = eN.hom ≫ Spec.map (CommRingCat.ofHom EI.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) K)))
  rw [← Spec.map_comp]
  have H : CommRingCat.ofHom (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) K)) ≫
      CommRingCat.ofHom EI.symm.toRingHom =
      CommRingCat.ofHom (algebraMap Γ(Y, U)
        (integralClosure Γ(Y, U) Γ(Spec ↧K, f ⁻¹ᵁ U))) := by
    ext r
    exact congrArg Subtype.val (EI.symm.commutes r)
  rw [H]
  exact heN

end HodgeLean.Foundations.Program
