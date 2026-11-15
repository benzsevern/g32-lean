import HodgeLean.Foundations.TubularEuler.AffineConormalSectionFibreHelpers

/-! # Original affine ideal elements under scalar extension of section coordinates

The original section equivalence and the specified point scalar map give the tensor coordinates.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

theorem affineIdealTensor_sections_value
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    (s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker φ.hom))).hom
      ((ModuleCat.extendScalars (φ ≫ ψ).hom).map
        (s2e_affine_ideal_sections_equiv R S φ).toModuleIso.hom
        ((1 : ℂ) ⊗ₜ[R, (φ ≫ ψ).hom] (s2e_affine_ideal_sections_equiv R S φ).symm u)) =
      (1 : ℂ) ⊗ₜ[R] u := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  rw [ModuleCat.ExtendScalars.map_tmul]
  change (1 : ℂ) ⊗ₜ[R]
    ((s2e_affine_ideal_sections_equiv R S φ) ((s2e_affine_ideal_sections_equiv R S φ).symm u)) = _
  rw [LinearEquiv.apply_symm_apply]

theorem affineIdealSection_original_tensor_value
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    let M := Conormal.idealModule (Spec.map φ)
    letI : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
    let s := affineIdealModuleSection R S φ u
    let t := (affineModuleFibreIso R (φ ≫ ψ) M).hom
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).app M ≪≫
          (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).app M).hom)
        (i1_module_pointValue ((Scheme.Modules.pullback (Spec.map φ)).obj M)
          (i1_module_sectionPullback (Spec.map φ) M s) (Spec.map ψ)))
    (s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker φ.hom))).hom
      ((ModuleCat.extendScalars (φ ≫ ψ).hom).map
        (s2e_affine_ideal_sections_equiv R S φ).toModuleIso.hom t) =
      (1 : ℂ) ⊗ₜ[R] u := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  let M := Conormal.idealModule (Spec.map φ)
  letI : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
  have h := affineIdealSection_composite_tensor_value R S φ ψ u
  have ht := congrArg (fun t : (ModuleCat.extendScalars (φ ≫ ψ).hom).obj
      ((moduleSpecΓFunctor (R := R)).obj M) =>
    (s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker φ.hom))).hom
      ((ModuleCat.extendScalars (φ ≫ ψ).hom).map
        (s2e_affine_ideal_sections_equiv R S φ).toModuleIso.hom t)) h
  exact ht.trans (affineIdealTensor_sections_value R S φ ψ u)

theorem affineIdealSection_original_cotangent_value
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    let M := Conormal.idealModule (Spec.map φ)
    letI : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
    let s := affineIdealModuleSection R S φ u
    let t := (affineModuleFibreIso R (φ ≫ ψ) M).hom
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).app M ≪≫
          (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).app M).hom)
        (i1_module_pointValue ((Scheme.Modules.pullback (Spec.map φ)).obj M)
          (i1_module_sectionPullback (Spec.map φ) M s) (Spec.map ψ)))
    conormalFibreTensorFromIdeal (RingHom.ker φ.hom)
      ((s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker φ.hom))).hom
        ((ModuleCat.extendScalars (φ ≫ ψ).hom).map
          (s2e_affine_ideal_sections_equiv R S φ).toModuleIso.hom t)) =
      (1 : ℂ) ⊗ₜ[R] (RingHom.ker φ.hom).toCotangent u := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  have h := congrArg (conormalFibreTensorFromIdeal (C := ℂ) (RingHom.ker φ.hom))
    (affineIdealSection_original_tensor_value R S φ ψ u)
  exact h.trans (conormalFibreTensorFromIdeal_tmul (RingHom.ker φ.hom) 1 u)

#print axioms affineIdealSection_original_cotangent_value

#print axioms affineIdealSection_original_tensor_value

#print axioms affineIdealTensor_sections_value

end HodgeLean.Foundations.TubularEuler
