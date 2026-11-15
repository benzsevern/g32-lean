import HodgeLean.Foundations.TubularEuler.AffineConormalSectionHelpers

/-! # Original affine conormal sections in the retained tensor fibre

Specialization of the pulled-back ideal section retains its original ideal element.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution
open HodgeLean.Foundations.BundleThom

theorem moduleSectionPullback_eq_sectionPullback {A B : Scheme.{0}} (f : A ⟶ B)
    (M : B.Modules) (s : SheafOfModules.unit.{0} B.ringCatSheaf ⟶ M) :
    i1_moduleSectionPullback f M s = i1_module_sectionPullback f M s := by
  rfl

def affineConormalSection (R S : CommRingCat.{0}) (φ : R ⟶ S) (u : RingHom.ker φ.hom) :
    SheafOfModules.unit.{0} (Spec S).ringCatSheaf ⟶ Conormal.sheaf (Spec.map φ) :=
  i1_module_sectionPullback (Spec.map φ) (Conormal.idealModule (Spec.map φ))
    (affineIdealModuleSection R S φ u)


theorem modulePointValue_composition_comparison {A B : Scheme.{0}}
    (a : Spec (CommRingCat.of ℂ) ⟶ A) (f : A ⟶ B)
    (b : Spec (CommRingCat.of ℂ) ⟶ B) (h : a ≫ f = b)
    (M : B.Modules) (s : SheafOfModules.unit.{0} B.ringCatSheaf ⟶ M) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      (((Scheme.Modules.pullbackComp a f).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M).hom)
      (i1_module_pointValue ((Scheme.Modules.pullback f).obj M)
        (i1_module_sectionPullback f M s) a) = i1_module_pointValue M s b := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.map_comp, ConcreteCategory.comp_apply]
  rw [i1_module_pointValue_pullback_comp, i1_module_pointValue_congr]

theorem affineModuleFibreIso_composite_section_apply {A : Scheme.{0}}
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (a : Spec (CommRingCat.of ℂ) ⟶ A) (f : A ⟶ Spec R)
    (h : a ≫ f = Spec.map ψ) (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (s : SheafOfModules.unit.{0} (Spec R).ringCatSheaf ⟶ M) :
    (affineModuleFibreIso R ψ M).hom
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (((Scheme.Modules.pullbackComp a f).app M ≪≫
          (Scheme.Modules.pullbackCongr h).app M).hom)
        (i1_module_pointValue ((Scheme.Modules.pullback f).obj M)
          (i1_module_sectionPullback f M s) a)) =
      (1 : ℂ) ⊗ₜ[R, ψ.hom]
        (show (moduleSpecΓFunctor (R := R)).obj M from
          s.val.app (.op ⊤) (1 : Γ(Spec R, ⊤))) := by
  rw [modulePointValue_composition_comparison]
  exact affineModuleFibreIso_section_apply R ψ M s

theorem affineIdealSection_composite_tensor_value
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (u : RingHom.ker φ.hom) :
    let M := Conormal.idealModule (Spec.map φ)
    letI : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
    let s := affineIdealModuleSection R S φ u
    (affineModuleFibreIso R (φ ≫ ψ) M).hom
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).app M ≪≫
          (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).app M).hom)
        (i1_module_pointValue ((Scheme.Modules.pullback (Spec.map φ)).obj M)
          (i1_module_sectionPullback (Spec.map φ) M s) (Spec.map ψ))) =
      (1 : ℂ) ⊗ₜ[R, (φ ≫ ψ).hom]
        (show (moduleSpecΓFunctor (R := R)).obj M from
          (s2e_affine_ideal_sections_equiv R S φ).symm u) := by
  let M := Conormal.idealModule (Spec.map φ)
  letI : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
  have h := affineModuleFibreIso_composite_section_apply R (φ ≫ ψ) (Spec.map ψ)
    (Spec.map φ) (Spec.map_comp φ ψ).symm M (affineIdealModuleSection R S φ u)
  have ht := congrArg (fun m : (moduleSpecΓFunctor (R := R)).obj M =>
    (1 : ℂ) ⊗ₜ[R, (φ ≫ ψ).hom] m) (affineIdealModuleSection_top R S φ u)
  exact h.trans ht

#print axioms affineIdealSection_composite_tensor_value

#print axioms affineModuleFibreIso_composite_section_apply

#print axioms moduleSectionPullback_eq_sectionPullback
#print axioms modulePointValue_composition_comparison

end HodgeLean.Foundations.TubularEuler
