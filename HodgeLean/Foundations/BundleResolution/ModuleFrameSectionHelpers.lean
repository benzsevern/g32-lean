import HodgeLean.Foundations.BundleResolution.ModuleFreeFibreGeneratorHelpers
import HodgeLean.Foundations.BundleResolution.ModuleSectionHelpers

/-! # Local frame generators as actual specialized sections

The fibre comparison sends specialized free generators to coordinate
vectors, and local frame maps transport this equality to the actual module.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution
variable {Q : Over (Spec ↧ℂ)}
private local instance (x : ComplexPoint Q) :
    (SheafOfModules.pushforward.{0} x.left.toRingCatSheafHom).IsRightAdjoint :=
  (inferInstance : (Scheme.Modules.pushforward x.left).IsRightAdjoint)

theorem i1_freeModuleFibreIso_generator (I : Type) (x : ComplexPoint Q) (i : I) :
    (i1_freeModuleFibreIso I x).hom
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (inv (C := SheafOfModules (Spec ↧ℂ).ringCatSheaf)
          (SheafOfModules.pullbackObjUnitToUnit.{0} x.left.toRingCatSheafHom) ≫
          (Scheme.Modules.pullback x.left).map (SheafOfModules.ιFree i))
        (1 : Γ(Spec ↧ℂ, ⊤))) = Finsupp.single i 1 := by
  have h := CategoryTheory.congr_fun (i1_freeModuleFibreIso_injection I x i)
    (1 : Γ(Spec ↧ℂ, ⊤))
  have hA : (tilde.isoTop (R := CommRingCat.of ℂ) (ModuleCat.of ℂ ℂ)).inv
      (1 : Γ(Spec ↧ℂ, ⊤)) = 1 := by
    rw [← i1_tildeSelf_isoTop_one (CommRingCat.of ℂ), Iso.hom_inv_id_apply]
  simp only [ConcreteCategory.comp_apply] at h
  erw [hA] at h
  exact h

theorem i1_module_frameGenerator_value (M : Q.left.Modules) (U : Q.left.Opens) (I : Type)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) (i : I) :
    i1_moduleSectionValue M U (SheafOfModules.ιFree i ≫ e.hom) x hx =
      (i1_module_frameFibreIso M U I e x hx).hom (Finsupp.single i 1) := by
  have hg := i1_freeModuleFibreIso_generator I (ComplexPoint.asOpenPoint Q U x hx) i
  dsimp only [i1_module_frameFibreIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, ConcreteCategory.comp_apply]
  rw [← hg]
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply]
  simp only [i1_moduleSectionValue, i1_module_openFibreIso, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, ConcreteCategory.comp_apply, Category.assoc]
  rfl
end HodgeLean.Foundations.BundleResolution
