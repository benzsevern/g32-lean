import HodgeLean.Foundations.BundleResolution.ModuleSectionPullbackCoherenceHelpers
import HodgeLean.Foundations.BundleResolution.ModuleFreeFibreGeneratorHelpers

/-! # Algebra of actual module-section specialization

Actual point specialization is additive, respects regular coefficients
and module morphisms, and is coherent with composition and equal point maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open HodgeLean.Foundations.Algebraic
namespace HodgeLean.Foundations.BundleResolution

def i1_module_pointValueAddHom {X : Scheme.{0}} (M : X.Modules) (a : Spec ↧ℂ ⟶ X) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ M) →+
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj ((Scheme.Modules.pullback a).obj M) where
  toFun s := i1_module_pointValue M s a
  map_zero' := by
    dsimp only [i1_module_pointValue, i1_module_sectionPullback]
    rw [Functor.map_zero, comp_zero]
    rfl
  map_add' s t := by
    dsimp only [i1_module_pointValue, i1_module_sectionPullback]
    rw [Functor.map_add, Preadditive.comp_add]
    rfl

theorem i1_moduleSpecΓ_linearMap_apply {N : (Spec ↧ℂ).Modules}
    (t : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶ N) (r : Γ(Spec ↧ℂ, ⊤)) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map t r =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r •
        (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map t (1 : Γ(Spec ↧ℂ, ⊤)) := by
  let A := tilde.isoTop (R := CommRingCat.of ℂ) (ModuleCat.of ℂ ℂ)
  let m := (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map t
  have h1 : A.hom (1 : ℂ) = (1 : Γ(Spec ↧ℂ, ⊤)) := i1_tildeSelf_isoTop_one _
  have hi : A.inv r = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r := i1_tildeSelf_isoTop_inv _ r
  change m r = _
  calc
    m r = m (A.hom (A.inv r)) := by rw [Iso.inv_hom_id_apply]
    _ = m (A.hom (A.inv r • (1 : ℂ))) := by rw [smul_eq_mul, mul_one]
    _ = A.inv r • m (A.hom (1 : ℂ)) := by rw [map_smul, map_smul]
    _ = _ := by rw [hi, h1]

theorem i1_module_scal_top_one (X : Scheme.{0}) (c : Γ(X, ⊤)) :
    (f5sheaf_scal c).val.app (op ⊤) (1 : Γ(X, ⊤)) = c := by
  rw [f5sheaf_scal_app, one_mul]
  exact CategoryTheory.congr_fun (X.presheaf.map_id _) c

theorem i1_module_pointValue_scalar {X : Scheme.{0}} (M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) (a : Spec ↧ℂ ⟶ X) (c : Γ(X, ⊤)) :
    i1_module_pointValue M (f5sheaf_scal c ≫ s) a =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (a.appTop c) • i1_module_pointValue M s a := by
  let A := i1_module_unitPullbackIso a
  have hs : (Scheme.Modules.pullback a).map (f5sheaf_scal c) ≫ A.hom =
      A.hom ≫ f5sheaf_scal (a.appTop c) := f5sheaf_pullback_scal a c
  have hsc : A.inv ≫ (Scheme.Modules.pullback a).map (f5sheaf_scal c) =
      f5sheaf_scal (a.appTop c) ≫ A.inv := by
    apply (cancel_mono A.hom).1
    simp only [Category.assoc, hs, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hsec : i1_module_sectionPullback a M (f5sheaf_scal c ≫ s) =
      f5sheaf_scal (a.appTop c) ≫ i1_module_sectionPullback a M s := by
    dsimp only [i1_module_sectionPullback]
    rw [Functor.map_comp, ← Category.assoc, hsc, Category.assoc]
  unfold i1_module_pointValue
  rw [hsec, Functor.map_comp, ConcreteCategory.comp_apply]
  have htop : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      (f5sheaf_scal (a.appTop c)) (1 : Γ(Spec ↧ℂ, ⊤)) = a.appTop c :=
    i1_module_scal_top_one _ _
  rw [htop]
  exact i1_moduleSpecΓ_linearMap_apply _ _

theorem i1_module_pointValue_naturality {X : Scheme.{0}} {M N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) (t : M ⟶ N) (a : Spec ↧ℂ ⟶ X) :
    i1_module_pointValue N (s ≫ t) a =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map ((Scheme.Modules.pullback a).map t)
        (i1_module_pointValue M s a) := by
  simp only [i1_module_pointValue, i1_module_sectionPullback, Functor.map_comp,
    Category.assoc, ConcreteCategory.comp_apply]

theorem i1_module_pointValue_pullback_comp {X Y : Scheme.{0}}
    (a : Spec ↧ℂ ⟶ X) (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackComp a f).hom.app M)
      (i1_module_pointValue ((Scheme.Modules.pullback f).obj M)
        (i1_module_sectionPullback f M s) a) = i1_module_pointValue M s (a ≫ f) := by
  unfold i1_module_pointValue
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← i1_module_sectionPullback_comp]

theorem i1_module_pointValue_congr {X : Scheme.{0}} (M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) {a b : Spec ↧ℂ ⟶ X} (h : a = b) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      ((Scheme.Modules.pullbackCongr h).hom.app M) (i1_module_pointValue M s a) =
      i1_module_pointValue M s b := by
  subst b
  rfl
end HodgeLean.Foundations.BundleResolution
