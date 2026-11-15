import HodgeLean.Foundations.BundleResolution.ModuleFrameFibreHelpers

/-! # Generator compatibility for actual free module fibres

The associated-module comparison preserves the canonical free generator
injections. These identities link local algebraic sections to fibre bases.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution

theorem i1_tildeFinsupp_injection {R : CommRingCat.{0}} (I : Type) (i : I) :
    (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] I →₀ R)) ≫
      (tildeFinsupp (R := R) I).hom = SheafOfModules.ιFree i := by
  unfold tildeFinsupp
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (C := (Spec R).Modules) _ _ (Discrete.mk i)
theorem i1_tildeSelf_isoTop_one (R : CommRingCat.{0}) :
    (tilde.isoTop (R := R) (ModuleCat.of R R)).hom (1 : R) =
      (1 : Γ(Spec R, ⊤)) := by
  change StructureSheaf.toOpenₗ R R ⊤ 1 = 1
  exact StructureSheaf.const_one ⊤

variable {Q : Over (Spec ↧ℂ)}
private local instance (x : ComplexPoint Q) :
    (SheafOfModules.pushforward.{0} x.left.toRingCatSheafHom).IsRightAdjoint :=
  (inferInstance : (Scheme.Modules.pushforward x.left).IsRightAdjoint)

theorem i1_freeModuleFibreIso_injection (I : Type) (x : ComplexPoint Q) (i : I) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
      (inv (C := SheafOfModules (Spec ↧ℂ).ringCatSheaf) (SheafOfModules.pullbackObjUnitToUnit.{0} x.left.toRingCatSheafHom) ≫
        (Scheme.Modules.pullback x.left).map (SheafOfModules.ιFree i)) ≫
      (i1_freeModuleFibreIso I x).hom =
    (tilde.isoTop (R := CommRingCat.of ℂ) (ModuleCat.of ℂ ℂ)).inv ≫
      ModuleCat.ofHom (Finsupp.lsingle i : ℂ →ₗ[ℂ] I →₀ ℂ) := by
  let F := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let l := ModuleCat.ofHom (Finsupp.lsingle i : ℂ →ₗ[ℂ] I →₀ ℂ)
  let T := tildeFinsupp (R := CommRingCat.of ℂ) I
  let A := tilde.isoTop (R := CommRingCat.of ℂ) (ModuleCat.of ℂ ℂ)
  let B := tilde.isoTop (R := CommRingCat.of ℂ) (ModuleCat.of ℂ (I →₀ ℂ))
  have h₁ : inv (C := SheafOfModules (Spec ↧ℂ).ringCatSheaf) (SheafOfModules.pullbackObjUnitToUnit.{0} x.left.toRingCatSheafHom) ≫
      (Scheme.Modules.pullback x.left).map (SheafOfModules.ιFree i) ≫
      (SheafOfModules.pullbackObjFreeIso x.left.toRingCatSheafHom I).hom =
      SheafOfModules.ιFree i := by
    erw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
      IsIso.inv_hom_id_assoc]
  have h₂ : SheafOfModules.ιFree i ≫ T.inv = (tilde.functor (CommRingCat.of ℂ)).map l := by
    rw [← i1_tildeFinsupp_injection I i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₃ : l ≫ B.hom = A.hom ≫ F.map ((tilde.functor (CommRingCat.of ℂ)).map l) :=
    (tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).hom.naturality l
  let P := SheafOfModules.pullbackObjFreeIso x.left.toRingCatSheafHom I
  let t : SheafOfModules.unit (Spec ↧ℂ).ringCatSheaf ⟶
      (Scheme.Modules.pullback x.left).obj (SheafOfModules.free I) :=
    inv (C := SheafOfModules (Spec ↧ℂ).ringCatSheaf)
      (SheafOfModules.pullbackObjUnitToUnit.{0} x.left.toRingCatSheafHom) ≫
      (Scheme.Modules.pullback x.left).map (SheafOfModules.ιFree i)
  have ht : t ≫ P.hom = SheafOfModules.ιFree i := by
    simpa only [t, P, Category.assoc] using h₁
  change F.map t ≫ F.map P.hom ≫ F.map T.inv ≫ B.inv = A.inv ≫ l
  rw [← Category.assoc, ← F.map_comp, ht, ← Category.assoc, ← F.map_comp, h₂]
  apply (cancel_mono B.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₃, Iso.inv_hom_id_assoc]
theorem i1_tildeSelf_isoTop_hom (R : CommRingCat.{0}) (r : R) :
    (tilde.isoTop (R := R) (ModuleCat.of R R)).hom r = (Scheme.ΓSpecIso R).inv r := by
  change StructureSheaf.toOpenₗ R R ⊤ r = (Scheme.ΓSpecIso R).inv r
  rw [Scheme.ΓSpecIso_inv]
  rfl

theorem i1_tildeSelf_isoTop_inv (R : CommRingCat.{0}) (r : Γ(Spec R, ⊤)) :
    (tilde.isoTop (R := R) (ModuleCat.of R R)).inv r = (Scheme.ΓSpecIso R).hom r := by
  apply (ConcreteCategory.bijective_of_isIso
    (tilde.isoTop (R := R) (ModuleCat.of R R)).hom).1
  rw [Iso.inv_hom_id_apply, i1_tildeSelf_isoTop_hom, Iso.hom_inv_id_apply]
end HodgeLean.Foundations.BundleResolution
