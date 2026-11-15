import HodgeLean.Foundations.Program.G32Native.PairedC3ProductSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Native coordinates of finite free module sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable (X : Scheme.{0}) (s : ℕ)

/-- The finite free sheaf as the product of its original structure modules. -/
def pairedC3FreeProductIso :
    (SheafOfModules.free (R := X.ringCatSheaf) (Fin s) : X.Modules) ≅
      ∏ᶜ (fun _ : Fin s => (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := by
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let M : Fin s → X.Modules := fun _ => SheafOfModules.unit X.ringCatSheaf
  exact (biproduct.isoCoproduct M).symm ≪≫ biproduct.isoProduct M

/-- A sheaf isomorphism gives an equivalence over the original section ring. -/
def pairedC3ModuleIsoSectionEquiv {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) where
  toFun := e.hom.app V
  invFun := e.inv.app V
  map_add' := (e.hom.app V).hom.map_add
  map_smul' r v := Scheme.Modules.Hom.app_smul e.hom r v
  left_inv v := by
    change (e.hom.app V ≫ e.inv.app V) v = v
    rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  right_inv v := by
    change (e.inv.app V ≫ e.hom.app V) v = v
    rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl

/-- Native section coordinates for the finite free module. -/
def pairedC3FreeSectionEquiv (V : X.Opens) :
    Γ((SheafOfModules.free (R := X.ringCatSheaf) (Fin s) : X.Modules), V) ≃ₗ[Γ(X, V)]
      (Fin s → Γ(X, V)) :=
  LinearEquiv.trans
    (pairedC3ModuleIsoSectionEquiv X (pairedC3FreeProductIso X s) V)
    (pairedC3ProductSectionEquiv (fun _ : Fin s =>
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)) V)

/-- Finite free coordinates are the original module projection maps. -/
theorem paired_c3_free_section_coordinate (V : X.Opens)
    (v : Γ((SheafOfModules.free (R := X.ringCatSheaf) (Fin s) : X.Modules), V)) (a : Fin s) :
    pairedC3FreeSectionEquiv X s V v a =
      Scheme.Modules.Hom.app ((pairedC3FreeProductIso X s).hom ≫
        Pi.π (fun _ : Fin s => (SheafOfModules.unit X.ringCatSheaf : X.Modules)) a) V v := by
  change pairedC3ProductSectionEquiv _ V (Scheme.Modules.Hom.app (pairedC3FreeProductIso X s).hom V v) a = _
  rw [paired_c3_product_section_coordinate]
  rfl


/-- Native free-module coordinates commute with the original restrictions. -/
theorem paired_c3_free_section_restrict (V W : X.Opens) (hWV : W ≤ V)
    (v : Γ((SheafOfModules.free (R := X.ringCatSheaf) (Fin s) : X.Modules), V)) :
    pairedC3FreeSectionEquiv X s W
      ((Scheme.Modules.presheaf (SheafOfModules.free (R := X.ringCatSheaf) (Fin s))).map
        (homOfLE hWV).op v) =
      fun a => X.presheaf.map (homOfLE hWV).op (pairedC3FreeSectionEquiv X s V v a) := by
  funext a
  rw [paired_c3_free_section_coordinate, paired_c3_free_section_coordinate]
  exact PresheafOfModules.naturality_apply
    (((pairedC3FreeProductIso X s).hom ≫
      Pi.π (fun _ : Fin s => (SheafOfModules.unit X.ringCatSheaf : X.Modules)) a)).val
        (homOfLE hWV).op v

#print axioms pairedC3ModuleIsoSectionEquiv
#print axioms paired_c3_free_section_restrict
#print axioms pairedC3FreeProductIso
#print axioms pairedC3FreeSectionEquiv
#print axioms paired_c3_free_section_coordinate
end HodgeLean.Foundations.Program.G32Native
