import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Section coordinates for products of the original module sheaves -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable {X : Scheme.{0}} {ι : Type} (M : ι → X.Modules)

/-- Taking sections of a product gives the product of the original section modules. -/
def pairedC3ProductSectionEquiv (V : X.Opens) :
    Γ((∏ᶜ M : X.Modules), V) ≃ₗ[Γ(X, V)] (∀ i, Γ(M i, V)) :=
  ((PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (op V)) M) ≪≫
    ModuleCat.piIsoPi _).toLinearEquiv

/-- Product section coordinates are the original sheaf projection maps. -/
theorem paired_c3_product_section_coordinate (V : X.Opens)
    (v : Γ((∏ᶜ M : X.Modules), V)) (i : ι) :
    pairedC3ProductSectionEquiv M V v i = (Pi.π M i).app V v := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op V)
  have h : ((PreservesProduct.iso F M) ≪≫ ModuleCat.piIsoPi _).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) = F.map (Pi.π M i) := by
    rw [Iso.trans_hom, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
      PreservesProduct.iso_hom, piComparison_comp_π]
  exact ConcreteCategory.congr_hom h v

/-- Product coordinates commute with the original section restrictions. -/
theorem paired_c3_product_section_restrict (V W : X.Opens) (hWV : W ≤ V)
    (v : Γ((∏ᶜ M : X.Modules), V)) (i : ι) :
    pairedC3ProductSectionEquiv M W
        ((∏ᶜ M : X.Modules).presheaf.map (homOfLE hWV).op v) i =
      (M i).presheaf.map (homOfLE hWV).op (pairedC3ProductSectionEquiv M V v i) := by
  rw [paired_c3_product_section_coordinate, paired_c3_product_section_coordinate]
  exact PresheafOfModules.naturality_apply (Pi.π M i).val (homOfLE hWV).op v

#print axioms pairedC3ProductSectionEquiv
#print axioms paired_c3_product_section_coordinate
#print axioms paired_c3_product_section_restrict
end HodgeLean.Foundations.Program.G32Native
