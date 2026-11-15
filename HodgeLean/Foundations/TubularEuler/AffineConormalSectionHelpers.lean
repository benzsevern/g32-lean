import HodgeLean.Foundations.TubularEuler.AffineModuleSectionFibreHelpers
import HodgeLean.Foundations.BundleResolution.ModuleGlobalSectionHelpers

/-! # Sections from original affine immersion ideal elements

The original ideal-module section is pulled back to the actual conormal sheaf.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleResolution

def affineIdealModuleSection (R S : CommRingCat.{0}) (φ : R ⟶ S) (u : RingHom.ker φ.hom) :
    SheafOfModules.unit.{0} (Spec R).ringCatSheaf ⟶ Conormal.idealModule (Spec.map φ) :=
  (i1_module_unitHomEquivTop (Conormal.idealModule (Spec.map φ))).symm
    ((s2e_affine_ideal_sections_equiv R S φ).symm u)

theorem affineIdealModuleSection_top (R S : CommRingCat.{0}) (φ : R ⟶ S)
    (u : RingHom.ker φ.hom) :
    (affineIdealModuleSection R S φ u).val.app (.op ⊤) (1 : Γ(Spec R, ⊤)) =
      (s2e_affine_ideal_sections_equiv R S φ).symm u := by
  exact (i1_module_unitHomEquivTop (Conormal.idealModule (Spec.map φ))).apply_symm_apply _

#print axioms affineIdealModuleSection_top

end HodgeLean.Foundations.TubularEuler
