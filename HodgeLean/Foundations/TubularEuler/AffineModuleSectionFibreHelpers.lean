import HodgeLean.Foundations.TubularEuler.AffineModulePointComparisonHelpers
import HodgeLean.Foundations.TubularEuler.ModuleSectionPullbackUnitHelpers
import HodgeLean.Foundations.BundleResolution.ModulePointValueAlgebraHelpers

/-! # Actual affine module section values under the original fibre comparison

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem affineModulePointUnit_section_apply
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) (s : SheafOfModules.unit.{0} (Spec R).ringCatSheaf ⟶ M) :
    affineModulePointUnit R ψ M (s.val.app (.op ⊤) (1 : Γ(Spec R, ⊤))) =
      i1_module_pointValue M s (Spec.map ψ) := by
  have h := moduleSection_pullback_top_value (Spec.map ψ) M s
  exact h.symm

#print axioms affineModulePointUnit_section_apply

theorem affineModuleFibreIso_section_apply
    (R : CommRingCat.{0}) (ψ : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (s : SheafOfModules.unit.{0} (Spec R).ringCatSheaf ⟶ M) :
    (affineModuleFibreIso R ψ M).hom (i1_module_pointValue M s (Spec.map ψ)) =
      (1 : ℂ) ⊗ₜ[R, ψ.hom]
        (show (moduleSpecΓFunctor (R := R)).obj M from
          s.val.app (.op ⊤) (1 : Γ(Spec R, ⊤))) := by
  rw [← affineModulePointUnit_section_apply]
  exact affineModuleFibreIso_pointUnit_apply R ψ M _

#print axioms affineModuleFibreIso_section_apply

end HodgeLean.Foundations.TubularEuler
