import HodgeLean.Foundations.TubularEuler.AffineConormalSectionFibreHelpers
import HodgeLean.Foundations.TubularEuler.ModuleIsoValueHelpers
import HodgeLean.Foundations.TubularEuler.AffineCompositeFibreEvaluationHelpers

/-! # Section evaluation through the named composite affine module comparison

The comparison sends the actual pulled-back section to its original pure tensor.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem affineCompositeModuleFibreIso_section_apply
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (s : SheafOfModules.unit.{0} (Spec R).ringCatSheaf ⟶ M) :
    (affineCompositeModuleFibreIso R S φ ψ M).hom
      (i1_module_pointValue ((Scheme.Modules.pullback (Spec.map φ)).obj M)
        (i1_module_sectionPullback (Spec.map φ) M s) (Spec.map ψ)) =
      (1 : ℂ) ⊗ₜ[R, (φ ≫ ψ).hom]
        (show (moduleSpecΓFunctor (R := R)).obj M from
          s.val.app (.op ⊤) (1 : Γ(Spec R, ⊤))) := by
  exact affineCompositeModuleFibreIso_apply_eq R S φ ψ M _ _
    (affineModuleFibreIso_composite_section_apply R (φ ≫ ψ) (Spec.map ψ)
      (Spec.map φ) (Spec.map_comp φ ψ).symm M s)

#print axioms affineCompositeModuleFibreIso_section_apply

end HodgeLean.Foundations.TubularEuler
