import HodgeLean.Foundations.TubularEuler.AffineCompositeFibreIsoHelpers
import HodgeLean.Foundations.TubularEuler.ModuleIsoValueHelpers

/-! # Evaluation through the original composite affine module comparison

The value calculation is separated from the section and tensor specialization.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

theorem affineCompositeModuleFibreIso_apply_eq
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (x : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ψ)).obj
        ((Scheme.Modules.pullback (Spec.map φ)).obj M)))
    (y : (ModuleCat.extendScalars (φ ≫ ψ).hom).obj
      ((moduleSpecΓFunctor (R := R)).obj M))
    (h : (affineModuleFibreIso R (φ ≫ ψ) M).hom
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).app M ≪≫
          (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).app M).hom) x) = y) :
    (affineCompositeModuleFibreIso R S φ ψ M).hom x = y := by
  exact moduleIso_apply_eq_of_factorization
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ))
    ((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).app M ≪≫
      (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).app M)
    (affineModuleFibreIso R (φ ≫ ψ) M) (affineCompositeModuleFibreIso R S φ ψ M)
    (affineCompositeModuleFibreIso_eq R S φ ψ M) x y h

#print axioms affineCompositeModuleFibreIso_apply_eq

end HodgeLean.Foundations.TubularEuler
