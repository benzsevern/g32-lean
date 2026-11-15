import HodgeLean.Foundations.TubularEuler.AffineModuleFibreHelpers

/-! # Isomorphism factors of composite affine module transport

The comparison retains the original pullback-composition isomorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler

theorem affineCompositeModuleFibreIso_eq
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] :
    affineCompositeModuleFibreIso R S φ ψ M =
      (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
        ((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).app M ≪≫
          (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).app M) ≪≫
      affineModuleFibreIso R (φ ≫ ψ) M := by
  rfl

#print axioms affineCompositeModuleFibreIso_eq

end HodgeLean.Foundations.TubularEuler
