import HodgeLean.Foundations.TubularEuler.AffineModuleFibreHelpers

/-! # Original affine conormal ideal tensor factors

The named comparison retains scalar extension of the original ideal section equivalence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

theorem affineConormalFibreIdealTensorIso_eq
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    affineConormalFibreIdealTensorIso R S φ ψ =
      affineConormalFibreIdealSectionsIso R S φ ψ ≪≫
        (ModuleCat.extendScalars (φ ≫ ψ).hom).mapIso
          (s2e_affine_ideal_sections_equiv R S φ).toModuleIso ≪≫
        s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker φ.hom)) := by
  rfl

#print axioms affineConormalFibreIdealTensorIso_eq

end HodgeLean.Foundations.TubularEuler
