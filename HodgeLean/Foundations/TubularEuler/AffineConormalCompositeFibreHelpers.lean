import HodgeLean.Foundations.TubularEuler.AffineModuleFibreHelpers

/-! # Original conormal comparison as composite affine module transport

The comparison retains the original ideal module and its actual scalar extension.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

theorem affineConormalFibreIdealSectionsIso_eq_composite
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    let M := Conormal.idealModule (Spec.map φ)
    letI : IsIso M.fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
    affineConormalFibreIdealSectionsIso R S φ ψ =
      affineCompositeModuleFibreIso R S φ ψ M := by
  rfl

#print axioms affineConormalFibreIdealSectionsIso_eq_composite

end HodgeLean.Foundations.TubularEuler
