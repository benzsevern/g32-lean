import HodgeLean.Foundations.TubularEuler.AffineConormalCompositeFibreHelpers
import HodgeLean.Foundations.TubularEuler.ModuleIsoValueHelpers

/-! # Values through the original affine conormal section comparison

The equality of isomorphisms is used before specializing section or tensor values.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

theorem affineConormalFibreIdealSectionsIso_apply_eq
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    letI : IsIso (Conormal.idealModule (Spec.map φ)).fromTildeΓ := s2e_idealModule_spec_fromTilde_isIso R (Spec.map φ)
    ∀ (x : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback (Spec.map ψ)).obj (Conormal.sheaf (Spec.map φ))))
      (y : (ModuleCat.extendScalars (φ ≫ ψ).hom).obj
        ((moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map φ)))),
      (affineCompositeModuleFibreIso R S φ ψ (Conormal.idealModule (Spec.map φ))).hom x = y →
      (affineConormalFibreIdealSectionsIso R S φ ψ).hom x = y := by
  intro x y h
  exact moduleIso_apply_eq_of_eq _ _
    (affineConormalFibreIdealSectionsIso_eq_composite R S φ ψ) x y h

#print axioms affineConormalFibreIdealSectionsIso_apply_eq

end HodgeLean.Foundations.TubularEuler
