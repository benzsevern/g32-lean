import HodgeLean.Foundations.TubularEuler.AffineConormalTensorFactorHelpers
import HodgeLean.Foundations.TubularEuler.ModuleIsoCompositeValueHelpers

/-! # Evaluation of the original affine conormal ideal tensor comparison

Each stage retains its original fibre value and scalar-extension map.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program

theorem affineConormalFibreIdealTensorIso_apply_eq
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    ∀ (x : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback (Spec.map ψ)).obj (Conormal.sheaf (Spec.map φ))))
      (v : (ModuleCat.extendScalars (φ ≫ ψ).hom).obj
        ((moduleSpecΓFunctor (R := R)).obj (Conormal.idealModule (Spec.map φ)) ))
      (y : ℂ ⊗[R] RingHom.ker φ.hom),
      (affineConormalFibreIdealSectionsIso R S φ ψ).hom x = v →
      (s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker φ.hom))).hom
        ((ModuleCat.extendScalars (φ ≫ ψ).hom).map
          (s2e_affine_ideal_sections_equiv R S φ).toModuleIso.hom v) = y →
      (affineConormalFibreIdealTensorIso R S φ ψ).hom x = y := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  dsimp only
  intro x v y ha h
  exact moduleIso_apply_eq_of_middle_map
    (ModuleCat.extendScalars (φ ≫ ψ).hom)
    (affineConormalFibreIdealSectionsIso R S φ ψ)
    (s2e_affine_ideal_sections_equiv R S φ).toModuleIso
    (s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker φ.hom)))
    (affineConormalFibreIdealTensorIso R S φ ψ)
    (affineConormalFibreIdealTensorIso_eq R S φ ψ) x v y ha h

#print axioms affineConormalFibreIdealTensorIso_apply_eq

end HodgeLean.Foundations.TubularEuler
