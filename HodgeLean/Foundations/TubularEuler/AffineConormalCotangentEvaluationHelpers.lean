import HodgeLean.Foundations.TubularEuler.AffineConormalCotangentFactorHelpers
import HodgeLean.Foundations.TubularEuler.ModuleIsoCompositeValueHelpers

/-! # Values through the original affine conormal cotangent comparison

The named comparison retains both the original ideal tensor value and its cotangent quotient.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

theorem affineConormalFibreCotangentIso_apply_eq
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    ∀ (x : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
        ((Scheme.Modules.pullback (Spec.map ψ)).obj (Conormal.sheaf (Spec.map φ))))
      (v : ℂ ⊗[R] RingHom.ker φ.hom) (y : ℂ ⊗[R] (RingHom.ker φ.hom).Cotangent),
      (affineConormalFibreIdealTensorIso R S φ ψ).hom x = v →
      (conormalFibreTensorEquiv (RingHom.ker φ.hom)
        (affineConormalScalar_killsIdeal R S φ ψ)).toModuleIso.hom v = y →
      (affineConormalFibreCotangentIso R S φ ψ).hom x = y := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  dsimp only
  intro x v y ha hb
  exact moduleIso_apply_eq_of_trans_values
    (affineConormalFibreIdealTensorIso R S φ ψ)
    (conormalFibreTensorEquiv (RingHom.ker φ.hom)
      (affineConormalScalar_killsIdeal R S φ ψ)).toModuleIso
    (affineConormalFibreCotangentIso R S φ ψ)
    (affineConormalFibreCotangentIso_eq R S φ ψ) x v y ha hb

#print axioms affineConormalFibreCotangentIso_apply_eq

end HodgeLean.Foundations.TubularEuler
