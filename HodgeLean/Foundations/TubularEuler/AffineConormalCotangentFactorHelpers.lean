import HodgeLean.Foundations.TubularEuler.AffineModuleFibreHelpers

/-! # Original cotangent tensor fibre factors

The point scalar map annihilates the original immersion ideal before its cotangent quotient.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 50000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

theorem affineConormalScalar_killsIdeal
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    ∀ r ∈ RingHom.ker φ.hom, algebraMap R ℂ r = 0 := by
  letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
  intro r hr
  change φ.hom r = 0 at hr
  change ψ.hom (φ.hom r) = 0
  rw [hr, map_zero]

theorem affineConormalFibreCotangentIso_eq
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (ψ : S ⟶ CommRingCat.of ℂ) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    affineConormalFibreCotangentIso R S φ ψ =
      affineConormalFibreIdealTensorIso R S φ ψ ≪≫
        (conormalFibreTensorEquiv (RingHom.ker φ.hom)
          (affineConormalScalar_killsIdeal R S φ ψ)).toModuleIso := by
  rfl

#print axioms affineConormalFibreCotangentIso_eq

#print axioms affineConormalScalar_killsIdeal

end HodgeLean.Foundations.TubularEuler
