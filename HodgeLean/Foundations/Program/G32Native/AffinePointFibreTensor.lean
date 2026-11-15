import HodgeLean.Foundations.Program.SchoenCycleC2AffinePullbackHelpers
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.Analysis.Complex.Basic

/-! # The actual affine point fibre as scalar extension of module sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Pullback to an actual affine complex point identifies its module fibre
with scalar extension of the original module's global sections. -/
def affinePointFibreTensorEquiv (R : CommRingCat.{0}) (ε : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] :
    letI : Algebra R ℂ := ε.hom.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ε)).obj M) ≃ₗ[ℂ]
      ℂ ⊗[R] ((moduleSpecΓFunctor (R := R)).obj M) := by
  letI : Algebra R ℂ := ε.hom.toAlgebra
  let N := (moduleSpecΓFunctor (R := R)).obj M
  let e := ((Scheme.Modules.pullback (Spec.map ε)).mapIso (asIso M.fromTildeΓ)).symm ≪≫
    (s2e_affine_pullback_tilde_iso R (CommRingCat.of ℂ) ε).app N
  exact ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso e).toLinearEquiv.trans
    ((tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app
      ((ModuleCat.extendScalars ε.hom).obj N)).symm.toLinearEquiv

/-- Duals of the actual point fibres are exactly ambient-ring-linear
functionals on the original module sections with values at that point. -/
def affinePointDualEquiv (R : CommRingCat.{0}) (ε : R ⟶ CommRingCat.of ℂ)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] :
    letI : Algebra R ℂ := ε.hom.toAlgebra
    Module.Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ε)).obj M)) ≃ₗ[ℂ]
      (((moduleSpecΓFunctor (R := R)).obj M) →ₗ[R] ℂ) := by
  letI : Algebra R ℂ := ε.hom.toAlgebra
  exact (affinePointFibreTensorEquiv R ε M).symm.dualMap.trans
    (LinearMap.liftBaseChangeEquiv ℂ).symm

#print axioms affinePointDualEquiv
#print axioms affinePointFibreTensorEquiv
end HodgeLean.Foundations.Program.G32Native
