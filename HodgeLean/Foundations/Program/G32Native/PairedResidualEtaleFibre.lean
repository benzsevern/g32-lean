import HodgeLean.Foundations.Program.G32Native.PairedResidualDifferentialFibre
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # The original differential fibre after formally etale localization -/
noncomputable section
set_option maxHeartbeats 400000
open KaehlerDifferential TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Formally etale localization preserves the actual absolute differential fibre.
Source: Stacks Project, Tag 00S2; Hartshorne, Algebraic Geometry, II.8. -/
def residualEtaleDifferentialFibreEquiv
    (R A L K : Type*) [CommRing R] [CommRing A] [CommRing L] [Field K]
    [Algebra R A] [Algebra R L] [Algebra A L] [IsScalarTower R A L]
    [Algebra A K] [Algebra L K] [IsScalarTower A L K]
    [Algebra.FormallyEtale A L] : K ⊗[L] Ω[L⁄R] ≃ₗ[K] K ⊗[A] Ω[A⁄R] :=
  ((tensorKaehlerEquivOfFormallyEtale R A L).symm.baseChange L K _ _).trans
    (AlgebraTensorModule.cancelBaseChange A L K K Ω[A⁄R])

/-- The localization fibre identification retains each original differential.
Source: Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_etale_differential_fibre_D
    (R A L K : Type*) [CommRing R] [CommRing A] [CommRing L] [Field K]
    [Algebra R A] [Algebra R L] [Algebra A L] [IsScalarTower R A L]
    [Algebra A K] [Algebra L K] [IsScalarTower A L K]
    [Algebra.FormallyEtale A L] (a : A) :
    residualEtaleDifferentialFibreEquiv R A L K
      (1 ⊗ₜ[L] D R L (algebraMap A L a)) = 1 ⊗ₜ[A] D R A a := by
  simp only [residualEtaleDifferentialFibreEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

#print axioms residualEtaleDifferentialFibreEquiv
#print axioms residual_etale_differential_fibre_D
end HodgeLean.Foundations.Program.G32Native
