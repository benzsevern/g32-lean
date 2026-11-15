import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Differential bases retaining specified etale polynomial coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- A specified etale polynomial coordinate map supplies a basis of the actual
differential module by scalar extension of the original polynomial basis. -/
def etaleCoordinateDifferentialBasis
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R]
    (n : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale) :
    Module.Basis (Fin n) R Ω[R⁄k] := by
  letI : Algebra (MvPolynomial (Fin n) k) R := c.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin n) k) R :=
    IsScalarTower.of_algebraMap_eq (fun a => (c.commutes a).symm)
  letI : Algebra.Etale (MvPolynomial (Fin n) k) R := RingHom.etale_algebraMap.mp hc
  exact ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).baseChange R).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial (Fin n) k) R)

/-- The resulting basis vectors are the actual differentials of the specified
original coordinate functions. -/
theorem etaleCoordinateDifferentialBasis_apply
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R]
    (n : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale) (i : Fin n) :
    etaleCoordinateDifferentialBasis k R n c hc i =
      KaehlerDifferential.D k R (c (MvPolynomial.X i)) := by
  unfold etaleCoordinateDifferentialBasis
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

#print axioms etaleCoordinateDifferentialBasis
#print axioms etaleCoordinateDifferentialBasis_apply
end HodgeLean.Foundations.Program.G32Native
