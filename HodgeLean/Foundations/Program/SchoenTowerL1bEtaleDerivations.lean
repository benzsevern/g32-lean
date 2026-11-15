import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (A R ι : Type*) [CommRing A] [CommRing R]
    [Algebra A R] [Algebra (MvPolynomial ι A) R]
    [IsScalarTower A (MvPolynomial ι A) R]
    [Algebra.FormallyEtale (MvPolynomial ι A) R]

/-- The polynomial differential basis transported along a formally étale map. -/
def s2v_l1b_etaleDifferentialBasis : Module.Basis ι R Ω[R⁄A] :=
  ((KaehlerDifferential.mvPolynomialBasis A ι).baseChange R).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A (MvPolynomial ι A) R)

@[simp] theorem s2v_l1b_etaleDifferentialBasis_apply (j : ι) :
    s2v_l1b_etaleDifferentialBasis A R ι j =
      KaehlerDifferential.D A R (algebraMap (MvPolynomial ι A) R (MvPolynomial.X j)) := by
  rw [s2v_l1b_etaleDifferentialBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  apply (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A (MvPolynomial ι A) R).symm.injective
  rw [LinearEquiv.symm_apply_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

/-- The derivation dual to a specified polynomial coordinate. -/
def s2v_l1b_etaleCoordinateDerivation (j : ι) : Derivation A R R :=
  ((s2v_l1b_etaleDifferentialBasis A R ι).coord j).compDer (KaehlerDifferential.D A R)

@[simp] theorem s2v_l1b_etaleCoordinateDerivation_apply [DecidableEq ι] (j k : ι) :
    s2v_l1b_etaleCoordinateDerivation A R ι j
      (algebraMap (MvPolynomial ι A) R (MvPolynomial.X k)) = if j = k then 1 else 0 := by
  change (s2v_l1b_etaleDifferentialBasis A R ι).coord j
    (KaehlerDifferential.D A R (algebraMap (MvPolynomial ι A) R (MvPolynomial.X k))) = _
  rw [← s2v_l1b_etaleDifferentialBasis_apply]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

end HodgeLean.Foundations.Program
