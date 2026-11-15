import HodgeLean.Foundations.Program.SchoenCycleDifferentialEtaleCriterion
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- Prescribed polynomial coordinates whose differentials form a basis give a formally étale algebra when the first cotangent homology over the base vanishes.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1; the Jacobi–Zariski exact sequence. -/
theorem s2e_polynomial_formallyEtale_of_differential_basis
    (R T σ : Type*) [CommRing R] [CommRing T]
    [Algebra R T] [Algebra (MvPolynomial σ R) T]
    [IsScalarTower R (MvPolynomial σ R) T]
    [Subsingleton (Algebra.H1Cotangent R T)]
    (b : Module.Basis σ T Ω[T⁄R])
    (hb : ∀ i, b i = D R T (algebraMap (MvPolynomial σ R) T (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial σ R) T := by
  apply s2e_formallyEtale_of_differential_baseChange_bijective R (MvPolynomial σ R) T
  let c := (mvPolynomialBasis R σ).baseChange T
  have he : mapBaseChange R (MvPolynomial σ R) T = (c.equiv b (Equiv.refl σ)).toLinearMap := by
    apply c.ext
    intro i
    change mapBaseChange R (MvPolynomial σ R) T (c i) = c.equiv b (Equiv.refl σ) (c i)
    rw [Module.Basis.equiv_apply]
    simp only [c, Module.Basis.baseChange_apply, mvPolynomialBasis_apply,
      mapBaseChange_tmul, one_smul, map_D, Module.Basis.equiv_apply, Equiv.refl_apply, hb]
  rw [he]
  exact (c.equiv b (Equiv.refl σ)).bijective

#print axioms s2e_polynomial_formallyEtale_of_differential_basis
end HodgeLean.Foundations.Program
