import HodgeLean.Foundations.Program.SchoenCyclePolynomialDifferentialEtale
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.MvPolynomial.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Prescribed functions with a differential basis define an actual étale polynomial coordinate map for a smooth algebra of finite type over a Noetherian base.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1. -/
theorem s2e_prescribed_polynomial_etale_of_differential_basis
    (R A σ : Type*) [CommRing R] [IsNoetherianRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] [Finite σ]
    [Subsingleton (Algebra.H1Cotangent R A)]
    (c : σ → A) (b : Module.Basis σ A Ω[A⁄R]) (hb : ∀ i, b i = D R A (c i)) :
    (aeval (R := R) c).toRingHom.Etale := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  let f : MvPolynomial σ R →ₐ[R] A := aeval c
  letI : Algebra (MvPolynomial σ R) A := f.toAlgebra
  letI : IsScalarTower R (MvPolynomial σ R) A :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : Algebra.FiniteType (MvPolynomial σ R) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (MvPolynomial σ R) A
  letI : Algebra.FinitePresentation (MvPolynomial σ R) A :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  letI : Algebra.FormallyEtale (MvPolynomial σ R) A :=
    s2e_polynomial_formallyEtale_of_differential_basis R A σ b (by
      intro i
      change b i = D R A ((aeval (R := R) c) (X i))
      rw [aeval_X]
      exact hb i)
  exact RingHom.etale_algebraMap.mpr (show Algebra.Etale (MvPolynomial σ R) A from ⟨inferInstance, inferInstance⟩)

#print axioms s2e_prescribed_polynomial_etale_of_differential_basis
end HodgeLean.Foundations.Program
