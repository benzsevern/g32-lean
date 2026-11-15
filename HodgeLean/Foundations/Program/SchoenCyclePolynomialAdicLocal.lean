import HodgeLean.Foundations.Program.SchoenCycleAdicIdealEvaluation
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Analysis.Complex.Basic

/-! # The local structure of the polynomial adic ring -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The variable ideal is the kernel of the constant-coefficient map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1;
Mathlib, MvPolynomial.mem_pow_idealOfVars_iff'. -/
theorem s2e_idealOfVars_eq_ker_constantCoeff
    (R ι : Type*) [CommRing R] :
    idealOfVars ι R = RingHom.ker (constantCoeff : MvPolynomial ι R →+* R) := by
  ext p
  change p ∈ idealOfVars ι R ↔ constantCoeff p = 0
  rw [← pow_one (idealOfVars ι R), mem_pow_idealOfVars_iff']
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have he : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    exact h

#print axioms s2e_idealOfVars_eq_ker_constantCoeff
/-- The polynomial variable ideal over the complex numbers is maximal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1;
the quotient is the coefficient field. -/
theorem s2e_idealOfVars_complex_isMaximal (ι : Type*) :
    (idealOfVars ι ℂ).IsMaximal := by
  rw [s2e_idealOfVars_eq_ker_constantCoeff]
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨C c, by simp⟩

#print axioms s2e_idealOfVars_complex_isMaximal
/-- The adic ring of complex polynomials at the variable ideal is local.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, isLocalRing_of_isAdicComplete_maximal. -/
instance s2e_polynomial_adic_isLocalRing (ι : Type*) [Finite ι] :
    IsLocalRing (AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) := by
  let I := idealOfVars ι ℂ
  letI : I.IsMaximal := s2e_idealOfVars_complex_isMaximal ι
  letI : (I.map (algebraMap (MvPolynomial ι ℂ) (AdicCompletion I (MvPolynomial ι ℂ)))).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le I I le_rfl (idealOfVars_fg ι ℂ)
  letI := AdicCompletion.isAdicComplete_self I (idealOfVars_fg ι ℂ)
  exact isLocalRing_of_isAdicComplete_maximal
    (I.map (algebraMap (MvPolynomial ι ℂ) (AdicCompletion I (MvPolynomial ι ℂ))))

#print axioms s2e_polynomial_adic_isLocalRing
/-- The maximal ideal of the polynomial adic ring is the extended variable ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10;
Mathlib, AdicCompletion.isMaximal_map_of_le. -/
theorem s2e_polynomial_adic_maximalIdeal (ι : Type*) [Finite ι] :
    IsLocalRing.maximalIdeal (AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) =
      (idealOfVars ι ℂ).map
        (algebraMap (MvPolynomial ι ℂ) (AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ))) := by
  letI := s2e_idealOfVars_complex_isMaximal ι
  exact (IsLocalRing.eq_maximalIdeal
    (AdicCompletion.isMaximal_map_of_le _ _ le_rfl (idealOfVars_fg ι ℂ))).symm

#print axioms s2e_polynomial_adic_maximalIdeal
/-- Order-one vanishing detects the maximal ideal in the polynomial adic ring.
Source: Mathlib, AdicCompletion.pow_smul_top_eq_ker_eval. -/
theorem s2e_polynomial_adic_mem_maximalIdeal_iff_eval
    (ι : Type*) [Finite ι]
    (z : AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) :
    z ∈ IsLocalRing.maximalIdeal (AdicCompletion (idealOfVars ι ℂ) (MvPolynomial ι ℂ)) ↔
      AdicCompletion.evalₐ (idealOfVars ι ℂ) 1 z = 0 := by
  rw [s2e_polynomial_adic_maximalIdeal]
  simpa only [pow_one] using
    s2e_adic_mem_extended_pow_iff_eval (idealOfVars ι ℂ) (idealOfVars_fg ι ℂ) z 1

#print axioms s2e_polynomial_adic_mem_maximalIdeal_iff_eval
end HodgeLean.Foundations.Program
