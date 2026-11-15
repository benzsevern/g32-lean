import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import Mathlib.Algebra.Polynomial.OfFn
import HodgeLean.Foundations.Program.SchoenCycleC11LocalInverseHelpers
import HodgeLean.Foundations.Port.Analysis.Complex.Polynomial.HolomorphicFactor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.Program

/-- An individual simple root makes the root-direction derivative invertible.
Source: Polynomial.fderiv_mvFamilyEquation_comp_inr and ContinuousLinearEquiv.unitsEquivAut. -/
theorem s2e_c11_polynomial_rootDirection_invertible
    {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) (z : (Fin n → ℂ) × ℂ)
    (hz : (Polynomial.mvFamilySpecialization p z.1).derivative.eval z.2 ≠ 0) :
    (fderiv ℂ (Polynomial.mvFamilyEquation p) z ∘L
      ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).IsInvertible := by
  rw [Polynomial.fderiv_mvFamilyEquation_comp_inr]
  exact ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hz), rfl⟩

/-- Projection from a polynomial zero locus is locally invertible at every individual simple root.
Source: Mathlib, implicit-function theorem; Polynomial.hasStrictFDerivAt_mvFamilyEquation. -/
theorem s2e_c11_polynomial_regular_projection
    {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :
    IsLocalHomeomorphOn
      (fun z : {z : (Fin n → ℂ) × ℂ // Polynomial.mvFamilyEquation p z = 0} => z.1.1)
      {z | (Polynomial.mvFamilySpecialization p z.1.1).derivative.eval z.1.2 ≠ 0} := by
  apply s2e_c11_implicit_zero_projection
  intro z hz
  exact ⟨_, Polynomial.hasStrictFDerivAt_mvFamilyEquation p z.1,
    s2e_c11_polynomial_rootDirection_invertible p z.1 hz⟩

/-- The polynomial with independent coefficient parameters of a fixed finite length.
Source: Mathlib, Polynomial.ofFn and multivariable polynomial coordinates. -/
def s2e_c11_universalCoefficientPolynomial (n : ℕ) : Polynomial (MvPolynomial (Fin n) ℂ) :=
  Polynomial.ofFn n (fun i => MvPolynomial.X i)

/-- Coefficient evaluations provide the continuous parameter map for an arbitrary complex algebra.
Source: ComplexPoint.continuous_affineAlgebraHom_apply and product topology. -/
def s2e_c11_coefficientParameters
    {A : Type} [CommRing A] [Algebra ℂ A] (p : Polynomial A) :
    (A →ₐ[ℂ] ℂ) → (Fin (p.natDegree + 1) → ℂ) := fun ψ i => ψ (p.coeff i)

/-- The coefficient parameter map is continuous for pointwise convergence.
Source: ComplexPoint.continuous_affineAlgebraHom_apply. -/
theorem s2e_c11_coefficientParameters_continuous
    {A : Type} [CommRing A] [Algebra ℂ A] (p : Polynomial A) :
    Continuous (s2e_c11_coefficientParameters p) := by
  exact continuous_pi (fun i =>
    AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply A (p.coeff i))

/-- Specializing the independent coefficients recovers the given algebra polynomial.
Source: Mathlib, Polynomial.ofFn coefficient identities and Polynomial.coeff_map. -/
theorem s2e_c11_universalCoefficient_specialization
    {A : Type} [CommRing A] [Algebra ℂ A] (p : Polynomial A) (ψ : A →ₐ[ℂ] ℂ) :
    Polynomial.mvFamilySpecialization (s2e_c11_universalCoefficientPolynomial (p.natDegree + 1))
      (s2e_c11_coefficientParameters p ψ) = p.map ψ.toRingHom := by
  ext i
  by_cases hi : i < p.natDegree + 1
  · simp only [Polynomial.mvFamilySpecialization, s2e_c11_universalCoefficientPolynomial,
      Polynomial.coeff_map, Polynomial.ofFn_coeff_eq_val_of_lt _ hi,
      MvPolynomial.eval_X, s2e_c11_coefficientParameters]
    rfl
  · have hpi : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [Polynomial.mvFamilySpecialization, s2e_c11_universalCoefficientPolynomial,
      Polynomial.coeff_map, Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega : p.natDegree + 1 ≤ i),
      map_zero, hpi]

/-- The actual root locus of a polynomial over complex algebra homomorphisms.
Source: Hartshorne, Algebraic Geometry, Appendix B, relative polynomial equation loci. -/
abbrev s2e_c11_relativeRootLocus
    {A : Type} [CommRing A] [Algebra ℂ A] (p : Polynomial A) :=
  {z : (A →ₐ[ℂ] ℂ) × ℂ // Polynomial.eval₂ z.1.toRingHom z.2 p = 0}

/-- An arbitrary coefficient-algebra root locus is the continuous base change of the universal family.
Source: Mathlib, polynomial coefficient specialization and subtype product topology. -/
def s2e_c11_relativeRootPullbackHomeomorph
    {A : Type} [CommRing A] [Algebra ℂ A] (p : Polynomial A) :
    {q : (A →ₐ[ℂ] ℂ) ×
      {z : (Fin (p.natDegree + 1) → ℂ) × ℂ //
        Polynomial.mvFamilyEquation (s2e_c11_universalCoefficientPolynomial (p.natDegree + 1)) z = 0} //
      s2e_c11_coefficientParameters p q.1 = q.2.1.1} ≃ₜ s2e_c11_relativeRootLocus p where
  toFun q := ⟨(q.1.1, q.1.2.1.2), by
    have h := q.1.2.2
    change (Polynomial.mvFamilySpecialization
      (s2e_c11_universalCoefficientPolynomial (p.natDegree + 1)) q.1.2.1.1).eval q.1.2.1.2 = 0 at h
    rw [← q.2, s2e_c11_universalCoefficient_specialization, Polynomial.eval_map] at h
    exact h⟩
  invFun z := ⟨(z.1.1, ⟨(s2e_c11_coefficientParameters p z.1.1, z.1.2), by
    change (Polynomial.mvFamilySpecialization
      (s2e_c11_universalCoefficientPolynomial (p.natDegree + 1))
        (s2e_c11_coefficientParameters p z.1.1)).eval z.1.2 = 0
    rw [s2e_c11_universalCoefficient_specialization, Polynomial.eval_map]
    exact z.2⟩), rfl⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · exact q.2
      · rfl
  right_inv z := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (continuous_fst.comp continuous_subtype_val).prodMk
    apply Continuous.subtype_mk
    exact ((s2e_c11_coefficientParameters_continuous p).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        (continuous_snd.comp continuous_subtype_val)

/-- Relative polynomial projection is locally invertible at simple roots over any complex algebra.
Source: Mathlib, implicit-function theorem and continuous base change of polynomial root loci. -/
theorem s2e_c11_relativeRoot_regular_projection
    {A : Type} [CommRing A] [Algebra ℂ A] (p : Polynomial A) :
    IsLocalHomeomorphOn (fun z : s2e_c11_relativeRootLocus p => z.1.1)
      {z | Polynomial.eval₂ z.1.1.toRingHom z.1.2 p.derivative ≠ 0} := by
  let P := s2e_c11_universalCoefficientPolynomial (p.natDegree + 1)
  let h := s2e_c11_relativeRootPullbackHomeomorph p
  have hp := s2e_c11_localHomeomorphOn_baseChange
    (fun z : {z : (Fin (p.natDegree + 1) → ℂ) × ℂ // Polynomial.mvFamilyEquation P z = 0} => z.1.1)
    _ (s2e_c11_polynomial_regular_projection P) (s2e_c11_coefficientParameters p)
    (s2e_c11_coefficientParameters_continuous p)
  have hset : {q : {q : (A →ₐ[ℂ] ℂ) ×
      {z : (Fin (p.natDegree + 1) → ℂ) × ℂ // Polynomial.mvFamilyEquation P z = 0} //
        s2e_c11_coefficientParameters p q.1 = q.2.1.1} |
      (Polynomial.mvFamilySpecialization P q.1.2.1.1).derivative.eval q.1.2.1.2 ≠ 0} =
      h ⁻¹' {z | Polynomial.eval₂ z.1.1.toRingHom z.1.2 p.derivative ≠ 0} := by
    ext q
    change (Polynomial.mvFamilySpecialization P q.1.2.1.1).derivative.eval q.1.2.1.2 ≠ 0 ↔
      Polynomial.eval₂ q.1.1.toRingHom q.1.2.1.2 p.derivative ≠ 0
    rw [← q.2, s2e_c11_universalCoefficient_specialization,
      Polynomial.derivative_map, Polynomial.eval_map]
  simp only [Set.mem_setOf_eq] at hp
  rw [hset] at hp
  change IsLocalHomeomorphOn
    ((fun z : s2e_c11_relativeRootLocus p => z.1.1) ∘ h) _ at hp
  have ht := hp.of_comp_right h.isLocalHomeomorph.isLocalHomeomorphOn
  intro z hz
  exact ht z ⟨h.symm z, by
    change h (h.symm z) ∈
      {z : s2e_c11_relativeRootLocus p | Polynomial.eval₂ z.1.1.toRingHom z.1.2 p.derivative ≠ 0}
    rw [h.apply_symm_apply]
    exact hz, h.apply_symm_apply z⟩

end HodgeLean.Foundations.Program
