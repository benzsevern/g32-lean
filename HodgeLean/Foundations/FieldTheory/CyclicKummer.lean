import HodgeLean.Foundations.FieldTheory.CyclicKummerProofs

/-! Cyclic field and eigenfunction contracts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace FieldTheory.CyclicKummer

/-- Eigenfunction powers belong to the fixed field.
Source: Mathlib, FieldTheory.KummerExtension, exists_root_adjoin_eq_top_of_isCyclic; SchoenTowerI2aFieldHelpers.s2v_i2a_aut_pow_generator. -/
theorem eigenfunction_power_fixed
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (m : ℕ) (hm : 0 < m) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (τ : E ≃ₐ[F] E) (v : E) (hv : τ v = algebraMap F E ζ * v) :
    v ^ m ∈ IntermediateField.fixedField (Subgroup.zpowers τ) :=
  eigenfunction_power_fixed_aux F E m hm ζ hζ τ v hv

/-- A generator whose fixed field is the base determines the cyclic degree.
Source: Mathlib, FieldTheory.Galois.Basic, IntermediateField.finrank_fixedField_eq_card; SchoenTowerL1bKummerDegree.s2v_l1b_degree_of_fixed_generator. -/
theorem degree_of_fixed_generator
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (τ : E ≃ₐ[F] E)
    (hfix : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥) :
    IsGalois F E ∧ IsCyclic (E ≃ₐ[F] E) ∧ Module.finrank F E = orderOf τ :=
  degree_of_fixed_generator_aux F E τ hfix

/-- A generating primitive eigenfunction gives the exact binomial and degree.
Source: Mathlib, FieldTheory.KummerExtension, irreducible_X_pow_sub_C_of_root_adjoin_eq_top; SchoenTowerI2aBinomialDegree.s2v_i2a_binomial_irreducible; SchoenCycleC1ActualCoverKummerProofs.s2e_c1_actual_cover_generic_kummer. -/
theorem degree_of_primitive_eigenfunction
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (m : ℕ) (hm : 0 < m) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (τ : E ≃ₐ[F] E) (v : E) (hv : v ≠ 0)
    (hτ : τ v = algebraMap F E ζ * v)
    (c : F) (hc : v ^ m = algebraMap F E c)
    (hgen : IntermediateField.adjoin F {v} = ⊤) :
    minpoly F v = Polynomial.X ^ m - Polynomial.C c ∧
      Module.finrank F E = m :=
  degree_of_primitive_eigenfunction_aux F E m hm ζ hζ τ v hv hτ c hc hgen

-- The real quadratic extension has a cyclic group of order two.
example : Module.finrank ℝ ℂ = 2 ∧ IsGalois ℝ ℂ ∧ IsCyclic (ℂ ≃ₐ[ℝ] ℂ) := by
  letI : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
  refine ⟨Complex.finrank_real_complex, inferInstance, ?_⟩
  apply isCyclic_of_prime_card (p := 2)
  rw [IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]

-- Conjugation moves the nonzero eigenfunction I by the primitive scalar -1.
example : IsPrimitiveRoot (-1 : ℝ) 2 ∧ Complex.I ≠ 0 ∧
    Complex.conjAe Complex.I = algebraMap ℝ ℂ (-1) * Complex.I ∧
    Complex.conjAe ≠ (1 : ℂ ≃ₐ[ℝ] ℂ) ∧ Complex.I ^ 2 = (-1 : ℂ) := by
  refine ⟨IsPrimitiveRoot.neg_one 0 (by norm_num), Complex.I_ne_zero, ?_, ?_,
    Complex.I_sq⟩
  · simp
  · intro h
    have hI := DFunLike.congr_fun h Complex.I
    have hi := congrArg Complex.im hI
    norm_num at hi

-- The eigenfunction square is fixed under the non-identity action.
example : Complex.conjAe (Complex.I ^ 2) = Complex.I ^ 2 := by
  simp [Complex.I_sq]

-- A nonzero period-one generator checks the binomial normalization.
example : minpoly ℚ (2 : ℚ) = Polynomial.X ^ 1 - Polynomial.C 2 ∧
    Module.finrank ℚ ℚ = 1 := by
  constructor
  · simpa using minpoly.eq_X_sub_C_of_algebraMap_inj
      (B := ℚ) (2 : ℚ) (Function.injective_id)
  · exact Module.finrank_self ℚ

end FieldTheory.CyclicKummer
