import HodgeLean.Foundations.FieldTheory.CyclicKummerChecks
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Galois.Basic

/-! Auxiliary cyclic field and eigenfunction contracts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace FieldTheory.CyclicKummer

/-- Eigenfunction powers belong to the fixed field.
Source: Mathlib, FieldTheory.KummerExtension, exists_root_adjoin_eq_top_of_isCyclic; SchoenTowerI2aFieldHelpers.s2v_i2a_aut_pow_generator. -/
theorem eigenfunction_power_fixed_aux
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (m : ℕ) (hm : 0 < m) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (τ : E ≃ₐ[F] E) (v : E) (hv : τ v = algebraMap F E ζ * v) :
    v ^ m ∈ IntermediateField.fixedField (Subgroup.zpowers τ) := by
  have hfixed : τ (v ^ m) = v ^ m := by
    rw [map_pow, hv, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul]
  have hle : Subgroup.zpowers τ ≤ MulAction.stabilizer (E ≃ₐ[F] E) (v ^ m) :=
    Subgroup.zpowers_le.mpr hfixed
  rw [IntermediateField.mem_fixedField_iff]
  intro g hg
  exact hle hg

/-- A generator whose fixed field is the base determines the cyclic degree.
Source: Mathlib, FieldTheory.Galois.Basic, IntermediateField.finrank_fixedField_eq_card; SchoenTowerL1bKummerDegree.s2v_l1b_degree_of_fixed_generator. -/
theorem degree_of_fixed_generator_aux
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (τ : E ≃ₐ[F] E)
    (hfix : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥) :
    IsGalois F E ∧ IsCyclic (E ≃ₐ[F] E) ∧ Module.finrank F E = orderOf τ := by
  let H := Subgroup.zpowers τ
  have htop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hfix]
    exact IntermediateField.fixingSubgroup_bot
  haveI : IsGalois F E := IsGalois.of_fixedField_eq_bot F E (htop ▸ hfix)
  haveI : IsCyclic (E ≃ₐ[F] E) := by
    haveI : IsCyclic (⊤ : Subgroup (E ≃ₐ[F] E)) := htop ▸ inferInstance
    exact isCyclic_of_surjective (⊤ : Subgroup (E ≃ₐ[F] E)).subtype
      (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  refine ⟨inferInstance, inferInstance, ?_⟩
  calc
    Module.finrank F E = Nat.card H := by
      rw [← IntermediateField.finrank_fixedField_eq_card H, hfix]
      exact IntermediateField.finrank_bot'.symm
    _ = orderOf τ := Nat.card_zpowers τ

/-- A generating primitive eigenfunction gives the exact binomial and degree.
Source: Mathlib, FieldTheory.KummerExtension, irreducible_X_pow_sub_C_of_root_adjoin_eq_top; SchoenTowerI2aBinomialDegree.s2v_i2a_binomial_irreducible; SchoenCycleC1ActualCoverKummerProofs.s2e_c1_actual_cover_generic_kummer. -/
theorem degree_of_primitive_eigenfunction_aux
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (m : ℕ) (hm : 0 < m) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (τ : E ≃ₐ[F] E) (v : E) (hv : v ≠ 0)
    (hτ : τ v = algebraMap F E ζ * v)
    (c : F) (hc : v ^ m = algebraMap F E c)
    (hgen : IntermediateField.adjoin F {v} = ⊤) :
    minpoly F v = Polynomial.X ^ m - Polynomial.C c ∧
      Module.finrank F E = m := by
  have hroot : Polynomial.aeval v (Polynomial.X ^ m - Polynomial.C c) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hc, sub_self]
  have hint : IsIntegral F v := ⟨_, Polynomial.monic_X_pow_sub_C c hm.ne', hroot⟩
  have hpow (i : ℕ) : (τ ^ i) v = algebraMap F E ζ ^ i * v := by
    induction i with
    | zero => simp only [pow_zero, AlgEquiv.one_apply, one_mul]
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow,
        τ.commutes, hτ, pow_succ]
      ac_rfl
  have horbit : Function.Injective (fun i : Fin m => (τ ^ i.val) v) := by
    have hz := hζ.map_of_injective (algebraMap F E).injective
    intro i j hij
    apply Fin.ext
    apply hz.pow_inj i.isLt j.isLt
    apply mul_right_cancel₀ hv
    simpa only [hpow] using hij
  have hdegree : m ≤ (minpoly F v).natDegree := by
    by_contra hdeg
    have hroots : ∀ i : Fin m,
        ((minpoly F v).map (algebraMap F E)).eval ((τ ^ i.val) v) = 0 := by
      intro i
      rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply,
        minpoly.aeval, map_zero]
    have hlt : ((minpoly F v).map (algebraMap F E)).natDegree <
        Fintype.card (Fin m) := by
      simpa only [Fintype.card_fin] using
        lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_of_not_ge hdeg)
    have H := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      _ horbit hroots hlt
    exact ((Polynomial.map_ne_zero_iff (algebraMap F E).injective).mpr
      (minpoly.ne_zero hint)) H
  have hmin : minpoly F v = Polynomial.X ^ m - Polynomial.C c := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.monic_X_pow_sub_C c hm.ne') (minpoly.dvd F v hroot)
    simpa only [Polynomial.natDegree_X_pow_sub_C] using hdegree
  refine ⟨hmin, ?_⟩
  have H := IntermediateField.adjoin.finrank hint
  rw [hgen, IntermediateField.finrank_top', hmin,
    Polynomial.natDegree_X_pow_sub_C] at H
  exact H

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
