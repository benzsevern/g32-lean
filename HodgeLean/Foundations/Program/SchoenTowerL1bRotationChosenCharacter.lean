import Mathlib.FieldTheory.KummerExtension
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Norm.Basic

noncomputable section
set_option maxHeartbeats 400000
open Module Polynomial Subgroup
namespace HodgeLean.Foundations.Program

/-- A specified generator of the actual Galois group has a binomial generator
with any prescribed primitive base-field character. -/
theorem s2v_l1b_rotation_chosen_character_generator
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (τ : K ≃ₐ[F] K) (hτ : ∀ u, u ∈ zpowers τ)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (finrank F K)) :
    ∃ t : K, t ≠ 0 ∧ τ t = ζ • t ∧
      t ^ finrank F K ∈ Set.range (algebraMap F K) ∧
      IntermediateField.adjoin F {t} = ⊤ := by
  have horder := orderOf_eq_card_of_forall_mem_zpowers hτ
  rw [IsGalois.card_aut_eq_finrank] at horder
  have hroot : IsRoot (minpoly F τ.toLinearMap) ζ := by
    simpa [minpoly_algEquiv_toLinearMap τ (isOfFinOrder_of_finite τ), horder,
      sub_eq_zero] using hζ.pow_eq_one
  obtain ⟨t, ht⟩ := (Module.End.hasEigenvalue_of_isRoot hroot).exists_hasEigenvector
  have hiterate := ht.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hiterate
  refine ⟨t, ht.2, ?_, ?_, ?_⟩
  · simpa only [pow_one] using hiterate 1
  · rw [← IntermediateField.mem_bot,
      ← OrderIso.map_bot IsGalois.intermediateFieldEquivSubgroup.symm]
    intro ⟨u, hu⟩
    obtain ⟨n, rfl : τ ^ n = u⟩ := mem_powers_iff_mem_zpowers.mpr (hτ u)
    rw [smul_pow', Submonoid.smul_def, AlgEquiv.smul_def, hiterate, smul_pow,
      ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, one_smul]
  · apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [OrderIso.map_top, eq_top_iff]
    intro u hu
    obtain ⟨n, rfl : τ ^ n = u⟩ := mem_powers_iff_mem_zpowers.mpr (hτ u)
    have heq := hu ⟨t, IntermediateField.mem_adjoin_simple_self F t⟩
    simp only [AlgEquiv.smul_def, hiterate] at heq
    conv_rhs at heq => rw [← one_smul F t]
    obtain ⟨k, rfl⟩ := hζ.dvd_of_pow_eq_one n (smul_left_injective F ht.2 heq)
    rw [pow_mul, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', one_pow]
    exact one_mem _

/-- Exact degree order suffices to select a binomial generator for the specified action. -/
theorem s2v_l1b_rotation_degree_order_character_generator
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (τ : K ≃ₐ[F] K) (hτ : orderOf τ = finrank F K)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (finrank F K)) :
    ∃ t : K, t ≠ 0 ∧ τ t = ζ • t ∧
      t ^ finrank F K ∈ Set.range (algebraMap F K) ∧
      IntermediateField.adjoin F {t} = ⊤ := by
  have htop : zpowers τ = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (zpowers τ)).mp
    rw [Nat.card_zpowers, hτ, IsGalois.card_aut_eq_finrank]
  apply s2v_l1b_rotation_chosen_character_generator τ _ hζ
  intro u
  rw [htop]
  exact Subgroup.mem_top u

end HodgeLean.Foundations.Program
