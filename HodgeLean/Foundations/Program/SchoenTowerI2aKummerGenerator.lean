import HodgeLean.Foundations.Program.SchoenTowerI2aFieldHelpers
import Mathlib.FieldTheory.KummerExtension

/-! # Choosing an original-field Kummer eigenvector
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite-order field automorphism has a nonzero eigenvector for every primitive root of its order in the base field.
Source: Mathlib, minpoly_algEquiv_toLinearMap and Module.End.hasEigenvalue_of_isRoot. -/
theorem s2v_i2a_kummer_eigenvector
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (m : ℕ) (hm : 0 < m) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[F] K) (hd : orderOf d = m) :
    ∃ v : K, v ≠ 0 ∧ d v = algebraMap F K ζ * v := by
  have hfinite : IsOfFinOrder d := orderOf_pos_iff.mp (by rw [hd]; exact hm)
  have hroot : Polynomial.IsRoot (minpoly F d.toLinearMap) ζ := by
    simpa [minpoly_algEquiv_toLinearMap d hfinite, hd, sub_eq_zero] using hζ.pow_eq_one
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot hroot).exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  simpa only [AlgEquiv.toLinearMap_apply, Algebra.smul_def] using hv.apply_eq_smul

/-- A primitive eigenvector for a specified cyclic Galois generator generates the original extension and has its m-th power in the base field.
Source: Mathlib, IsGalois.intermediateFieldEquivSubgroup and primitive eigenvector orbits. -/
theorem s2v_i2a_cyclic_kummer_generator
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (m : ℕ) (hm : 0 < m) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[F] K) (hd : orderOf d = m)
    (hcyc : ∀ σ : K ≃ₐ[F] K, σ ∈ Subgroup.zpowers d) :
    ∃ (v : K) (a : F), v ≠ 0 ∧ d v = algebraMap F K ζ * v ∧
      v ^ m = algebraMap F K a ∧
      Subfield.closure (Set.range (algebraMap F K) ∪ {v}) = ⊤ := by
  obtain ⟨v, hvne, hdv⟩ := s2v_i2a_kummer_eigenvector m hm ζ hζ d hd
  have hζK : (algebraMap F K ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hvbase : v ^ m ∈ Set.range (algebraMap F K) := by
    rw [← IntermediateField.mem_bot,
      ← OrderIso.map_bot IsGalois.intermediateFieldEquivSubgroup.symm]
    intro ⟨σ, hσ⟩
    obtain ⟨n, rfl : d ^ n = σ⟩ := mem_powers_iff_mem_zpowers.mpr (hcyc σ)
    change (d ^ n) (v ^ m) = v ^ m
    rw [map_pow, s2v_i2a_aut_pow_generator d v ζ hdv n, mul_pow, ← pow_mul,
      Nat.mul_comm n m, pow_mul, hζK, one_pow, one_mul]
  have hadjoin : IntermediateField.adjoin F ({v} : Set K) = ⊤ := by
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top, eq_top_iff]
    intro σ hσ
    obtain ⟨n, rfl : d ^ n = σ⟩ := mem_powers_iff_mem_zpowers.mpr (hcyc σ)
    have H := hσ ⟨v, IntermediateField.mem_adjoin_simple_self F v⟩
    change (d ^ n) v = v at H
    rw [s2v_i2a_aut_pow_generator d v ζ hdv n] at H
    have hζn : ζ ^ n = 1 := by
      apply (algebraMap F K).injective
      rw [map_pow, map_one]
      apply mul_right_cancel₀ hvne
      simpa only [one_mul] using H
    obtain ⟨k, rfl⟩ := hζ.dvd_of_pow_eq_one n hζn
    have hperiod : d ^ m = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
    rw [pow_mul, hperiod, one_pow]
    exact one_mem _
  obtain ⟨a, ha⟩ := hvbase
  refine ⟨v, a, hvne, hdv, ha.symm, ?_⟩
  exact congrArg IntermediateField.toSubfield hadjoin

end HodgeLean.Foundations.Program
