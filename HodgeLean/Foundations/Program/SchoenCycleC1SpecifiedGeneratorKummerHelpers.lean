import HodgeLean.Foundations.Program.SchoenCycleC1FullOrderFieldHelpers

/-! # Generic Kummer coordinates for the specified residual generator -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial IntermediateField
namespace HodgeLean.Foundations.Program

/-- A specified full-order automorphism has a nonzero Kummer eigenvector
with any prescribed primitive eigenvalue. -/
theorem s2e_c1_kummer_eigenvector_of_full_order
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (σ : L ≃ₐ[K] L) (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank K L = m) (horder : orderOf σ = m)
    (ζ : K) (hζ : IsPrimitiveRoot ζ m) :
    ∃ z : L, z ≠ 0 ∧ σ z = ζ • z ∧
      z ^ m ∈ Set.range (algebraMap K L) ∧ K⟮z⟯ = ⊤ := by
  obtain ⟨hG, hC⟩ := s2e_c1_galois_cyclic_of_full_order σ (horder.trans hdim.symm)
  letI := hG
  have hcard : Nat.card (L ≃ₐ[K] L) = m := (IsGalois.card_aut_eq_finrank K L).trans hdim
  have htop : Subgroup.zpowers σ = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_zpowers, horder, hcard])
  have hgen (τ : L ≃ₐ[K] L) : τ ∈ Subgroup.zpowers σ := by rw [htop]; trivial
  have hroot : IsRoot (minpoly K σ.toLinearMap) ζ := by
    simpa only [minpoly_algEquiv_toLinearMap σ (isOfFinOrder_of_finite σ), horder,
      IsRoot, eval_sub, eval_pow, eval_X, eval_one, eval_C, sub_eq_zero] using hζ.pow_eq_one
  obtain ⟨z, hz⟩ := (Module.End.hasEigenvalue_of_isRoot hroot).exists_hasEigenvector
  have hpowers := hz.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hpowers
  refine ⟨z, hz.2, hz.apply_eq_smul, ?_, ?_⟩
  · rw [← IntermediateField.mem_bot,
      ← OrderIso.map_bot IsGalois.intermediateFieldEquivSubgroup.symm]
    intro ⟨τ, hτ⟩
    obtain ⟨n, rfl : σ ^ n = τ⟩ := mem_powers_iff_mem_zpowers.mpr (hgen τ)
    rw [smul_pow', Submonoid.smul_def, AlgEquiv.smul_def, hpowers, smul_pow,
      ← pow_mul, mul_comm n m, pow_mul, hζ.pow_eq_one, one_pow, one_smul]
  · apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top, eq_top_iff]
    intro τ hτ
    obtain ⟨n, rfl : σ ^ n = τ⟩ := mem_powers_iff_mem_zpowers.mpr (hgen τ)
    have he := hτ ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
    simp only [AlgEquiv.smul_def, hpowers] at he
    have hζn : ζ ^ n = 1 := by
      apply smul_left_injective K hz.2
      simpa only [one_smul] using he
    obtain ⟨k, hk⟩ := hζ.dvd_of_pow_eq_one n hζn
    have hσm : σ ^ m = 1 := by rw [← horder]; exact pow_orderOf_eq_one σ
    rw [hk, pow_mul, hσm, one_pow]
    exact one_mem _

/-- A prescribed primitive eigenvalue of the specified generator can be
retained in a power basis with its exact Kummer minimal polynomial. -/
theorem s2e_c1_kummer_powerBasis_of_specified_generator
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (σ : L ≃ₐ[K] L) (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank K L = m) (horder : orderOf σ = m)
    (ζ : K) (hζ : IsPrimitiveRoot ζ m) :
    ∃ (B : PowerBasis K L) (c : K),
      minpoly K B.gen = X ^ m - C c ∧
      B.gen ^ m = algebraMap K L c ∧ σ B.gen = ζ • B.gen := by
  obtain ⟨z, _, hσ, ⟨c, hc⟩, hgen⟩ :=
    s2e_c1_kummer_eigenvector_of_full_order σ m hm hdim horder ζ hζ
  have htop : Algebra.adjoin K ({z} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsAlgebraic.of_finite K z), hgen, IntermediateField.top_toSubalgebra]
  let B := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite K z) htop
  have hmin : minpoly K z = X ^ m - C c := by
    have hi := irreducible_X_pow_sub_C_of_root_adjoin_eq_top
      (by simpa only [hdim] using hc.symm) hgen
    apply (minpoly.eq_of_irreducible_of_monic (by simpa only [hdim] using hi) ?_
      (monic_X_pow_sub_C c (Nat.ne_of_gt hm))).symm
    simp only [map_sub, map_pow, aeval_X, aeval_C, ← hc, sub_self]
  exact ⟨B, c, hmin, hc.symm, hσ⟩


end HodgeLean.Foundations.Program
