import HodgeLean.Foundations.Program.SchoenCycleC1SpecifiedGeneratorKummerHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial IntermediateField
namespace HodgeLean.Foundations.Program

/-- A specified nonzero primitive eigenvector itself is the Kummer power
basis generator, retaining its specified coefficient and exact equation. -/
theorem s2e_c1_kummer_powerBasis_of_specified_eigenvector
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (σ : L ≃ₐ[K] L) (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank K L = m) (horder : orderOf σ = m)
    (ζ : K) (hζ : IsPrimitiveRoot ζ m) (z : L) (hz : z ≠ 0)
    (heig : σ z = ζ • z) (c : K) (hpower : z ^ m = algebraMap K L c) :
    ∃ B : PowerBasis K L, B.gen = z ∧ minpoly K B.gen = X ^ m - C c := by
  obtain ⟨hG, _⟩ := s2e_c1_galois_cyclic_of_full_order σ (horder.trans hdim.symm)
  letI := hG
  have hcard : Nat.card (L ≃ₐ[K] L) = m := (IsGalois.card_aut_eq_finrank K L).trans hdim
  have htop : Subgroup.zpowers σ = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_zpowers, horder, hcard])
  have hgen (τ : L ≃ₐ[K] L) : τ ∈ Subgroup.zpowers σ := by rw [htop]; trivial
  have hvec : Module.End.HasEigenvector σ.toLinearMap ζ z :=
    ⟨Module.End.mem_eigenspace_iff.mpr heig, hz⟩
  have hpowers := hvec.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hpowers
  have hzgen : K⟮z⟯ = ⊤ := by
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top, eq_top_iff]
    intro τ hτ
    obtain ⟨n, rfl : σ ^ n = τ⟩ := mem_powers_iff_mem_zpowers.mpr (hgen τ)
    have he := hτ ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
    simp only [AlgEquiv.smul_def, hpowers] at he
    have hζn : ζ ^ n = 1 := by
      apply smul_left_injective K hz
      simpa only [one_smul] using he
    obtain ⟨k, hk⟩ := hζ.dvd_of_pow_eq_one n hζn
    have hσm : σ ^ m = 1 := by rw [← horder]; exact pow_orderOf_eq_one σ
    rw [hk, pow_mul, hσm, one_pow]
    exact one_mem _
  have hadjoin : Algebra.adjoin K ({z} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsAlgebraic.of_finite K z), hzgen, IntermediateField.top_toSubalgebra]
  let B := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite K z) hadjoin
  refine ⟨B, rfl, ?_⟩
  have hi := irreducible_X_pow_sub_C_of_root_adjoin_eq_top
    (by simpa only [hdim] using hpower) hzgen
  apply (minpoly.eq_of_irreducible_of_monic (by simpa only [hdim] using hi) ?_
    (monic_X_pow_sub_C c (Nat.ne_of_gt hm))).symm
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  change z ^ m - algebraMap K L c = 0
  exact sub_eq_zero.mpr hpower

end HodgeLean.Foundations.Program
