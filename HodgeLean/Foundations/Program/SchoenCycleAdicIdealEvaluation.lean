import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Finite evaluation and extended adic ideals -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite evaluation detects the extension of powers of a finitely generated
ideal to its adic ring.
Source: Mathlib, AdicCompletion.pow_smul_top_eq_ker_eval. -/
theorem s2e_adic_mem_extended_pow_iff_eval
    {R : Type*} [CommRing R] (I : Ideal R) (hfg : I.FG)
    (z : AdicCompletion I R) (N : ℕ) :
    z ∈ (I ^ N).map (algebraMap R (AdicCompletion I R)) ↔
      AdicCompletion.evalₐ I N z = 0 := by
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (hfg)]
  change AdicCompletion.eval I R N z = 0 ↔ _
  have h : (I ^ N • ⊤ : Ideal R) ≤
      I ^ N := by simp
  rw [← AdicCompletion.factor_eval_eq_evalₐ _ _ h]
  have hi : Function.Injective (Ideal.Quotient.factor h) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    rw [Ideal.Quotient.factor_ker]
    apply Ideal.map_mk_eq_bot_of_le
    simp
  exact (map_eq_zero_iff _ hi).symm


#print axioms s2e_adic_mem_extended_pow_iff_eval
end HodgeLean.Foundations.Program
