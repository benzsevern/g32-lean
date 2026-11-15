import HodgeLean.Foundations.Program.G32Native.TypeIIIQuaternionPure

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- A positive involution on a definite quaternion algebra is canonical
conjugation. Positivity is measured by any rational linear functional. -/
theorem typeIII_positive_involution (b : ℚ) (hb : b < 0)
    (R : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] (ℍ[ℚ, -3, 0, b])ᵐᵒᵖ)
    (hR : ∀ q, (R ((R q).unop)).unop = q)
    (τ : ℍ[ℚ, -3, 0, b] →ₗ[ℚ] ℚ)
    (hpos : ∀ q, q ≠ 0 → 0 < τ (q * (R q).unop)) :
    ∀ q, (R q).unop = star q := by
  have hτ : 0 < τ 1 := by simpa using hpos 1 one_ne_zero
  have hpure (q : ℍ[ℚ, -3, 0, b]) (hq : q.re = 0) : (R q).unop = -q := by
    by_cases hq0 : q = 0
    · simp [hq0]
    have hn := typeIIIQuaternionNorm_pos b hb q hq0
    have hsquare : (R q).unop * (R q).unop =
        algebraMap ℚ _ (-typeIIIQuaternionNorm b q) := by
      have h := congrArg (fun z => (R z).unop) (typeIIIQuaternion_pure_square b q hq)
      simpa only [map_mul, MulOpposite.unop_mul, AlgEquiv.commutes,
        MulOpposite.algebraMap_apply, MulOpposite.unop_op] using h
    have hqR : (R q).unop.re = 0 :=
      typeIIIQuaternion_pure_of_square_neg b _ (by linarith) _ hsquare
    let s := q + (R q).unop
    have hsR : (R s).unop = s := by
      simp only [s, map_add, MulOpposite.unop_add, hR]
      exact add_comm _ _
    have hspure : s.re = 0 := by simp [s, hq, hqR]
    have hs0 : s = 0 := by
      by_contra hs
      have hp := hpos s hs
      rw [hsR, typeIIIQuaternion_pure_square b s hspure,
        Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul] at hp
      have hn0 := typeIIIQuaternionNorm_nonneg b hb s
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn0)
        (le_of_lt hτ))) hp
    exact (eq_neg_iff_add_eq_zero).2 (by simpa only [s, add_comm] using hs0)
  intro q
  let v : ℍ[ℚ, -3, 0, b] := q - algebraMap ℚ _ q.re
  have hv : v.re = 0 := by simp [v, QuaternionAlgebra.algebraMap_eq]
  have h := hpure v hv
  have hsplit : q = v + algebraMap ℚ _ q.re := by
    dsimp [v]
    exact (sub_add_cancel _ _).symm
  rw [hsplit, map_add, MulOpposite.unop_add, AlgEquiv.commutes,
    MulOpposite.algebraMap_apply, MulOpposite.unop_op, h]
  have hvstar : star v = -v := by ext <;> simp [hv]
  rw [star_add, hvstar]
  congr 1
  ext <;> simp [QuaternionAlgebra.algebraMap_eq]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_positive_involution
