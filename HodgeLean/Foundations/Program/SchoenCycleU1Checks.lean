module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.Tactic

/-! # Independent canonical-parameter checks
Two lines are distinct, and the complex first-order test has a nonzero nilpotent.
HC no distance; AV milestone no distance.
-/
public section

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The two coordinate lines give distinct projective parameters.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, linear systems. -/
theorem s2e_u1_check_distinct_lines :
    Projectivization.mk ℂ ((1, 0) : ℂ × ℂ) (by simp) ≠
      Projectivization.mk ℂ ((0, 1) : ℂ × ℂ) (by simp) := by
  intro h
  obtain ⟨c, he⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h
  have hf := congrArg Prod.fst he
  simp at hf

/-- The first-order test has information invisible after reduction.
Source: Hartshorne, Algebraic Geometry, II.8, dual numbers and tangent vectors. -/
theorem s2e_u1_check_first_order :
    (DualNumber.eps : DualNumber ℂ) ≠ 0 ∧
      (DualNumber.eps : DualNumber ℂ) ^ 2 = 0 := by
  constructor
  · intro h
    have hs := congrArg TrivSqZeroExt.snd h
    change (1 : ℂ) = 0 at hs
    exact one_ne_zero hs
  · simpa only [pow_two] using (DualNumber.eps_mul_eps (R := ℂ))

#print axioms s2e_u1_check_distinct_lines
#print axioms s2e_u1_check_first_order
end HodgeLean.Foundations.Program
