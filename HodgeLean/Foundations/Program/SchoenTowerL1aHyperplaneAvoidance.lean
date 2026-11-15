import Mathlib.Algebra.Polynomial.Roots

/-! # Finite support hyperplane avoidance

Implication from nonzero finite coordinate vectors to one integer-coefficient
linear form nonvanishing on all of them. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A moment-curve linear form with natural number coefficients avoids finitely many nonzero vectors.
Source: Hartshorne, Algebraic Geometry, II.2–3, affine neighborhoods in projective space; polynomial root bound. -/
theorem s2v_l1a_finite_coordinate_avoidance
    {K κ : Type*} [Field K] [CharZero K] [Fintype κ]
    (n : ℕ) (v : κ → Fin n → K) (hv : ∀ k, v k ≠ 0) :
    ∃ t : ℕ, ∀ k, (∑ j : Fin n, v k j * (t : K) ^ j.val) ≠ 0 := by
  classical
  let P (k : κ) : Polynomial K := ∑ j : Fin n, Polynomial.monomial j.val (v k j)
  have hcoeff (k : κ) (j : Fin n) : (P k).coeff j.val = v k j := by
    simp [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj]
  have hP (k : κ) : P k ≠ 0 := by
    intro hzero
    apply hv k
    funext j
    have h := congrArg (fun p : Polynomial K => p.coeff j.val) hzero
    simpa only [hcoeff, Polynomial.coeff_zero, Pi.zero_apply] using h
  have hprod : (∏ k, P k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => hP k)
  have hex : ∃ t : ℕ, (∏ k, P k).eval (t : K) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hprod
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono
    rintro x ⟨t, rfl⟩
    exact h t
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, ?_⟩
  intro k
  have hall : ∏ k, (P k).eval (t : K) ≠ 0 := by
    simpa only [Polynomial.eval_prod] using ht
  have hk := Finset.prod_ne_zero_iff.mp hall k (Finset.mem_univ k)
  simpa only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial] using hk

end HodgeLean.Foundations.Program
