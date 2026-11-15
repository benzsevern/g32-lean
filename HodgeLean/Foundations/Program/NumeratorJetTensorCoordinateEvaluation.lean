import HodgeLean.Foundations.Program.NumeratorJetTensorWeightData

/-! # Evaluation of the initial rational tensor coordinates -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

set_option maxRecDepth 8192

/-- Multiplying every source coefficient by a reduced target polynomial. -/
def b65e_tensorCoordinateTargetMulQ (e : Fin 2) (u : Fin 6 → ℚ)
    (v : Fin 6 → Fin 6 → ℚ) (c h : Fin 6) : ℚ :=
  b65e_coordinateMulQ e u (fun a ↦ v a h) c

/-- Tensor evaluation preserves a target-polynomial factor. -/
theorem b65e_tensorCoordinateTargetMulQ_eval (e : Fin 2) (u : Fin 6 → ℚ)
    (v : Fin 6 → Fin 6 → ℚ) (x y : ℂ) (hx : (b65q_fibreC e).eval x = 0) :
    b65e_tensorCoordinateEvalQ (b65e_tensorCoordinateTargetMulQ e u v) x y =
      b65e_coordinateEvalQ u x * b65e_tensorCoordinateEvalQ v x y := by
  calc
    _ = ∑ h : Fin 6, y ^ (h : ℕ) *
        b65e_coordinateEvalQ (b65e_coordinateMulQ e u (fun a ↦ v a h)) x := by
      simp only [b65e_tensorCoordinateEvalQ, b65e_coordinateEvalQ]
      dsimp only [b65e_tensorCoordinateTargetMulQ]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = b65e_coordinateEvalQ u x * (∑ h : Fin 6, y ^ (h : ℕ) *
        b65e_coordinateEvalQ (fun a ↦ v a h) x) := by
      simp_rw [b65e_coordinateMulQ_eval e _ _ x hx]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by
      congr 1
      simp only [b65e_tensorCoordinateEvalQ, b65e_coordinateEvalQ, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro h _
      ring

/-- Tensor-coordinate evaluation preserves addition. -/
theorem b65e_tensorCoordinateEvalQ_add (u v : Fin 6 → Fin 6 → ℚ) (x y : ℂ) :
    b65e_tensorCoordinateEvalQ (fun a b ↦ u a b + v a b) x y =
      b65e_tensorCoordinateEvalQ u x y + b65e_tensorCoordinateEvalQ v x y := by
  simp only [b65e_tensorCoordinateEvalQ, b65e_coordinateEvalQ, Rat.cast_add,
    add_mul, mul_add, Finset.sum_add_distrib]

/-- Tensor-coordinate evaluation preserves negation. -/
theorem b65e_tensorCoordinateEvalQ_neg (u : Fin 6 → Fin 6 → ℚ) (x y : ℂ) :
    b65e_tensorCoordinateEvalQ (fun a b ↦ -u a b) x y =
      -b65e_tensorCoordinateEvalQ u x y := by
  simp only [b65e_tensorCoordinateEvalQ, b65e_coordinateEvalQ, Rat.cast_neg,
    neg_mul, mul_neg, Finset.sum_neg_distrib]

/-- Velocity coordinates evaluate to the rational velocity polynomial. -/
theorem b65e_coordinateEvalQ_velocity (e : Fin 2) (x : ℂ) :
    b65e_coordinateEvalQ (b65e_velocityQ e) x =
      (b65e_velocityPolynomialQ e).eval₂ (Rat.castHom ℂ) x := by
  simp only [b65e_coordinateEvalQ, b65e_velocityPolynomialQ, eval₂_finsetSum,
    eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Rat.coe_castHom]

/-- Inverse coordinates evaluate to the checked rational inverse polynomial. -/
theorem b65e_coordinateEvalQ_crossInverse (e : Fin 2) (x : ℂ) :
    b65e_coordinateEvalQ (b65e_crossInverseCoeffQ e) x =
      (b65e_crossInverseQ e).eval₂ (Rat.castHom ℂ) x := by
  simp only [b65e_coordinateEvalQ, b65e_crossInverseQ, eval₂_finsetSum,
    eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Rat.coe_castHom]

/-- Coordinate evaluation preserves subtraction. -/
theorem b65e_coordinateEvalQ_sub (u v : Fin 6 → ℚ) (x : ℂ) :
    b65e_coordinateEvalQ (fun a ↦ u a - v a) x =
      b65e_coordinateEvalQ u x - b65e_coordinateEvalQ v x := by
  simp only [b65e_coordinateEvalQ, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]

/-- Degree-six divided differences can be summed over seven fixed coefficient positions. -/
theorem b65e_tensorDifferenceQ_eq_seven (g : ℚ[X]) (hg : g.natDegree ≤ 6) :
    b65e_tensorDifferenceQ g = ∑ n : Fin 7, C (C (g.coeff n)) *
      ∑ i ∈ Finset.range n.val, C (X ^ i) * X ^ (n.val - 1 - i) := by
  unfold b65e_tensorDifferenceQ
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ C (C (g.coeff n)) *
    ∑ i ∈ Finset.range n, C (X ^ i) * X ^ (n - 1 - i)) 7]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n _ hn
  have hcoeff : g.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by
    have hn' : ¬ n < g.natDegree + 1 := by simpa only [Finset.mem_range] using hn
    omega)
  simp only [hcoeff, map_zero, zero_mul]

set_option maxHeartbeats 400000 in
/-- Seven polynomial coefficients give the divided difference in tensor coordinates. -/
theorem b65e_tensorDifferenceCoordsQ_coeff_eval (g : ℚ[X]) (hg : g.natDegree ≤ 6)
    (x y : ℂ) :
    b65e_tensorCoordinateEvalQ
        (b65e_tensorDifferenceCoordsQ (fun c : Fin 7 ↦ g.coeff c)) x y =
      b65e_tensorEval (b65e_tensorDifferenceQ g) x y := by
  rw [b65e_tensorDifferenceQ_eq_seven g hg]
  norm_num [b65e_tensorCoordinateEvalQ, b65e_coordinateEvalQ,
    b65e_tensorDifferenceCoordsQ, b65e_tensorEval,
    Fin.sum_univ_succ, Finset.sum_range_succ,
    eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, eval₂_finsetSum,
    coe_eval₂RingHom, Rat.coe_castHom]
  ring

/-- Velocity divided differences agree with the finite tensor coordinates. -/
theorem b65e_tensorDifferenceCoordsQ_velocity_eval (e : Fin 2) (x y : ℂ) :
    b65e_tensorCoordinateEvalQ
        (b65e_tensorDifferenceCoordsQ (b65e_velocitySevenQ e)) x y =
      b65e_tensorEval (b65e_tensorDifferenceQ (b65e_velocityPolynomialQ e)) x y := by
  have hc : (fun c : Fin 7 ↦ (b65e_velocityPolynomialQ e).coeff c) =
      b65e_velocitySevenQ e := by
    funext c
    fin_cases e <;> fin_cases c <;>
      norm_num [b65e_velocityPolynomialQ, b65e_velocityQ, b65e_velocitySevenQ,
        Fin.sum_univ_succ, coeff_C_mul_X_pow, coeff_X]
  rw [← hc]
  exact b65e_tensorDifferenceCoordsQ_coeff_eval _ (by
    rw [b65e_velocityPolynomialQ_natDegree]; split_ifs <;> omega) x y

/-- Sextic divided differences agree with the finite tensor coordinates. -/
theorem b65e_tensorDifferenceCoordsQ_fibre_eval (e : Fin 2) (x y : ℂ) :
    b65e_tensorCoordinateEvalQ
        (b65e_tensorDifferenceCoordsQ (b65q_fibreCoeff e)) x y =
      b65e_tensorEval (b65e_tensorDifferenceQ (b65e_fibrePolynomialQ e)) x y := by
  have hc : (fun c : Fin 7 ↦ (b65e_fibrePolynomialQ e).coeff c) = b65q_fibreCoeff e := by
    funext c
    have hf : b65e_fibrePolynomialQ e = Polynomial.ofFn 7 (b65q_fibreCoeff e) := by
      rw [b65e_ofFn_eq_sum]
      rfl
    rw [hf]
    exact Polynomial.ofFn_coeff_eq_val_of_lt _ c.isLt
  rw [← hc]
  exact b65e_tensorDifferenceCoordsQ_coeff_eval _ (by
    rw [b65e_fibrePolynomialQ_natDegree]) x y

/-- The finite initial tensor calculation evaluates to the original moving-pole weight. -/
theorem b65e_initialTensorCoordsQ_eval (e d : Fin 2) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) :
    b65e_tensorCoordinateEvalQ (b65e_initialTensorCoordsQ e d) x y =
      b65e_tensorEval (b65e_tensorWeightQ e d) x y := by
  by_cases hd : d = e
  · subst d
    have hc : b65e_initialTensorCoordsQ e e =
        b65e_tensorDifferenceCoordsQ (b65e_velocitySevenQ e) := by
      funext c h
      simp only [b65e_initialTensorCoordsQ, ite_true]
    rw [hc]
    simpa only [b65e_tensorWeightQ, ite_true] using
      b65e_tensorDifferenceCoordsQ_velocity_eval e x y
  · have hi := b65e_otherFibre_eq e d hd
    change b65e_tensorCoordinateEvalQ
      (fun c h ↦ if d = e then b65e_tensorDifferenceCoordsQ (b65e_velocitySevenQ e) c h else
        b65e_tensorCoordinateTargetMulQ e
          (b65e_coordinateMulQ e (fun a ↦ b65e_velocityQ e a - b65e_velocityQ d a)
            (b65e_crossInverseCoeffQ e))
          (b65e_tensorDifferenceCoordsQ (b65q_fibreCoeff d)) c h +
        b65e_tensorDifferenceCoordsQ (b65e_velocitySevenQ d) c h) x y = _
    simp only [ite_eq_right hd]
    rw [b65e_tensorCoordinateEvalQ_add, b65e_tensorCoordinateTargetMulQ_eval e _ _ x y hx,
      b65e_coordinateMulQ_eval e _ _ x hx, b65e_coordinateEvalQ_sub,
      b65e_coordinateEvalQ_velocity, b65e_coordinateEvalQ_velocity,
      b65e_coordinateEvalQ_crossInverse, b65e_tensorDifferenceCoordsQ_fibre_eval,
      b65e_tensorDifferenceCoordsQ_velocity_eval]
    simp only [b65e_tensorWeightQ, ite_eq_right hd, b65e_tensorInverseQ, hi,
      b65e_tensorEval, eval₂_add, eval₂_mul, eval₂_C, eval₂_sub, coe_eval₂RingHom]
    ring

end HodgeLean.Foundations.Program
