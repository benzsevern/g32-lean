import HodgeLean.Foundations.Program.NumeratorJetMovingCoordinateField
import HodgeLean.Foundations.Program.NumeratorJetTensorWeightEvaluation
import HodgeLean.Foundations.Program.NumeratorJetFixedAssembly
import HodgeLean.Foundations.Program.NumeratorJetMovingAssembly

/-! # Evaluation of the finite moving-pole contractions -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- Coordinate evaluation commutes with sums over a finite set. -/
theorem b65e_coordinateEvalQ_finsetSum {ι : Type*} (s : Finset ι)
    (u : ι → Fin 6 → ℚ) (z : ℂ) :
    b65e_coordinateEvalQ (fun c ↦ ∑ a ∈ s, u a c) z =
      ∑ a ∈ s, b65e_coordinateEvalQ (u a) z := by
  simp only [b65e_coordinateEvalQ, Rat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Coordinate evaluation commutes with addition. -/
theorem b65e_coordinateEvalQ_add (u v : Fin 6 → ℚ) (z : ℂ) :
    b65e_coordinateEvalQ (fun c ↦ u c + v c) z =
      b65e_coordinateEvalQ u z + b65e_coordinateEvalQ v z := by
  simp only [b65e_coordinateEvalQ, Rat.cast_add, add_mul, Finset.sum_add_distrib]

/-- Coordinate evaluation preserves rational scalar multiplication on the right. -/
theorem b65e_coordinateEvalQ_scale_right (a : ℚ) (u : Fin 6 → ℚ) (z : ℂ) :
    b65e_coordinateEvalQ (fun c ↦ u c * a) z =
      b65e_coordinateEvalQ u z * (a : ℂ) := by
  simp only [b65e_coordinateEvalQ, Rat.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Stored moving coordinates evaluate to the stored residue at the labelled pole. -/
theorem b65e_movingJet_coordinateEval (p : Fin 12 → ℂ) (b : ℕ) (x : Fin 12)
    (i j : Fin 4) :
    b65e_coordinateEvalQ (fun s ↦ b65e_movingJet (Fin.ofNat 8 b) (b65q_fibreIndex x) s i j)
      (p x) = b65e_storedResidue p b (.inr x) i j := by
  simp only [b65e_coordinateEvalQ, b65e_storedResidue, b65e_residueJet, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.map_apply, Rat.coe_castHom, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Stored fixed coefficients are the casts of the rational arrays. -/
theorem b65e_fixedJet_stored (p : Fin 12 → ℂ) (b : ℕ) (k i j : Fin 4) :
    (b65e_fixedJet (Fin.ofNat 8 b) k i j : ℂ) = b65e_storedResidue p b (.inl k) i j := by
  simp only [b65e_storedResidue, b65e_residueJet, Matrix.map_apply, Rat.coe_castHom]

/-- Certified fixed weights evaluate to the geometric coefficients at a moving pole. -/
theorem b65e_fixedWeightCoeffQ_coordinateEval (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (a : ℕ) (ha : a < 7) (x : Fin 12) (k : Fin 4) :
    b65e_coordinateEvalQ (b65e_fixedWeightCoeffQ (Fin.ofNat 7 a) (b65q_fibreIndex x) k)
      (p x) = b65e_poleRatioCoeff p (.inr x) (.inl k) a := by
  have hx : x ∈ b65q_fibreSet (b65q_fibreIndex x) := by
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hav : ((Fin.ofNat 7 a : Fin 7) : ℕ) = a := by
    simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt ha]
  have hw := b65e_fixedWeight_poleRatioCoeff p O _ k x hx (Fin.ofNat 7 a)
  rw [hav] at hw
  rw [b65e_poleRatioCoeff_symm, ← hw]
  simp only [b65e_reducedFixedWeightQ, b65e_coordinateEvalQ, eval₂_finsetSum, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X, Rat.coe_castHom]

/-- The fixed-source part of the rational contraction evaluates to the fixed-source field. -/
theorem b65e_movingFixedContraction_eval (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 7) (x : Fin 12) (i j : Fin 4) :
    b65e_coordinateEvalQ
        (fun c ↦ b65e_movingFixedContractionCoordsQ n (b65q_fibreIndex x) c i j) (p x) =
      ∑ k : Fin 4, ∑ a ∈ Finset.range (n.val + 1),
        b65e_poleRatioCoeff p (.inr x) (.inl k) a *
          ((∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
            b65e_storedResidue p b (.inl k) i t *
              b65e_storedResidue p (n.val - a - b) (.inr x) t j) -
           (∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
            b65e_storedResidue p b (.inr x) i t *
              b65e_storedResidue p (n.val - a - b) (.inl k) t j)) := by
  have hz : (b65q_fibreC (b65q_fibreIndex x)).eval (p x) = 0 :=
    b65q_fibre_root O _ (by
      simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and])
  unfold b65e_movingFixedContractionCoordsQ
  simp only [b65e_coordinateEvalQ_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a ha
  have ha7 : a < 7 := by have := Finset.mem_range.mp ha; omega
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [b65e_coordinateEvalQ_sub, b65e_coordinateEvalQ_scale,
    b65e_coordinateEvalQ_scale_right, b65e_coordinateMulQ_eval _ _ _ _ hz,
    b65e_coordinateMulQ_eval _ _ _ _ hz, b65e_fixedWeightCoeffQ_coordinateEval p O a ha7,
    b65e_movingJet_coordinateEval, b65e_movingJet_coordinateEval,
    b65e_fixedJet_stored p, b65e_fixedJet_stored p]
  ring

/-- Weighted moving vectors evaluate to labelled source sums of stored residues. -/
theorem b65e_tensorWeightedMoving_coordinateEval (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (a b : ℕ) (x : Fin 12) (d : Fin 2) (i j : Fin 4) :
    b65e_coordinateEvalQ
        (b65e_tensorWeightedMovingQ (Fin.ofNat 7 a) (Fin.ofNat 8 b) (b65q_fibreIndex x) d i j)
        (p x) =
      ∑ y ∈ b65q_fibreSet d,
        b65e_tensorCoordinateEvalQ
            (b65e_tensorWeightCoeffQ (Fin.ofNat 7 a) (b65q_fibreIndex x) d) (p x) (p y) *
          b65e_storedResidue p b (.inr y) i j :=
  b65e_tensorWeightedMovingQ_sum p O _ _ _ d i j (p x)

/-- One moving-source contraction term is a labelled sum of off-diagonal field terms. -/
theorem b65e_movingMovingContraction_term (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : ℕ) (x : Fin 12) (d : Fin 2) (a : ℕ) (ha : a < 7) (t : Fin 4) (b : ℕ)
    (i j : Fin 4) :
    b65e_coordinateEvalQ (fun c ↦
      b65e_coordinateMulQ (b65q_fibreIndex x)
        (b65e_tensorWeightedMovingQ (Fin.ofNat 7 a) (Fin.ofNat 8 b) (b65q_fibreIndex x) d i t)
        (fun s ↦ b65e_movingJet (Fin.ofNat 8 (n - a - b)) (b65q_fibreIndex x) s t j) c -
      b65e_coordinateMulQ (b65q_fibreIndex x)
        (fun s ↦ b65e_movingJet (Fin.ofNat 8 b) (b65q_fibreIndex x) s i t)
        (b65e_tensorWeightedMovingQ (Fin.ofNat 7 a)
          (Fin.ofNat 8 (n - a - b)) (b65q_fibreIndex x) d t j) c) (p x) =
      ∑ y ∈ b65q_fibreSet d, if y = x then 0 else
        b65e_poleRatioCoeff p (.inr x) (.inr y) a *
          (b65e_storedResidue p b (.inr y) i t *
              b65e_storedResidue p (n - a - b) (.inr x) t j -
            b65e_storedResidue p b (.inr x) i t *
              b65e_storedResidue p (n - a - b) (.inr y) t j) := by
  have hz : (b65q_fibreC (b65q_fibreIndex x)).eval (p x) = 0 :=
    b65q_fibre_root O _ (by
      simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and])
  have hav : ((Fin.ofNat 7 a : Fin 7) : ℕ) = a := by
    simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt ha]
  rw [b65e_coordinateEvalQ_sub, b65e_coordinateMulQ_eval _ _ _ _ hz,
    b65e_coordinateMulQ_eval _ _ _ _ hz, b65e_tensorWeightedMoving_coordinateEval p O,
    b65e_tensorWeightedMoving_coordinateEval p O, b65e_movingJet_coordinateEval,
    b65e_movingJet_coordinateEval, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    rw [ite_eq_left_iff.mpr (fun h ↦ absurd rfl h)]
    ring
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hyx)]
    have hd : b65q_fibreIndex y = d := (Finset.mem_filter.mp hy).2
    have hw := b65e_tensorWeightCoeffQ_poleRatioCoeff p O (Fin.ofNat 7 a) x y
      (Ne.symm hyx)
    rw [hd, hav] at hw
    rw [hw]
    ring

/-- The moving-source part of the rational contraction evaluates to the moving-source field. -/
theorem b65e_movingMovingContraction_eval (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 7) (x : Fin 12) (i j : Fin 4) :
    b65e_coordinateEvalQ
        (fun c ↦ b65e_movingMovingContractionCoordsQ n (b65q_fibreIndex x) c i j) (p x) =
      ∑ y : Fin 12, if y = x then 0 else ∑ a ∈ Finset.range (n.val + 1),
        b65e_poleRatioCoeff p (.inr x) (.inr y) a *
          ((∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
            b65e_storedResidue p b (.inr y) i t *
              b65e_storedResidue p (n.val - a - b) (.inr x) t j) -
           (∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
            b65e_storedResidue p b (.inr x) i t *
              b65e_storedResidue p (n.val - a - b) (.inr y) t j)) := by
  set G : Fin 12 → ℕ → Fin 4 → ℕ → ℂ := fun y a t b ↦ if y = x then 0 else
    b65e_poleRatioCoeff p (.inr x) (.inr y) a *
      (b65e_storedResidue p b (.inr y) i t *
          b65e_storedResidue p (n.val - a - b) (.inr x) t j -
        b65e_storedResidue p b (.inr x) i t *
          b65e_storedResidue p (n.val - a - b) (.inr y) t j) with hG
  have hrhs (y : Fin 12) :
      (if y = x then (0 : ℂ) else ∑ a ∈ Finset.range (n.val + 1),
        b65e_poleRatioCoeff p (.inr x) (.inr y) a *
          ((∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
            b65e_storedResidue p b (.inr y) i t *
              b65e_storedResidue p (n.val - a - b) (.inr x) t j) -
           (∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1),
            b65e_storedResidue p b (.inr x) i t *
              b65e_storedResidue p (n.val - a - b) (.inr y) t j))) =
      ∑ a ∈ Finset.range (n.val + 1), ∑ t : Fin 4,
        ∑ b ∈ Finset.range (n.val - a + 1), G y a t b := by
    by_cases hyx : y = x
    · simp only [hG, hyx, ite_true, Finset.sum_const_zero]
    · simp only [hG, hyx, ite_false]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
  rw [Finset.sum_congr rfl fun y _ ↦ hrhs y]
  unfold b65e_movingMovingContractionCoordsQ
  simp only [b65e_coordinateEvalQ_finsetSum]
  calc
    _ = ∑ d : Fin 2, ∑ a ∈ Finset.range (n.val + 1), ∑ t : Fin 4,
        ∑ b ∈ Finset.range (n.val - a + 1), ∑ y ∈ b65q_fibreSet d, G y a t b := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a ha
      have ha7 : a < 7 := by have := Finset.mem_range.mp ha; omega
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro b _
      exact b65e_movingMovingContraction_term p O n x d a ha7 t b i j
    _ = ∑ d : Fin 2, ∑ y ∈ b65q_fibreSet d, ∑ a ∈ Finset.range (n.val + 1),
        ∑ t : Fin 4, ∑ b ∈ Finset.range (n.val - a + 1), G y a t b := by
      apply Finset.sum_congr rfl
      intro d _
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      conv_rhs => rw [Finset.sum_comm]
    _ = _ := Finset.sum_fiberwise Finset.univ b65q_fibreIndex _

/-- The finite rational contraction evaluates to the stored moving-pole field. -/
theorem b65e_movingContraction_field (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : Fin 7) (x : Fin 12) (i j : Fin 4) :
    b65e_coordinateEvalQ
        (fun c ↦ b65e_movingContractionCoordsQ n (b65q_fibreIndex x) c i j) (p x) =
      b65e_fieldCoeff p (b65e_storedResidue p) n (.inr x) i j := by
  unfold b65e_movingContractionCoordsQ
  rw [b65e_coordinateEvalQ_add, b65e_movingFixedContraction_eval p O,
    b65e_movingMovingContraction_eval p O]
  unfold b65e_fieldCoeff
  rw [Fintype.sum_sum_type]
  simp only [reduceCtorEq, ite_false, Sum.inr.injEq]

end HodgeLean.Foundations.Program
