import HodgeLean.Foundations.Program.NumeratorJetReducedMovingField
import HodgeLean.Foundations.Program.NumeratorJetFixedAssembly

/-! # Rational remainder interface for stored moving coefficients -/

noncomputable section
open Polynomial Matrix
namespace HodgeLean.Foundations.Program

/-- The periodic polynomial arrays encode the periodic complex arrays at every order. -/
theorem b65e_storedResidue_eval_nat (p : Fin 12 → ℂ) (n : ℕ) :
    b65e_polynomialResidue p b65e_storedFixedQ b65e_storedMovingQ n =
      b65e_storedResidue p n := by
  funext q i j
  cases q with
  | inl k => rfl
  | inr x =>
    simp only [b65e_polynomialResidue, b65e_storedMovingQ, b65e_storedResidue,
      b65e_residueJet, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
      Rat.coe_castHom, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring

/-- A rational remainder identity gives the actual stored moving-pole field step. -/
theorem b65e_moving_stored_step_of_remainder (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (n : ℕ) (x : Fin 12) (i j : Fin 4)
    (h : (b65e_reducedMovingFieldQ b65e_storedFixedQ b65e_storedMovingQ n
        (b65q_fibreIndex x) i j) %ₘ b65e_fibrePolynomialQ (b65q_fibreIndex x) =
      C (n + 1 : ℚ) * b65e_storedMovingQ (n + 1) (b65q_fibreIndex x) i j) :
    b65e_fieldCoeff p (b65e_storedResidue p) n (.inr x) i j =
      (n + 1 : ℂ) * b65e_storedResidue p (n + 1) (.inr x) i j := by
  have hx : x ∈ b65q_fibreSet (b65q_fibreIndex x) := by
    simp only [b65q_fibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hr : (b65e_fibrePolynomialQ (b65q_fibreIndex x)).eval₂ (Rat.castHom ℂ) (p x) = 0 := by
    rw [← eval_map, b65e_fibrePolynomialQ_map]
    exact b65q_fibre_root O _ hx
  have he := congrArg (fun f : ℚ[X] ↦ f.eval₂ (Rat.castHom ℂ) (p x)) h
  rw [eval₂_modByMonic_eq_self_of_root hr, eval₂_mul, eval₂_C,
    b65e_reducedMovingFieldQ_eval p O b65e_storedFixedQ b65e_storedMovingQ n x i j] at he
  have hc : b65e_polynomialResidue p b65e_storedFixedQ b65e_storedMovingQ =
      b65e_storedResidue p := funext (b65e_storedResidue_eval_nat p)
  rw [hc] at he
  have hs := congrFun (congrFun (congrFun
    (b65e_storedResidue_eval_nat p (n + 1)) (.inr x)) i) j
  simp only [b65e_polynomialResidue] at hs
  rw [hs] at he
  simpa only [Rat.coe_castHom, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using he

end HodgeLean.Foundations.Program
