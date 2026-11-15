import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Galois.Basic

/-! Independent scalar, quadratic-field and ramified monomial checks.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace FieldTheory.CyclicKummer.Checks

-- Period six with a noncoprime pair (2, 4), and an unpaired exponent zero.
example :
    let t : ℚ := 12
    let x : ℚ := 2
    let y : ℚ := 3
    let ε : ℚ := t ^ 6 / (x ^ 2 * y ^ 4)
    t ^ 6 = ε * x ^ 2 * y ^ 4 * (0 : ℚ) ^ 0 ∧
      (t / x) ^ 6 = ε * (y / x) ^ 4 * (0 : ℚ) ^ 0 ∧
      (t / y) ^ 6 = ε * (x / y) ^ 2 * (0 : ℚ) ^ 0 := by
  norm_num

-- A pair with one exponent zero is still permitted.
example :
    let t : ℚ := 6
    let x : ℚ := 2
    let y : ℚ := 3
    let ε : ℚ := t ^ 4 / y ^ 4
    (t / x) ^ 4 = ε * (y / x) ^ 4 ∧
      (t / y) ^ 4 = ε * (x / y) ^ 0 := by
  norm_num

-- Evaluation on the actual integral ring is unchanged by identity transport.
example (R K L : Type*) [CommRing R] [Field K] [CommRing L] [Algebra R K]
    (p : integralClosure R K →+* L) (b : integralClosure R K) :
    p ((AlgEquiv.refl : K ≃ₐ[R] K).mapIntegralClosure b) = p b := by
  rfl

-- Scalar period one puts no nonzero requirement on an eigenfunction.
example (F E : Type*) [Field F] [Field E] [Algebra F E] (v : E) :
    (AlgEquiv.refl : E ≃ₐ[F] E) (v ^ 1) = v ^ 1 := by
  rfl

-- The real quadratic extension has a cyclic group of order two.
example : Module.finrank ℝ ℂ = 2 ∧ IsGalois ℝ ℂ ∧ IsCyclic (ℂ ≃ₐ[ℝ] ℂ) := by
  letI : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
  refine ⟨Complex.finrank_real_complex, inferInstance, ?_⟩
  apply isCyclic_of_prime_card (p := 2)
  rw [IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]

-- Conjugation moves the nonzero eigenfunction I by the primitive scalar -1.
example : IsPrimitiveRoot (-1 : ℝ) 2 ∧ Complex.I ≠ 0 ∧
    Complex.conjAe Complex.I = algebraMap ℝ ℂ (-1) * Complex.I ∧
    Complex.conjAe ≠ (1 : ℂ ≃ₐ[ℝ] ℂ) ∧ Complex.I ^ 2 = (-1 : ℂ) := by
  refine ⟨IsPrimitiveRoot.neg_one 0 (by norm_num), Complex.I_ne_zero, ?_, ?_,
    Complex.I_sq⟩
  · simp
  · intro h
    have hI := DFunLike.congr_fun h Complex.I
    have hi := congrArg Complex.im hI
    norm_num at hi

-- On the tame double cover x = t², the sign involution fixes x and every
-- evaluation at the ramification point, but moves t.
example :
    let σ := Polynomial.algEquivAevalNegX (R := ℂ)
    σ (Polynomial.X ^ 2) = Polynomial.X ^ 2 ∧
      σ Polynomial.X ≠ Polynomial.X ∧
      ∀ p : Polynomial ℂ, (σ p).eval 0 = p.eval 0 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · simp [Polynomial.algEquivAevalNegX_apply]
  · intro h
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
    norm_num [Polynomial.algEquivAevalNegX_apply] at hc
  · intro p
    change (p.comp (-Polynomial.X)).eval 0 = p.eval 0
    simp [Polynomial.eval_comp]

end FieldTheory.CyclicKummer.Checks
