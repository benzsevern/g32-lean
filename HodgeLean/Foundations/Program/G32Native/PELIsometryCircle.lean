import HodgeLean.Foundations.Program.G32Native.PELIsometryGroup
import HodgeLean.Foundations.HodgeGroupAlgebraicGkConn
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations

variable {n : ℕ}

/-- The elementary circle associated with a square-minus-one matrix. -/
def pelCircleMatrix (J : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :=
  (Real.cos t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Real.sin t : ℂ) • J

/-- Opposite angles give inverse matrices; the sign in the square is essential. -/
theorem pelCircleMatrix_mul_neg (J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J * J = -1) (t : ℝ) :
    pelCircleMatrix J t * pelCircleMatrix J (-t) = 1 := by
  have ht : (Real.cos t : ℂ) * (Real.cos t : ℂ) +
      (Real.sin t : ℂ) * (Real.sin t : ℂ) = 1 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq t] :
      Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1)
  simp only [pelCircleMatrix, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    add_mul, mul_add, smul_mul_smul, one_mul, mul_one, hJ, smul_neg]
  calc
    _ = ((Real.cos t : ℂ) * (Real.cos t : ℂ) +
        (Real.sin t : ℂ) * (Real.sin t : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by module
    _ = 1 := by rw [ht, one_smul]

/-- The period-circle matrices as units. -/
def pelCircleUnit (J : Matrix (Fin n) (Fin n) ℂ) (hJ : J * J = -1)
    (t : ℝ) : Matrix.GeneralLinearGroup (Fin n) ℂ where
  val := pelCircleMatrix J t
  inv := pelCircleMatrix J (-t)
  val_inv := pelCircleMatrix_mul_neg J hJ t
  inv_val := by simpa only [neg_neg] using pelCircleMatrix_mul_neg J hJ (-t)

/-- A square-minus-one isometry is infinitesimally skew. -/
theorem pel_square_isometry_skew (J Ω : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J * J = -1) (hΩ : J.transpose * Ω * J = Ω) :
    J.transpose * Ω + Ω * J = 0 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M * J) hΩ
  have hn : -(J.transpose * Ω) = Ω * J := by
    simpa only [mul_assoc, hJ, mul_neg, mul_one] using h
  rw [← hn, add_neg_cancel]

/-- The entire elementary circle preserves the original bilinear form. -/
theorem pelCircleMatrix_isometry (J Ω : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J * J = -1) (hΩ : J.transpose * Ω * J = Ω) (t : ℝ) :
    (pelCircleMatrix J t).transpose * Ω * pelCircleMatrix J t = Ω := by
  have hs := pel_square_isometry_skew J Ω hJ hΩ
  have ht : (Real.cos t : ℂ) * (Real.cos t : ℂ) +
      (Real.sin t : ℂ) * (Real.sin t : ℂ) = 1 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq t] :
      Real.cos t * Real.cos t + Real.sin t * Real.sin t = 1)
  calc
    _ = ((Real.cos t : ℂ) * (Real.cos t : ℂ)) • Ω +
        ((Real.cos t : ℂ) * (Real.sin t : ℂ)) • (J.transpose * Ω + Ω * J) +
        ((Real.sin t : ℂ) * (Real.sin t : ℂ)) • (J.transpose * Ω * J) := by
      simp only [pelCircleMatrix, Matrix.transpose_add, Matrix.transpose_smul,
        Matrix.transpose_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one]
      module
    _ = Ω := by
      rw [hs, hΩ, smul_zero, add_zero, ← add_smul, ht, one_smul]

/-- Quaternion commutation is retained along the circle. -/
theorem pelCircleMatrix_commute (J T : Matrix (Fin n) (Fin n) ℂ)
    (h : J * T = T * J) (t : ℝ) :
    pelCircleMatrix J t * T = T * pelCircleMatrix J t := by
  simp only [pelCircleMatrix, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, h]

/-- A compatible complex structure lies in the connected isometry group.
Source: the explicit curve cos(t) 1 + sin(t) J and
`g2k_mem_component_of_curve`. -/
theorem pel_complex_structure_mem_component (J Ω : Matrix (Fin n) (Fin n) ℂ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (hJ : J * J = -1) (hΩ : J.transpose * Ω * J = Ω)
    (hS : ∀ T ∈ S, J * T = T * J) :
    pelCircleUnit J hJ (Real.pi / 2) ∈ g1_identityComponent (pelIsometryGroup Ω S) := by
  apply g2k_mem_component_of_curve (pelIsometryGroup Ω S).carrier
    (pelCircleUnit J hJ) ?_ ?_ (0 : ℝ) (Real.pi / 2) ?_
  · intro i j
    change Continuous (fun t : ℝ =>
      (Real.cos t : ℂ) * (1 : Matrix (Fin n) (Fin n) ℂ) i j +
        (Real.sin t : ℂ) * J i j)
    exact ((Complex.continuous_ofReal.comp Real.continuous_cos).mul continuous_const).add
      ((Complex.continuous_ofReal.comp Real.continuous_sin).mul continuous_const)
  · intro t
    apply (mem_pelIsometryGroup Ω S _).mpr
    exact ⟨pelCircleMatrix_isometry J Ω hJ hΩ t,
      fun T hT => pelCircleMatrix_commute J T (hS T hT) t⟩
  · apply Units.ext
    simp [pelCircleUnit, pelCircleMatrix]

#print axioms pelCircleMatrix_mul_neg
#print axioms pel_square_isometry_skew
#print axioms pelCircleMatrix_isometry
#print axioms pelCircleMatrix_commute
#print axioms pel_complex_structure_mem_component
end HodgeLean.Foundations.Program.GeneralTypeIII
