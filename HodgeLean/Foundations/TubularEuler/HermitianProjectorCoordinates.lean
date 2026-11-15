import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! # Homogeneous Hermitian projector coordinates

The matrix retains homogeneous scaling and the affine coordinate recovery map.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open scoped ComplexConjugate
namespace HodgeLean.Foundations.TubularEuler

/-- Squared Hermitian length in homogeneous coordinates.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
def projectorLength {n : ℕ} (z : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (z i)

example : projectorLength (![1, Complex.I] : Fin 2 → ℂ) = 2 := by
  norm_num [projectorLength, Fin.sum_univ_two]

/-- The normalized rank-one Hermitian projector matrix.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
def hermitianProjector {n : ℕ} (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => z i * star (z j) / (projectorLength z : ℂ)

example : hermitianProjector (![1, Complex.I] : Fin 2 → ℂ) 0 1 = -Complex.I / 2 := by
  norm_num [hermitianProjector, projectorLength, Fin.sum_univ_two, Complex.star_def]

/-- Positivity of the denominator on nonzero homogeneous coordinates.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem projectorLength_pos {n : ℕ} {z : Fin n → ℂ} (hz : z ≠ 0) :
    0 < projectorLength z := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := Function.ne_iff.mp hz
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (z j))
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

example : 0 < projectorLength (![1, 0] : Fin 2 → ℂ) :=
  projectorLength_pos (by intro h; have := congrFun h 0; norm_num at this)

/-- Nonzero homogeneous rescaling leaves the projector unchanged.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem hermitianProjector_smul {n : ℕ} (z : Fin n → ℂ) (a : ℂ) (ha : a ≠ 0) :
    hermitianProjector (a • z) = hermitianProjector z := by
  have hlen : projectorLength (a • z) = Complex.normSq a * projectorLength z := by
    simp only [projectorLength, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
      Finset.mul_sum]
  ext i j
  simp only [hermitianProjector, Pi.smul_apply, smul_eq_mul, star_mul, hlen,
    Complex.ofReal_mul]
  rw [Complex.normSq_eq_conj_mul_self]
  change a * z i * (star (z j) * star a) / (star a * a * (projectorLength z : ℂ)) = _
  rw [show a * z i * (star (z j) * star a) = (star a * a) * (z i * star (z j)) by ring]
  exact mul_div_mul_left _ _ (mul_ne_zero (by simpa using ha) ha)

example : hermitianProjector ((2 : ℂ) • (![1, Complex.I] : Fin 2 → ℂ)) =
    hermitianProjector (![1, Complex.I] : Fin 2 → ℂ) :=
  hermitianProjector_smul _ _ (by norm_num)

/-- A nonzero diagonal entry recovers all affine coordinates from its column.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem hermitianProjector_ratio {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (hj : z j ≠ 0)
    (i : Fin n) : hermitianProjector z i j / hermitianProjector z j j = z i / z j := by
  have hz : z ≠ 0 := by intro h; exact hj (congrFun h j)
  have hlen : (projectorLength z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (projectorLength_pos hz))
  have hstar : star (z j) ≠ 0 := by simpa using hj
  dsimp [hermitianProjector]
  field_simp [hlen, hj, hstar]

example : hermitianProjector (![1, Complex.I] : Fin 2 → ℂ) 1 0 /
    hermitianProjector (![1, Complex.I] : Fin 2 → ℂ) 0 0 = Complex.I := by
  simpa using hermitianProjector_ratio (![1, Complex.I] : Fin 2 → ℂ) 0 (by norm_num) 1

/-- The normalized matrix takes values in the real vector space of Hermitian matrices.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem hermitianProjector_isHermitian {n : ℕ} (z : Fin n → ℂ) :
    (hermitianProjector z).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, hermitianProjector, star_div, star_mul, mul_comm]

example : (hermitianProjector (![1, Complex.I] : Fin 2 → ℂ)).IsHermitian :=
  hermitianProjector_isHermitian _

#print axioms projectorLength_pos
#print axioms hermitianProjector_isHermitian
#print axioms hermitianProjector_smul
#print axioms hermitianProjector_ratio
end HodgeLean.Foundations.TubularEuler
