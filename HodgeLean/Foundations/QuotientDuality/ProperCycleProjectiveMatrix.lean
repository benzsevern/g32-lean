import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Actual finite matrix coordinates for complex projective points -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual sum of squared coordinate norms of a homogeneous complex vector.
Source: Mathlib, Complex.normSq and Finset.sum.
HC no distance; AV milestone no distance. -/
def properCycle_projective_matrix_mass {ι : Type} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

/-- The actual coordinate mass of a nonzero homogeneous vector is strictly positive.
Source: Mathlib, Complex.normSq_pos and Finset.sum_pos'.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_mass_pos {ι : Type} [Fintype ι]
    (v : ι → ℂ) (hv : v ≠ 0) : 0 < properCycle_projective_matrix_mass v := by
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (v j))
    ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- Homogeneous scalar multiplication multiplies the actual mass by the scalar's squared norm.
Source: Mathlib, Complex.normSq_mul and Finset.mul_sum.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_mass_smul {ι : Type} [Fintype ι]
    (c : ℂ) (v : ι → ℂ) :
    properCycle_projective_matrix_mass (c • v) = Complex.normSq c * properCycle_projective_matrix_mass v := by
  simp only [properCycle_projective_matrix_mass, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Finset.mul_sum]

/-- The actual normalized outer-product matrix of a homogeneous complex coordinate vector.
Source: Mathlib, Complex.mul_conj and Projectivization.lift; the Hermitian projection onto a complex line.
HC no distance; AV milestone no distance. -/
def properCycle_projective_matrix {ι : Type} [Fintype ι] (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => v i * star (v j) / (properCycle_projective_matrix_mass v : ℂ)

/-- The actual normalized outer-product matrix is unchanged by nonzero homogeneous rescaling.
Source: Mathlib, Complex.normSq_mul and Complex.mul_conj.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_smul {ι : Type} [Fintype ι]
    (c : ℂ) (hc : c ≠ 0) (v : ι → ℂ) :
    properCycle_projective_matrix (c • v) = properCycle_projective_matrix v := by
  have hn : (Complex.normSq c : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hc).ne'
  ext i j
  simp only [properCycle_projective_matrix, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    star_mul, properCycle_projective_matrix_mass_smul, Complex.ofReal_mul]
  calc
    (c * v i) * (star (v j) * star c) /
        ((Complex.normSq c : ℂ) * (properCycle_projective_matrix_mass v : ℂ)) =
      (c * star c) * (v i * star (v j)) /
        ((Complex.normSq c : ℂ) * (properCycle_projective_matrix_mass v : ℂ)) := by ring
    _ = _ := by
      rw [show c * star c = (Complex.normSq c : ℂ) from Complex.mul_conj c]
      exact mul_div_mul_left _ _ hn

/-- The diagonal sum of the actual matrix of a nonzero homogeneous vector is one.
Source: Mathlib, Complex.mul_conj and the actual coordinate normalization sum.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_diagonal_sum {ι : Type} [Fintype ι]
    (v : ι → ℂ) (hv : v ≠ 0) : ∑ i, properCycle_projective_matrix v i i = 1 := by
  have hn : (properCycle_projective_matrix_mass v : ℂ) ≠ 0 := by
    exact_mod_cast (properCycle_projective_matrix_mass_pos v hv).ne'
  simp only [properCycle_projective_matrix, Matrix.of_apply]
  simp_rw [show ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) from fun z => Complex.mul_conj z]
  rw [← Finset.sum_div]
  have hh : (∑ i, (Complex.normSq (v i) : ℂ)) = (properCycle_projective_matrix_mass v : ℂ) := by
    simp only [properCycle_projective_matrix_mass, Complex.ofReal_sum]
  rw [hh, div_self hn]

/-- The actual normalization mass is continuous on the original finite complex coordinate space.
Source: Mathlib, Complex.continuous_normSq and continuous_finsetSum.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_mass_continuous {ι : Type} [Fintype ι] :
    Continuous (properCycle_projective_matrix_mass (ι := ι)) := by
  exact continuous_finsetSum Finset.univ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

/-- The actual normalized matrix is continuous on nonzero homogeneous coordinate vectors.
Source: Mathlib, continuity of complex conjugation and division, and the positive normalization mass.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_continuous {ι : Type} [Fintype ι] :
    Continuous (fun v : {v : ι → ℂ // v ≠ 0} => properCycle_projective_matrix v.val) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun v : {v : ι → ℂ // v ≠ 0} =>
    v.val i * star (v.val j) / (properCycle_projective_matrix_mass v.val : ℂ))
  apply (((continuous_apply i).comp continuous_subtype_val).mul
    (continuous_star.comp ((continuous_apply j).comp continuous_subtype_val))).div
    (Complex.continuous_ofReal.comp (properCycle_projective_matrix_mass_continuous.comp continuous_subtype_val))
  intro v
  change (properCycle_projective_matrix_mass v.val : ℂ) ≠ 0
  exact_mod_cast (properCycle_projective_matrix_mass_pos v.val v.property).ne'

end HodgeLean.Foundations.QuotientDuality
