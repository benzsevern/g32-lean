import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.CompactModel
import Mathlib.Data.Matrix.Basic

/-! # Real polynomial equations for actual projective matrix coordinates -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program HodgeLean.Foundations.ComplexTopology
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- Finite polynomial equations retain their literal simultaneous zero set.
Source: s2v_t11b_Formula.conjunction; realize_equationFormula.
HC no distance; AV milestone no distance. -/
def properCycle_finite_equation_formula {n : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial (Fin n) ℝ) : s2v_t11b_Formula n :=
  .conjunction (Finset.univ.toList.map fun i => equationFormula (p i))

/-- Evaluation of the finite equation formula is exactly simultaneous evaluation at zero.
Source: s2v_t11b_realize_conjunction; realize_equationFormula.
HC no distance; AV milestone no distance. -/
theorem properCycle_finite_equation_formula_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (properCycle_finite_equation_formula p).realize ↔
      ∀ i, MvPolynomial.eval x (p i) = 0 := by
  simp [properCycle_finite_equation_formula, s2v_t11b_realize_conjunction,
    realize_equationFormula]

/-- A real polynomial presentation of Hermitian matrices of trace one and vanishing two by two minors.
Source: properCycle_projective_matrix_coordinates_range; Complex.mul_re; Complex.mul_im.
HC no distance; AV milestone no distance. -/
def properCycle_polynomial_matrix_formula {n : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ι → MvPolynomial (Fin n) ℝ) : s2v_t11b_Formula n :=
  .inter
    (properCycle_finite_equation_formula fun ij : ι × ι => a ij.1 ij.2 - a ij.2 ij.1)
    (.inter
      (properCycle_finite_equation_formula fun ij : ι × ι => b ij.1 ij.2 + b ij.2 ij.1)
      (.inter (equationFormula ((∑ i, a i i) - 1))
        (.inter (equationFormula (∑ i, b i i))
          (.inter
            (properCycle_finite_equation_formula fun t : (ι × ι) × (ι × ι) =>
              a t.1.1 t.1.2 * a t.2.1 t.2.2 - b t.1.1 t.1.2 * b t.2.1 t.2.2 -
                a t.1.1 t.2.2 * a t.2.1 t.1.2 + b t.1.1 t.2.2 * b t.2.1 t.1.2)
            (properCycle_finite_equation_formula fun t : (ι × ι) × (ι × ι) =>
              a t.1.1 t.1.2 * b t.2.1 t.2.2 + b t.1.1 t.1.2 * a t.2.1 t.2.2 -
                a t.1.1 t.2.2 * b t.2.1 t.1.2 - b t.1.1 t.2.2 * a t.2.1 t.1.2)))))

/-- Polynomial matrix equations evaluate to the original complex matrix equations.
Source: Complex.ext_iff; properCycle_finite_equation_formula_iff.
HC no distance; AV milestone no distance. -/
theorem properCycle_polynomial_matrix_formula_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ι → MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (properCycle_polynomial_matrix_formula a b).realize ↔
      let M : Matrix ι ι ℂ := fun i j =>
        ⟨MvPolynomial.eval x (a i j), MvPolynomial.eval x (b i j)⟩
      (∀ i j, star (M i j) = M j i) ∧ (∑ i, M i i) = 1 ∧
        ∀ i j k l, M i j * M k l = M i l * M k j := by
  simp only [properCycle_polynomial_matrix_formula, s2v_t11b_Formula.realize,
    Set.mem_inter_iff, properCycle_finite_equation_formula_iff,
    realize_equationFormula, map_sub, map_add, map_mul, map_sum, map_one]
  simp only [Complex.ext_iff, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im]
  constructor
  · rintro ⟨ha, hb, ht, hu, hr, hi⟩
    refine ⟨?_, ⟨sub_eq_zero.mp ht, hu⟩, ?_⟩
    · intro i j
      exact ⟨sub_eq_zero.mp (ha (i,j)), by linarith [hb (i,j)]⟩
    · intro i j k l
      constructor <;> linarith [hr ((i,j),(k,l)), hi ((i,j),(k,l))]
  · rintro ⟨hh, ht, hm⟩
    refine ⟨?_, ?_, sub_eq_zero.mpr ht.1, ht.2, ?_, ?_⟩
    · rintro ⟨i,j⟩; exact sub_eq_zero.mpr (hh i j).1
    · rintro ⟨i,j⟩; linarith [(hh i j).2]
    · rintro ⟨⟨i,j⟩,⟨k,l⟩⟩; linarith [(hm i j k l).1]
    · rintro ⟨⟨i,j⟩,⟨k,l⟩⟩; linarith [(hm i j k l).2]

end HodgeLean.Foundations.QuotientDuality
