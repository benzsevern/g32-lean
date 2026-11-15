import HodgeLean.Foundations.HodgeGroupAlgebraicGkLie
import HodgeLean.Foundations.MatrixAlgGroupLieRecovery

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations HodgeLean.RealDefs HodgeLean.Foundations.Program MvPolynomial
variable {n : ℕ}

/-- The determinant-one isometry matrix group with its polynomial equations.
Source: Borel, Linear Algebraic Groups, second edition, §1.6. -/
def specialOrthogonalMatrixGroup (Ω : Matrix (Fin n) (Fin n) ℂ) :
    MatrixAlgGroup ℂ n := g1_inter (g1_isometryGroup Ω) (g1_SL ℂ n)

theorem mem_specialOrthogonalMatrixGroup (Ω : Matrix (Fin n) (Fin n) ℂ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g ∈ (specialOrthogonalMatrixGroup Ω).carrier ↔
      (g : Matrix (Fin n) (Fin n) ℂ).transpose * Ω * g = Ω ∧
      (g : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
  change (_ ∧ Matrix.GeneralLinearGroup.det g = 1) ↔ _
  rw [Units.ext_iff]
  rfl

attribute [local irreducible] specialOrthogonalMatrixGroup

private theorem eval_isometryEquation (Ω M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    eval (fun ij => M ij.1 ij.2) (g1_isometryEquations Ω i j) =
      (M.transpose * Ω * M - Ω) i j := by
  have hc : (eval (fun ij : Fin n × Fin n => M ij.1 ij.2)).mapMatrix (Ω.map C) = Ω := by
    ext a b; simp
  have hx : (eval (fun ij : Fin n × Fin n => M ij.1 ij.2)).mapMatrix (g1_varMatrix ℂ n) = M := by
    ext a b; simp [g1_varMatrix]
  have hm : (eval (fun ij : Fin n × Fin n => M ij.1 ij.2)).mapMatrix (g1_isometryEquations Ω) =
      M.transpose * Ω * M - Ω := by
    have ht : (eval (fun ij : Fin n × Fin n => M ij.1 ij.2)).mapMatrix
        (g1_varMatrix ℂ n).transpose = M.transpose := by
      ext a b
      simp [g1_varMatrix]
    rw [g1_isometryEquations, map_sub, map_mul, map_mul, hc, ht, hx]
  exact congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => N i j) hm

/-- The linearization of an isometry equation over the complex numbers.
Source: Borel, Linear Algebraic Groups, second edition, §3.6. -/
theorem differential_isometryEquation (Ω X : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    g1_differential (g1_isometryEquations Ω i j) X =
      (X.transpose * Ω + Ω * X) i j := by
  refine g2k_differential_eq_of_line _ X ?_
  have hm (t : ℂ) : (1 + t • X).transpose * Ω * (1 + t • X) - Ω =
      t • (X.transpose * Ω + Ω * X) + t ^ 2 • (X.transpose * Ω * X) := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
      add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul, pow_two]
    abel
  have hf : (fun t : ℂ => eval (fun ij => (1 + t • X) ij.1 ij.2)
      (g1_isometryEquations Ω i j)) =
      fun t => t * (X.transpose * Ω + Ω * X) i j +
        t ^ 2 * (X.transpose * Ω * X) i j := by
    funext t
    rw [eval_isometryEquation, hm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hf]
  exact g2k_hasDerivAt_mul_add_sq _ _

/-- Exponentiating a trace-zero skew operator gives actual determinant-one
isometries, for every complex parameter.
Source: Humphreys, Linear Algebraic Groups, §13.1. -/
theorem exp_mem_specialOrthogonalMatrixGroup (Ω X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.transpose * Ω + Ω * X = 0) (ht : X.trace = 0) (t : ℂ) :
    g2k_expGL X t ∈ (specialOrthogonalMatrixGroup Ω).carrier := by
  rw [mem_specialOrthogonalMatrixGroup, g2k_coe_expGL]
  refine ⟨g2k_exp_isometry X Ω hX t, ?_⟩
  simpa only [mul_one, sub_self, add_zero] using
    g2k_det_exp_proj X 1 (by simp) (by simp) (by simpa using ht) t

/-- The tangent space of the determinant-one isometry matrix group is exactly
the trace-zero skew space. This form also applies to degenerate Gram matrices.
Source: Borel, Linear Algebraic Groups, second edition, §3.6;
Humphreys, Linear Algebraic Groups, §13.1. -/
theorem lie_specialOrthogonalMatrixGroup (Ω X : Matrix (Fin n) (Fin n) ℂ) :
    X ∈ g1_lieAlgebra (specialOrthogonalMatrixGroup Ω) ↔
      X.transpose * Ω + Ω * X = 0 ∧ X.trace = 0 := by
  rw [g1_lieAlgebra, g1_mem_lieOfSet_iff]
  constructor
  · intro hv
    constructor
    · ext i j
      have hf : g1_isometryEquations Ω i j ∈ g1_vanishingIdealSet
          ((specialOrthogonalMatrixGroup Ω).carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) := by
        refine g1_mem_vanishingIdealSet_iff.mpr ?_
        intro g hg
        have hg' := (mem_specialOrthogonalMatrixGroup Ω g).mp hg
        rw [show g1_coords g =
          (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2) from rfl]
        rw [eval_isometryEquation, hg'.1, sub_self]
        rfl
      have hz := hv (g1_isometryEquations Ω i j) hf
      rw [differential_isometryEquation] at hz
      exact hz
    · have hf : MvPolynomial.map (algebraMap ℚ ℂ) ((g1_varMatrix ℚ n).det - 1) ∈
          g1_vanishingIdealSet
          ((specialOrthogonalMatrixGroup Ω).carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) := by
        refine g1_mem_vanishingIdealSet_iff.mpr ?_
        intro g hg
        have hg' := (mem_specialOrthogonalMatrixGroup Ω g).mp hg
        rw [g2k_eval_map, g2k_aeval_det_sub_one]
        change (g : Matrix (Fin n) (Fin n) ℂ).det - 1 = 0
        rw [hg'.2, sub_self]
      have hz := hv _ hf
      rwa [g2k_differential_det_sub_one] at hz
  · rintro ⟨hX, ht⟩
    intro f hf
    have hγ : ∀ i j, HasDerivAt (fun s : ℂ => NormedSpace.exp (s • X) i j) (X i j) 0 := by
      intro i j
      simpa using g2k_hasDerivAt_exp_mul X 1 0 i j
    have hd := g2k_hasDerivAt_differential (fun s => NormedSpace.exp (s • X)) X 0
      (by simp) hγ f
    have hz : (fun s : ℂ => eval (fun ij => NormedSpace.exp (s • X) ij.1 ij.2) f) =
        fun _ => 0 := by
      funext s
      have hh := g1_mem_vanishingIdealSet_iff.mp hf _
        (exp_mem_specialOrthogonalMatrixGroup Ω X hX ht s)
      change eval (fun ij => (g2k_expGL X s : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2) f = 0 at hh
      rw [g2k_coe_expGL] at hh
      exact hh
    rw [hz] at hd
    exact hd.unique (hasDerivAt_const 0 0)

#print axioms differential_isometryEquation
#print axioms exp_mem_specialOrthogonalMatrixGroup
#print axioms lie_specialOrthogonalMatrixGroup
end HodgeLean.Foundations.Abdulali
