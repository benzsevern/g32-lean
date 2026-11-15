import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Literal polynomial coefficients of homogeneous linear relation rows -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- Read a linear row's coefficient at the specified original homogeneous variable. -/
def conormalLinearFormCoefficient {K : Type*} [CommRing K] (k : ℕ)
    (p : homogeneousSubmodule (Fin (k + 1)) K 1) (i : Fin (k + 1)) : K :=
  p.val.coeff (Finsupp.single i 1)

/-- The literal coefficients reconstruct the same original homogeneous linear polynomial. -/
theorem conormal_linear_form_eq_sum {K : Type*} [CommRing K] (k : ℕ)
    (p : homogeneousSubmodule (Fin (k + 1)) K 1) :
    p.val = ∑ i, conormalLinearFormCoefficient k p i • (X i : MvPolynomial (Fin (k + 1)) K) := by
  classical
  have hspan : p.val ∈ Submodule.span K
      (Set.range (X : Fin (k + 1) → MvPolynomial (Fin (k + 1)) K)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact p.property
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  have hc (i : Fin (k + 1)) : conormalLinearFormCoefficient k p i = a i := by
    unfold conormalLinearFormCoefficient
    rw [← ha]
    simp [coeff_smul, coeff_X, Finsupp.single_left_inj one_ne_zero]
  simp only [hc]
  exact ha.symm

/-- Evaluation of the same linear row is multiplication by its literal coefficient row. -/
theorem conormal_linear_form_eval {K : Type*} [CommRing K] (k : ℕ)
    (p : homogeneousSubmodule (Fin (k + 1)) K 1) (v : Fin (k + 1) → K) :
    eval v p.val = ∑ i, conormalLinearFormCoefficient k p i * v i := by
  rw [conormal_linear_form_eq_sum k p]
  simp only [map_sum, smul_eq_C_mul, map_mul, eval_C, eval_X]

end HodgeLean.Foundations.Program.G32Native
