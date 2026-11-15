import HodgeLean.Foundations.Program.SchoenCycleChartIdeals
import Mathlib.Algebra.MvPolynomial.Division

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

theorem s2e_chart_coordinate_prime {k : ℕ} (i j : Fin (k + 1)) (h : j ≠ i) :
    (Ideal.span {s2e_s2b_chartHom i (chartCoordinate i j)}).IsPrime := by
  classical
  rw [s2e_chartHom_coordinate, dite_eq_right h]
  have hp : Prime (MvPolynomial.X ⟨j, h⟩ : MvPolynomial {q : Fin (k + 1) // q ≠ i} ℂ) :=
    MvPolynomial.X_prime
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

theorem s2e_chart_distinct_coordinate_not_mem {k : ℕ} (i j t : Fin (k + 1))
    (hji : j ≠ i) (htj : t ≠ j) :
    s2e_s2b_chartHom i (chartCoordinate i t) ∉
      Ideal.span {s2e_s2b_chartHom i (chartCoordinate i j)} := by
  classical
  let φ := MvPolynomial.eval₂Hom (RingHom.id ℂ)
    (fun q : {q : Fin (k + 1) // q ≠ i} => if q.val = j then (0 : ℂ) else 1)
  have hφ : Ideal.span {s2e_s2b_chartHom i (chartCoordinate i j)} ≤ RingHom.ker φ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change φ (s2e_s2b_chartHom i (chartCoordinate i j)) = 0
    rw [s2e_chartHom_coordinate, dite_eq_right hji]
    simp [φ]
  intro ht
  have hz := hφ ht
  rw [RingHom.mem_ker, s2e_chartHom_coordinate] at hz
  split_ifs at hz with hti
  · exact one_ne_zero (by simpa only [map_one] using hz)
  · simp [φ, htj] at hz

end HodgeLean.Foundations.Program
