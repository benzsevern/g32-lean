import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.RealCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Polynomial inequalities for Euclidean truncations.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.ComplexTopology

def radialPolynomial {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (r ^ 2) - ∑ i, (MvPolynomial.X i - MvPolynomial.C (x i)) ^ 2

lemma radialPolynomial_eval {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    MvPolynomial.eval y (radialPolynomial x r) = r ^ 2 - ‖y - x‖ ^ 2 := by
  simp only [radialPolynomial, map_sub, map_sum, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]

lemma radialPolynomial_nonneg_iff {n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ MvPolynomial.eval y (radialPolynomial x r) ↔ y ∈ Metric.closedBall x r := by
  rw [radialPolynomial_eval, sub_nonneg, Metric.mem_closedBall, dist_eq_norm]
  exact sq_le_sq₀ (norm_nonneg _) hr

def realPolynomialCarrier {n m : ℕ} (a b : Fin m → MvPolynomial (Fin n) ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | (∀ j, MvPolynomial.eval y (a j) = 0) ∧
    (∀ j, MvPolynomial.eval y (b j) = 0)}

lemma isClosed_realPolynomialCarrier {n m : ℕ}
    (a b : Fin m → MvPolynomial (Fin n) ℝ) :
    IsClosed (realPolynomialCarrier a b) := by
  have hc (q : MvPolynomial (Fin n) ℝ) :
      IsClosed {y : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval y q = 0} :=
    isClosed_eq (q.continuous_eval.comp (EuclideanSpace.equiv (Fin n) ℝ).continuous)
      continuous_const
  simpa only [realPolynomialCarrier, Set.setOf_and, Set.setOf_forall] using
    (isClosed_iInter fun j => hc (a j)).inter (isClosed_iInter fun j => hc (b j))

lemma compact_realPolynomial_truncation {n m : ℕ}
    (a b : Fin m → MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    IsCompact (realPolynomialCarrier a b ∩ Metric.closedBall x r) :=
  (isCompact_closedBall x r).inter_left (isClosed_realPolynomialCarrier a b)

end HodgeLean.Foundations.ComplexTopology
