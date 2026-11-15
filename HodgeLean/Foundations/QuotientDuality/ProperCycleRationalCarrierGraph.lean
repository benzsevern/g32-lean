import HodgeLean.Foundations.QuotientDuality.ProperCyclePolynomialMatrixEquations
import HodgeLean.Foundations.Semialgebraic.HardtMarkedImageHelpers

/-! # Actual Boolean graphs of rational coordinate maps -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Rational coordinate functions with a nonzero original denominator retain their literal Boolean graph on the supplied source carrier.
Source: properCycle_finite_equation_formula_iff; s2v_t11b_realize_subst.
HC no distance; AV milestone no distance. -/
theorem properCycle_rational_carrier_graph {n k : ℕ} (A : s2v_t11b_Formula n)
    (P : Fin k → MvPolynomial (Fin n) ℝ) (q : MvPolynomial (Fin n) ℝ)
    (hq : ∀ x : A.realize, MvPolynomial.eval x.val q ≠ 0)
    (f : A.realize → EuclideanSpace ℝ (Fin k))
    (hf : ∀ x j, f x j = MvPolynomial.eval x.val (P j) / MvPolynomial.eval x.val q) :
    ∃ G : s2v_t11b_Formula (n + k), ∀ z, z ∈ G.realize ↔ ∃ x : A.realize,
      (∀ i, z (Fin.castAdd k i) = x.val i) ∧
      (∀ j, z (Fin.natAdd n j) = f x j) := by
  let σ : Fin n → Fin (n+k) := Fin.castAdd k
  let G := (A.subst (fun i => MvPolynomial.X (σ i))).inter
    (properCycle_finite_equation_formula fun j =>
      MvPolynomial.X (Fin.natAdd n j) * MvPolynomial.rename σ q -
        MvPolynomial.rename σ (P j))
  refine ⟨G, ?_⟩
  intro z
  change (_ ∧ _) ↔ _
  rw [s2v_t11b_realize_subst, properCycle_finite_equation_formula_iff]
  simp only [MvPolynomial.eval_X, map_sub, map_mul, MvPolynomial.eval_rename]
  let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => z (σ i))
  change (u ∈ A.realize ∧ ∀ j, z (Fin.natAdd n j) * MvPolynomial.eval u q -
      MvPolynomial.eval u (P j) = 0) ↔ _
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨⟨u, hu⟩, fun _ => rfl, ?_⟩
    intro j
    rw [hf]
    exact (eq_div_iff (hq ⟨u, hu⟩)).mpr (sub_eq_zero.mp (h j))
  · rintro ⟨x, hx, hy⟩
    have hu : u = x.val := by ext i; exact hx i
    refine ⟨hu.symm ▸ x.property, ?_⟩
    intro j
    rw [hu, hy j, hf]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ (hq x))

/-- The literal image of a rational coordinate map on any retained Boolean mark has an actual Boolean formula.
Source: properCycle_rational_carrier_graph; Semialgebraic.ScalarTriangulation.actual_marked_image_formula.
HC no distance; AV milestone no distance. -/
theorem properCycle_rational_carrier_image {n k : ℕ} (A b : s2v_t11b_Formula n)
    (P : Fin k → MvPolynomial (Fin n) ℝ) (q : MvPolynomial (Fin n) ℝ)
    (hq : ∀ x : A.realize, MvPolynomial.eval x.val q ≠ 0)
    (f : A.realize → EuclideanSpace ℝ (Fin k))
    (hf : ∀ x j, f x j = MvPolynomial.eval x.val (P j) / MvPolynomial.eval x.val q) :
    ∃ B : s2v_t11b_Formula k, ∀ y, y ∈ B.realize ↔
      ∃ x : A.realize, f x = y ∧ x.val ∈ b.realize := by
  obtain ⟨G, hG⟩ := properCycle_rational_carrier_graph A P q hq f hf
  exact Semialgebraic.ScalarTriangulation.actual_marked_image_formula A b f G hG

end HodgeLean.Foundations.QuotientDuality
