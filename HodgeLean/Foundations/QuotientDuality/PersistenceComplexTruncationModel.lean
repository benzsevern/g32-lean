import HodgeLean.Foundations.QuotientDuality.PersistenceComplexEquationModel
import HodgeLean.Foundations.Program.SchoenTowerT11bBallFormula

/-! Actual compact marked Boolean models on complex coordinate truncations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Foundations.Program HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_complex_equation_truncation_model {n m k : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) (q : Fin k → MvPolynomial (Fin n) ℂ)
    (c : EuclideanSpace ℝ (Fin (n + n))) (r : ℝ) (hr : 0 ≤ r) :
    let T := zeroSet p ∩ (complexEuclideanCoordinates n) ⁻¹' Metric.closedBall c r
    ∃ f b : s2v_t11b_Formula (n + n), IsCompact f.realize ∧
      IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize) ∧
      ∃ e : T ≃ₜ f.realize, ∀ z : T, (e z).val ∈ b.realize ↔ z.val ∈ zeroSet q := by
  obtain ⟨f, hfc, hfp⟩ := persistence_complex_equation_formula p
  obtain ⟨b, hbc, hbq⟩ := persistence_complex_equation_formula q
  obtain ⟨g, hg⟩ := s2v_t11b_closedBall_formula c r hr
  let F : s2v_t11b_Formula (n + n) := .inter f g
  have hFc : IsCompact F.realize := by
    change IsCompact (f.realize ∩ g.realize)
    rw [hg]
    exact (isCompact_closedBall c r).inter_left hfc
  let e : ↥(zeroSet p ∩ (complexEuclideanCoordinates n) ⁻¹' Metric.closedBall c r) ≃ₜ
      F.realize := (complexEuclideanCoordinates n).sets (by
        ext z
        change (z ∈ zeroSet p ∧ complexEuclideanCoordinates n z ∈ Metric.closedBall c r) ↔
          (complexEuclideanCoordinates n z ∈ f.realize ∧
            complexEuclideanCoordinates n z ∈ g.realize)
        rw [hfp, hg])
  refine ⟨F, b, hFc, hbc.preimage continuous_subtype_val, e, ?_⟩
  intro z
  change complexEuclideanCoordinates n z.val ∈ b.realize ↔ z.val ∈ zeroSet q
  exact (hbq z.val).symm

end HodgeLean.Foundations.QuotientDuality
