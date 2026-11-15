import HodgeLean.Foundations.Program.SchoenTowerT11bParameterBooleanCoordinates
import HodgeLean.Foundations.Program.SchoenTowerT11bMvRootContinuation
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Regular-region projection charts for Boolean polynomial families in arbitrary parameter dimension.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open UniqueFactorizationMonoid

/-- Choose normalized associates for polynomial carriers over multivariate real coefficient rings.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, carrier factor-normalization step. -/
def s2v_t11b_mvParameterNormalization (n : ℕ) :
    StrongNormalizationMonoid (Polynomial (MvPolynomial (Fin n) ℝ)) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

attribute [local instance] s2v_t11b_mvParameterNormalization

/-- Boolean polynomial families have actual-fiber projection charts on connected regions where their radical carrier has simple degree-preserving fibers.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, regular cylindrical projection step. -/
theorem s2v_t11b_mv_regular_boolean_projection {n k : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) (hP : P ≠ 0)
    (Q : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (hdiv : ∀ i, Q i ≠ 0 → Q i ∣ P) (C : (Fin k → Bool) → Bool)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsPreconnected K) (a : K)
    (hlead : ∀ t ∈ K, MvPolynomial.eval (fun i => t i) (radical P).leadingCoeff ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, (radical P).eval₂ (MvPolynomial.eval (fun i => t i)) x = 0 →
      ((radical P).map (MvPolynomial.eval (fun i => t i))).derivative.eval x ≠ 0) :
    ∃ F : ({x : ℝ | C (fun i => decide (0 ≤ (Q i).eval₂ (MvPolynomial.eval (fun j => a.val j)) x)) = true} × K) ≃ₜ
        {z : K × ℝ | C (fun i => decide (0 ≤ (Q i).eval₂ (MvPolynomial.eval (fun j => z.1.val j)) z.2)) = true},
      ∀ y, (F y).val.1 = y.2 := by
  haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  obtain ⟨m, ψ, hc, hm, hr⟩ := s2v_t11b_mv_parameter_ordered_sections (radical P) K hK a hlead hsimple
  let φ : K → MvPolynomial (Fin n) ℝ →+* ℝ := fun t => MvPolynomial.eval (fun i => t.val i)
  have hφ : ∀ c, Continuous (fun t => φ t c) := fun c =>
    (s2v_t11b_mv_parameter_eval_contDiff c).continuous.comp continuous_subtype_val
  exact s2v_t11b_parameter_boolean_actual_fiber_chart φ hφ P hP Q hdiv C ψ hc hm hr
    (fun t x hx => hsimple t.val t.property x hx) a

end HodgeLean.Foundations.Program
