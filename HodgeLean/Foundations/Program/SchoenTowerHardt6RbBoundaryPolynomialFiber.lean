import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundaryFiniteFiber
import Mathlib.Algebra.Polynomial.Roots

/-! Nonzero specialized polynomial constraints force unique boundary heights. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_polynomial_boundary_fiber_unique {E : Type*} [MetricSpace E]
    (C : Set E) (f : E → ℝ) (hf : ContinuousOn f C) (a : E)
    (hlocal : ∀ ε : ℝ, 0 < ε → IsPreconnected (C ∩ Metric.ball a ε))
    (P : E × ℝ → ℝ) (hP : ContinuousOn P (closure C ×ˢ Set.univ))
    (hroot : ∀ x ∈ C, P (x, f x) = 0)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hspec : ∀ t, P (a, t) = p.eval t) :
    Set.Subsingleton {t : ℝ | (a, t) ∈ closure ((fun x => (x, f x)) '' C)} := by
  have hgraph : closure ((fun x => (x, f x)) '' C) ⊆
      (closure C ×ˢ Set.univ) ∩ P ⁻¹' {0} := by
    apply closure_minimal ?_ (hP.preimage_isClosed_of_isClosed
      (isClosed_closure.prod isClosed_univ) isClosed_singleton)
    rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨subset_closure hx, Set.mem_univ _⟩, hroot x hx⟩
  apply s2v_hardt6rb_finite_boundary_fiber_unique C f hf a hlocal
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro t ht
  change p.eval t = 0
  exact (hspec t).symm.trans (hgraph ht).2

end HodgeLean.Foundations.Program
