import HodgeLean.Adapters.NormalConeB4aClassIntersection

/-! # Original finite-coheight primes do not specialize to distinct equal-coheight primes
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry TopologicalSpace HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Distinct original primes of the same finite coheight do not lie in one another's closures.
Source: a3b4a_classComponent_intersection_coheight.
HC no distance; AV milestone no distance. -/
lemma properCycle_pure_prime_not_mem_closure
    (X : Scheme.{0}) (k : ℕ) (ξ η : X) (hξη : ξ ≠ η)
    (hξ : Order.coheight ξ = k) (hη : Order.coheight η = k) :
    ξ ∉ closure ({η} : Set X) := by
  intro h
  have hi := a3b4a_classComponent_intersection_coheight X k ξ η ξ hξη hξ.ge hη.ge
    (subset_closure (Set.mem_singleton ξ)) h
  rw [hξ] at hi
  have hn : k+1 ≤ k := by exact_mod_cast hi
  omega

end HodgeLean.Foundations.QuotientDuality
