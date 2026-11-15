import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

/-- Finite-dimensional cap bijectivity and the actual evaluation equation give a perfect pairing. -/
theorem retained_pairing_perfect_of_cap
    {V H : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    [AddCommGroup H] [Module ℚ H]
    (B : V →ₗ[ℚ] Module.Dual ℚ V) (K : V →ₗ[ℚ] H)
    (U : V ≃ₗ[ℚ] Module.Dual ℚ H) (hK : Function.Bijective K)
    (hpair : ∀ a b, B a b = U b (K a)) : Function.Bijective B := by
  letI : Module.Finite ℚ H := Module.Finite.of_surjective K hK.2
  let e : V ≃ₗ[ℚ] Module.Dual ℚ V :=
    ((LinearEquiv.ofBijective K hK).trans (Module.evalEquiv ℚ H)).trans U.dualMap
  have he : B = e.toLinearMap := by
    ext a b
    exact hpair a b
  rw [he]
  exact e.bijective

/-- Symmetry identifies the pairing directly with the dual cap equivalence. -/
theorem retained_symmetric_pairing_perfect_of_cap
    {V H : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup H] [Module ℚ H]
    (B : V →ₗ[ℚ] Module.Dual ℚ V) (K : V →ₗ[ℚ] H)
    (U : V ≃ₗ[ℚ] Module.Dual ℚ H) (hK : Function.Bijective K)
    (hpair : ∀ a b, B a b = U b (K a))
    (hsym : ∀ a b, B a b = B b a) : Function.Bijective B := by
  let e : V ≃ₗ[ℚ] Module.Dual ℚ V :=
    U.trans (LinearEquiv.ofBijective K hK).dualMap
  have he : B = e.toLinearMap := by
    ext a b
    exact (hsym a b).trans (hpair b a)
  rw [he]
  exact e.bijective

end HodgeLean.Foundations.QuotientDuality
