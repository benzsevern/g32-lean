import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.PeriodicFibreEnumeration
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Surjective single-orbit fibres have precisely the cardinality prescribed by their positive return divisors. -/
theorem periodic_fibre_cardinality
    {X B : Type*} (d : X → X) (p : X → B) (N : B → ℕ)
    (hN : ∀ b, 0 < N b) (hp : ∀ x, p (d x) = p x)
    (hsurj : Function.Surjective p)
    (horbit : ∀ x y, p x = p y → ∃ k : ℕ, d^[k] x = y)
    (hreturn : ∀ x k, d^[k] x = x ↔ N (p x) ∣ k) (b : B) :
    Finite {x : X // p x = b} ∧ Nat.card {x : X // p x = b} = N b := by
  obtain ⟨x, hx⟩ := hsurj b
  obtain ⟨E, hE⟩ := periodic_fibre_enumeration d p x (N (p x)) (hN (p x)) hp
    (fun y hy => horbit x y hy.symm) (hreturn x)
  have hfinite : Finite {y : X // p y = p x} := Finite.of_equiv _ E
  have hcard : Nat.card {y : X // p y = p x} = N (p x) := by
    rw [← Nat.card_congr E, Nat.card_fin]
  rw [hx] at hfinite hcard
  exact ⟨hfinite, hcard⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
