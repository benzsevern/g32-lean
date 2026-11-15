import Mathlib.RingTheory.GradedAlgebra.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The additive pieces determine the actual graded-ring decomposition uniquely. -/
theorem s2_gradedRing_eq {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) (g h : GradedRing 𝒜) : g = h := by
  cases g
  cases h
  congr 1
  exact Subsingleton.elim _ _

end HodgeLean.Foundations.Program
