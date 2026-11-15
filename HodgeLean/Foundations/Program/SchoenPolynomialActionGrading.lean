import HodgeLean.Foundations.Program.SchoenPolynomialPermutationAction
import HodgeLean.Foundations.Program.SchoenSubmoduleGradingBridge
import HodgeLean.Foundations.Program.SchoenSegreCoordinateCoefficients

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial permutation action preserves every retained homogeneous degree piece. -/
theorem s2_polynomialPermutationAction_preserves_grading (R : Type) [CommRing R]
    (d n : ℕ) {G : Type} [Group G] (σ : G →* Equiv.Perm (Fin n)) :
    letI := s2_polynomialPermutationAction R d n σ
    ∀ g : G, ∀ m, ∀ (a : MvPolynomial (Fin n → Fin (d + 1)) R), a ∈ s2_submoduleGradedPieces
      (homogeneousSubmodule (Fin n → Fin (d + 1)) R) m →
        g • a ∈ s2_submoduleGradedPieces
          (homogeneousSubmodule (Fin n → Fin (d + 1)) R) m := by
  letI := s2_polynomialPermutationAction R d n σ
  intro g m a ha
  exact (s2_segreCoordinateRename R d n (σ g).symm).map_mem ha

/-- The actual polynomial permutation action fixes every retained degree-zero element pointwise. -/
theorem s2_polynomialPermutationAction_fixes_degreeZero (R : Type) [CommRing R]
    (d n : ℕ) {G : Type} [Group G] (σ : G →* Equiv.Perm (Fin n)) :
    letI := s2_polynomialPermutationAction R d n σ
    ∀ g : G, ∀ (a : MvPolynomial (Fin n → Fin (d + 1)) R),
      a ∈ s2_submoduleGradedPieces (homogeneousSubmodule (Fin n → Fin (d + 1)) R) 0 →
        g • a = a := by
  letI := s2_polynomialPermutationAction R d n σ
  intro g a ha
  exact s2_segreCoordinateRename_degreeZero R d n (σ g).symm ⟨a, ha⟩

end HodgeLean.Foundations.Program
