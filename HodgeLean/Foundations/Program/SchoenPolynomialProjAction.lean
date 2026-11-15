import HodgeLean.Foundations.Program.SchoenPolynomialActionGrading
import HodgeLean.Foundations.Program.SchoenProjAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial ring action induces the retained tuple-coordinate scheme permutations under the subgroup grading comparison. -/
theorem s2_polynomialProjAction_comparison (R : Type) [CommRing R]
    (d n : ℕ) {G : Type} [Group G] (σ : G →* Equiv.Perm (Fin n)) (g : G) :
    let 𝒢 := homogeneousSubmodule (Fin n → Fin (d + 1)) R
    let 𝒜 := s2_submoduleGradedPieces 𝒢
    letI := s2_submoduleGradingAsSubgroups 𝒢
    letI := s2_polynomialPermutationAction R d n σ
    (s2_projAction 𝒜 (s2_polynomialPermutationAction_preserves_grading R d n σ) g).asIso.hom ≫
        (s2_submoduleGradingProjIso 𝒢).hom =
      (s2_submoduleGradingProjIso 𝒢).hom ≫ s2_segreCoordinateMap R d n (σ g) := by
  let 𝒢 := homogeneousSubmodule (Fin n → Fin (d + 1)) R
  let 𝒜 := s2_submoduleGradedPieces 𝒢
  letI := s2_submoduleGradingAsSubgroups 𝒢
  letI := s2_polynomialPermutationAction R d n σ
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro a
  change MvPolynomial.rename (fun b i => b ((σ g⁻¹).symm i)) a =
    MvPolynomial.rename (fun b i => b (σ g i)) a
  simp only [map_inv, Equiv.Perm.inv_def, Equiv.symm_symm]

end HodgeLean.Foundations.Program
