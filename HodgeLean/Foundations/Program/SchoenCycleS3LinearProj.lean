import HodgeLean.Foundations.Program.SchoenCycleS3LinearSubstitution
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Projective spectra under a complex linear coordinate change -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The polynomial automorphism of a linear coordinate change respects the grading. -/
def s2e_gradedLinearSubstitution {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    homogeneousSubmodule (Fin n) ℂ →+*ᵍ homogeneousSubmodule (Fin n) ℂ :=
  { (s2e_linearSubstitutionEquiv e).toRingHom with
    map_mem := fun hp => s2e_linearSubstitution_homogeneous e.toLinearMap _ hp }

/-- Linear substitution maps the irrelevant ideal onto itself. -/
theorem s2e_gradedLinearSubstitution_irrelevant {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin n) ℂ) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin n) ℂ)).map
        (s2e_gradedLinearSubstitution e) := by
  let f := s2e_gradedLinearSubstitution e
  let g := s2e_gradedLinearSubstitution e.symm
  have hfg (x : MvPolynomial (Fin n) ℂ) : f (g x) = x :=
    (s2e_linearSubstitutionEquiv e).apply_symm_apply x
  intro x hx
  rw [← hfg x]
  apply Ideal.mem_map_of_mem
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hx
  change GradedRing.proj (homogeneousSubmodule (Fin n) ℂ) 0 (g x) = 0
  rw [GradedRing.proj_apply] at hx ⊢
  rw [← g.map_directSumDecompose, hx, map_zero]

/-- The complex polynomial projective spectrum has the automorphism from a linear basis change. -/
def s2e_linearProjIso {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Proj (homogeneousSubmodule (Fin n) ℂ) ≅ Proj (homogeneousSubmodule (Fin n) ℂ) where
  hom := Proj.map (s2e_gradedLinearSubstitution e) (s2e_gradedLinearSubstitution_irrelevant e)
  inv := Proj.map (s2e_gradedLinearSubstitution e.symm)
    (s2e_gradedLinearSubstitution_irrelevant e.symm)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have hh : (s2e_gradedLinearSubstitution e).comp (s2e_gradedLinearSubstitution e.symm) =
        GradedRingHom.id _ := by
      ext x : 1
      exact (s2e_linearSubstitutionEquiv e).apply_symm_apply x
    simpa only [hh] using (Proj.map_id (𝒜 := homogeneousSubmodule (Fin n) ℂ))
  inv_hom_id := by
    rw [← Proj.map_comp]
    have hh : (s2e_gradedLinearSubstitution e.symm).comp (s2e_gradedLinearSubstitution e) =
        GradedRingHom.id _ := by
      ext x : 1
      exact (s2e_linearSubstitutionEquiv e).symm_apply_apply x
    simpa only [hh] using (Proj.map_id (𝒜 := homogeneousSubmodule (Fin n) ℂ))

end HodgeLean.Foundations.Program
