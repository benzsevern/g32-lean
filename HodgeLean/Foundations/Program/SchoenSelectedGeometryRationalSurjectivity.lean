import HodgeLean.Foundations.Program.SchoenSelectedGeometryHomologyNaturality
import HodgeLean.Foundations.Program.SchoenSelectedGeometryDualTransfer

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Complex singular pullback surjectivity descends to rational coefficients. -/
theorem s0_rational_pullback_surjective_of_complex {X Y : TopCat} (n : ℕ) (f : X ⟶ Y)
    (h : Function.Surjective (cohomologyMap ℂ n f)) :
    Function.Surjective (cohomologyMap ℚ n f) := by
  apply (s0_cohomology_surjective_iff_homology_injective ℚ n f).mpr
  have hi := (s0_cohomology_surjective_iff_homology_injective ℂ n f).mp h
  intro x y hxy
  apply s0_qToCHomology_injective X n
  apply hi
  rw [← s0_qToCHomology_naturality, ← s0_qToCHomology_naturality, hxy]

#print axioms s0_rational_pullback_surjective_of_complex
end HodgeLean.Foundations.Program
