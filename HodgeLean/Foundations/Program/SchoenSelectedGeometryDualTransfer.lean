import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Surjectivity of singular pullback over a field detects injectivity of singular pushforward. -/
theorem s0_cohomology_surjective_iff_homology_injective
    (K : Type) [Field K] {X Y : TopCat} (n : ℕ) (f : X ⟶ Y) :
    Function.Surjective (cohomologyMap K n f) ↔
      Function.Injective (homologyMap K n f) := by
  rw [← LinearMap.dualMap_surjective_iff]
  let eX := cohomologyEquivDualHomology K X n
  let eY := cohomologyEquivDualHomology K Y n
  have hnat (a : Cohomology K Y n) :
      eX (cohomologyMap K n f a) = (homologyMap K n f).dualMap (eY a) := by
    ext z
    exact cohomologyEquivDualHomology_cohomologyMap K n f a z
  constructor
  · intro h b
    obtain ⟨a, ha⟩ := h (eX.symm b)
    refine ⟨eY a, ?_⟩
    rw [← hnat, ha, eX.apply_symm_apply]
  · intro h b
    obtain ⟨a, ha⟩ := h (eX b)
    refine ⟨eY.symm a, eX.injective ?_⟩
    rw [hnat, eY.apply_symm_apply, ha]

#print axioms s0_cohomology_surjective_iff_homology_injective
end HodgeLean.Foundations.Program
