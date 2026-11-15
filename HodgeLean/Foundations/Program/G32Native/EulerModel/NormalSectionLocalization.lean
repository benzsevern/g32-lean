import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalSectionHomotopy
import HodgeLean.Foundations.AlgebraicTopology.RelativeCohomology.ProductTrace

/-! # Localization of zero-section pullback at the global section's unique zero -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The global section gives a map from the complement of its unique zero to the nonzero vectors. -/
def projectiveNormalSectionPairMap (k : ℕ) :
    TopPair.ofSubset (X := TopCat.of (Projectivization ℂ (ℂ × (Fin k → ℂ))))
      ({normalProjectiveBase k} : Set _)ᶜ ⟶
    TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k))
      {v : ProjectiveNormalTotalSpace k | v.1.2 = 0}ᶜ :=
  TopPair.ofHom
    (TopCat.ofHom ⟨projectiveNormalSectionMap k, continuous_projectiveNormalSectionMap k⟩)
    (TopCat.ofHom ⟨fun p => ⟨projectiveNormalSectionMap k p.1, by
      intro h
      exact p.2 ((projectiveNormalSectionVector_zero_iff k p.1).mp h)⟩,
      ((continuous_projectiveNormalSectionMap k).comp continuous_subtype_val).subtype_mk
        (fun (p : {p : Projectivization ℂ (ℂ × (Fin k → ℂ)) //
          p ∉ ({normalProjectiveBase k} : Set _)}) h =>
            p.2 ((projectiveNormalSectionVector_zero_iff k p.1).mp h))⟩)
    (by ext; rfl)

#print axioms projectiveNormalSectionPairMap

/-- Zero-section pullback is the absolute image of a class supported at the section's unique zero. -/
theorem projectiveNormalZeroSection_localization (k n : ℕ)
    (α : CohomologyWithSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k))
      {v : ProjectiveNormalTotalSpace k | v.1.2 = 0} n) :
    cohomologyMap ℚ n (TopCat.ofHom (projectiveNormalZeroSection k))
      (forgetSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k))
        {v : ProjectiveNormalTotalSpace k | v.1.2 = 0} n α) =
      relativeCohomologyToAbsolute ℚ _ n
        (relativeCohomologyMap ℚ n (projectiveNormalSectionPairMap k) α) := by
  rw [projectiveNormalSection_cohomology_pullback]
  exact (RelativeTrace.forget_naturality (projectiveNormalSectionPairMap k) n α).symm

#print axioms projectiveNormalZeroSection_localization
end HodgeLean.Foundations.Program.G32Native.EulerModel
