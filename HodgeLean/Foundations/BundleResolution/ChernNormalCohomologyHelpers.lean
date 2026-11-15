import HodgeLean.Foundations.BundleResolution.ChernNormalCoclassBasisHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.EuclideanVanishing

/-! # Cohomology of the actual complex normal pair

The real-coordinate pair identification transports the Euclidean local
homology calculation to the actual complex normal pair in every degree.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_complexNormal_cohomology_subsingleton_of_ne (k n : ℕ) (hn : n ≠ 2 * k) :
    Subsingleton (RelativeCohomology ℚ (puncturedPair ℂ k) n) := by
  let e := ((relativeHomologyFunctor ℚ n).mapIso (standardComplexRealPairIso k)).toLinearEquiv
  letI := ModuleCat.subsingleton_of_isZero
    (standardLocalHomology_isZero_of_ne (k * 2) n (by omega))
  exact relativeCohomology_subsingleton ℚ (puncturedPair ℂ k) n e.injective.subsingleton

theorem i1_complexNormal_cohomology_finite (k n : ℕ) :
    Module.Finite ℚ (RelativeCohomology ℚ (puncturedPair ℂ k) n) := by
  by_cases hn : n = 2 * k
  · subst n
    exact Module.Finite.equiv (LinearEquiv.ofBijective _
      (i1_normalizedPointCoclass_scalar_bijective k))
  · letI := i1_complexNormal_cohomology_subsingleton_of_ne k n hn
    infer_instance

end HodgeLean.Foundations.BundleResolution
