import HodgeLean.Foundations.BundleResolution.ChernRelativeProductComparisonHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers
import HodgeLean.Foundations.Singular.RationalTensorCohomology
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Relative

/-! # Actual rational cohomology of relative products

The relative Alexander–Whitney quasi-isomorphism and the checked algebraic
tensor comparison give the finite-factor relative product equivalence.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular HodgeLean.Foundations.BundleThom
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.BundleResolution

def i1_relativeProductTensorCohomologyEquiv (P : TopPair) (Y : TopCat) (n : ℕ) :
    ((HomologicalComplex.tensorObj ((relativeChainFunctor ℚ).obj P)
      (rationalChains Y)).sc n).linearDual.homology ≃ₗ[ℚ]
        RelativeCohomology ℚ (i1_relativeProductPair P Y) n := by
  letI := i1_relativeProductAlexanderWhitney_quasiIso P Y
  exact (ShortComplex.homologyMapIso (linearDualCochainComplexScIso
    (HomologicalComplex.tensorObj ((relativeChainFunctor ℚ).obj P) (rationalChains Y)) n)).toLinearEquiv.symm.trans
      (i1_chainDualPullbackEquiv n (i1_relativeProductAlexanderWhitney P Y))

def i1_relativeProductCohomologyEquiv (P : TopPair) (Y : TopCat)
    (hP : ∀ p, Module.Finite ℚ (RelativeCohomology ℚ P p)) (n : ℕ) :
    (⨁ a : tensorDegreeIndex n,
      RelativeCohomology ℚ P a.val.1 ⊗[ℚ] Cohomology ℚ Y a.val.2) ≃ₗ[ℚ]
        RelativeCohomology ℚ (i1_relativeProductPair P Y) n := by
  have hK (p : ℕ) : Module.Finite ℚ
      ((((relativeChainFunctor ℚ).obj P).sc p).linearDual.homology) := by
    letI := hP p
    exact Module.Finite.of_surjective (relativeCochainCohomologyEquiv ℚ P p).symm.toLinearMap
      (relativeCochainCohomologyEquiv ℚ P p).symm.surjective
  exact (DirectSum.congrLinearEquiv (fun a : tensorDegreeIndex n =>
    TensorProduct.congr (relativeCochainCohomologyEquiv ℚ P a.val.1).symm
      (cochainCohomologyEquiv ℚ Y a.val.2).symm)).trans
    ((rationalTensorCohomologyEquiv ((relativeChainFunctor ℚ).obj P) (rationalChains Y) hK n).trans
      (i1_relativeProductTensorCohomologyEquiv P Y n))

end HodgeLean.Foundations.BundleResolution
