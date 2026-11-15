import HodgeLean.Foundations.BundleResolution.ChernRelativeProductCupClassHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeShortTensorHelpers
import HodgeLean.Foundations.Singular.RationalTensorCohomologyClass

/-! # Relative Kunneth equivalence and actual cup products

Every pure tensor summand is sent to the relative cup product of the two
actual projection pullbacks.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.BundleResolution

theorem i1_relativeProductCohomologyEquiv_tmul (P : TopPair) (Y : TopCat)
    (hP : ∀ p, Module.Finite ℚ (RelativeCohomology ℚ P p)) (p q : ℕ)
    (α : RelativeCohomology ℚ P p) (β : Cohomology ℚ Y q) :
    i1_relativeProductCohomologyEquiv P Y hP (p + q)
      (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
        (fun a => RelativeCohomology ℚ P a.val.1 ⊗[ℚ] Cohomology ℚ Y a.val.2)
        ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩ (α ⊗ₜ[ℚ] β)) =
      i1_relativeCup (i1_relativeProductPair P Y) p q
        (relativeCohomologyMap ℚ p (i1_relativeProductFirst P Y) α)
        (cohomologyMap ℚ q (productSecond P.fst Y) β) := by
  obtain ⟨φ, rfl⟩ := i1_relativeCocycleClass_surjective P p α
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective Y q β
  have hK (r : ℕ) : Module.Finite ℚ
      ((((relativeChainFunctor ℚ).obj P).sc r).linearDual.homology) := by
    letI := hP r
    exact Module.Finite.of_surjective (relativeCochainCohomologyEquiv ℚ P r).symm.toLinearMap
      (relativeCochainCohomologyEquiv ℚ P r).symm.surjective
  change i1_relativeProductTensorCohomologyEquiv P Y (p + q)
    (rationalTensorCohomologyEquiv ((relativeChainFunctor ℚ).obj P) (rationalChains Y) hK (p + q)
      (i1_relativeShortDegreeSumEquiv P Y (p + q)
        (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
          (fun a => RelativeCohomology ℚ P a.val.1 ⊗[ℚ] Cohomology ℚ Y a.val.2)
          ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
          (i1_relativeCocycleClass P p φ ⊗ₜ[ℚ] cohomologyClass Y q ψ)))) = _
  rw [i1_relativeShortDegreeSumEquiv_classes, rationalTensorCohomologyEquiv_class]
  exact i1_relativeTensorScalarCycle_AW_class P Y p q φ ψ

end HodgeLean.Foundations.BundleResolution
