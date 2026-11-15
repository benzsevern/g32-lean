import HodgeLean.Foundations.BundleResolution.ChernRelativeCocycleClassHelpers
import HodgeLean.Foundations.BundleResolution.ChernCocyclePairingHelpers
import HodgeLean.Foundations.Singular.TensorDegreeSum

/-! # Short-complex representatives of relative tensor classes

The canonical factor comparisons retain actual relative and absolute
cocycle representatives in each tensor bidegree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.BundleResolution

def i1_relativeShortTensorEquiv (P : TopPair) (Y : TopCat) (p q : ℕ) :
    (RelativeCohomology ℚ P p ⊗[ℚ] Cohomology ℚ Y q) ≃ₗ[ℚ]
      ((((relativeChainFunctor ℚ).obj P).sc p).linearDual.homology ⊗[ℚ]
        ((rationalChains Y).sc q).linearDual.homology) :=
  TensorProduct.congr (relativeCochainCohomologyEquiv ℚ P p).symm
    (cochainCohomologyEquiv ℚ Y q).symm

def i1_relativeShortDegreeSumEquiv (P : TopPair) (Y : TopCat) (n : ℕ) :
    (⨁ a : tensorDegreeIndex n,
      RelativeCohomology ℚ P a.val.1 ⊗[ℚ] Cohomology ℚ Y a.val.2) ≃ₗ[ℚ]
    (⨁ a : tensorDegreeIndex n,
      ((((relativeChainFunctor ℚ).obj P).sc a.val.1).linearDual.homology ⊗[ℚ]
        ((rationalChains Y).sc a.val.2).linearDual.homology)) :=
  DirectSum.congrLinearEquiv (fun a => i1_relativeShortTensorEquiv P Y a.val.1 a.val.2)

theorem i1_relativeShortTensorEquiv_classes (P : TopPair) (Y : TopCat) (p q : ℕ)
    (φ : RelativeCocycle ℚ P p) (ψ : Cocycle ℚ (TopCat.toSSet.obj Y) q) :
    i1_relativeShortTensorEquiv P Y p q
      (i1_relativeCocycleClass P p φ ⊗ₜ[ℚ] cohomologyClass Y q ψ) =
        (((relativeChainFunctor ℚ).obj P).sc p).linearDual.moduleCatHomologyClass
            (i1_relativeCocycleToDualCycle P p φ) ⊗ₜ[ℚ]
          ((rationalChains Y).sc q).linearDual.moduleCatHomologyClass (i1_cocycleToDualCycle Y q ψ) := by
  have hφ : (relativeCochainCohomologyEquiv ℚ P p).symm (i1_relativeCocycleClass P p φ) =
      (((relativeChainFunctor ℚ).obj P).sc p).linearDual.moduleCatHomologyClass
        (i1_relativeCocycleToDualCycle P p φ) :=
    (LinearEquiv.symm_apply_eq (relativeCochainCohomologyEquiv ℚ P p)).mpr rfl
  have hψ : (cochainCohomologyEquiv ℚ Y q).symm (cohomologyClass Y q ψ) =
      ((rationalChains Y).sc q).linearDual.moduleCatHomologyClass (i1_cocycleToDualCycle Y q ψ) :=
    (LinearEquiv.symm_apply_eq (cochainCohomologyEquiv ℚ Y q)).mpr rfl
  exact (TensorProduct.congr_tmul (relativeCochainCohomologyEquiv ℚ P p).symm
    (cochainCohomologyEquiv ℚ Y q).symm _ _).trans
      (congrArg₂ (fun u v => u ⊗ₜ[ℚ] v) hφ hψ)

theorem i1_relativeShortDegreeSumEquiv_classes (P : TopPair) (Y : TopCat) (p q : ℕ)
    (φ : RelativeCocycle ℚ P p) (ψ : Cocycle ℚ (TopCat.toSSet.obj Y) q) :
    i1_relativeShortDegreeSumEquiv P Y (p + q)
      (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
        (fun a => RelativeCohomology ℚ P a.val.1 ⊗[ℚ] Cohomology ℚ Y a.val.2)
        ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
        (i1_relativeCocycleClass P p φ ⊗ₜ[ℚ] cohomologyClass Y q ψ)) =
      DirectSum.lof ℚ (tensorDegreeIndex (p + q))
        (fun a => ((((relativeChainFunctor ℚ).obj P).sc a.val.1).linearDual.homology ⊗[ℚ]
          ((rationalChains Y).sc a.val.2).linearDual.homology))
        ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
        ((((relativeChainFunctor ℚ).obj P).sc p).linearDual.moduleCatHomologyClass
            (i1_relativeCocycleToDualCycle P p φ) ⊗ₜ[ℚ]
          ((rationalChains Y).sc q).linearDual.moduleCatHomologyClass (i1_cocycleToDualCycle Y q ψ)) := by
  let a : tensorDegreeIndex (p + q) := ⟨(p, q), Finset.mem_antidiagonal.mpr rfl⟩
  have h := DirectSum.lmap_lof
    (fun b : tensorDegreeIndex (p + q) =>
      (i1_relativeShortTensorEquiv P Y b.val.1 b.val.2).toLinearMap) a
    (i1_relativeCocycleClass P p φ ⊗ₜ[ℚ] cohomologyClass Y q ψ)
  exact h.trans (congrArg (DirectSum.lof ℚ (tensorDegreeIndex (p + q))
    (fun b => ((((relativeChainFunctor ℚ).obj P).sc b.val.1).linearDual.homology ⊗[ℚ]
      ((rationalChains Y).sc b.val.2).linearDual.homology)) a)
        (i1_relativeShortTensorEquiv_classes P Y p q φ ψ))

end HodgeLean.Foundations.BundleResolution
