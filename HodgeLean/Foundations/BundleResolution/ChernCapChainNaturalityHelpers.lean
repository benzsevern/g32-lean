import HodgeLean.Foundations.BundleResolution.ChernRelativeCupNaturalityHelpers

/-! # Naturality of actual relative cap on chain representatives

The chain maps use the actual relative quotient and the actual absolute
singular chain functor, before passage to homology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.BundleResolution

theorem i1_relativeCap_chain_naturality {P Q : TopPair} (f : P ⟶ Q) (p q : ℕ)
    (φ : RelativeCochain ℚ Q p) (c : ((relativeChainFunctor ℚ).obj P).X (p + q)) :
    ((singularChainComplexMap ℚ (TopPair.Hom.fst f)).f q).hom
      (relativeCap ℚ P p q (i1_relativeCochainPullback f p φ) c) =
    relativeCap ℚ Q p q φ (((relativeChainFunctor ℚ).map f).f (p + q) c) := by
  apply (Module.Free.chooseBasis ℚ (ChainGroup ℚ (TopCat.toSSet.obj Q.fst) q)).eval_injective
  ext ψ
  have h := congrArg (fun η => η c) (i1_relativeCupCochain_naturality f p q φ ψ)
  exact h.symm

end HodgeLean.Foundations.BundleResolution
