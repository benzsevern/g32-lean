import HodgeLean.Foundations.BundleThom.RelativeSubcomplexMonomorphismHelpers

/-! # Canonical projections to actual relative subcomplex chains

The supplied ambient and fixed relative subcomplexes remain in the chain quotient.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- The actual chain quotient projection modulo the supplied fixed subcomplex on a supplied ambient domain.
Source: Hatcher, Algebraic Topology, §2.1, relative chain quotients. -/
def i1_relativeSubcomplexProjection (X : SSet) (Z U : X.Subcomplex) :
    (i1_subcomplexChainFunctor X).obj U ⟶ (i1_relativeSubcomplexChainFunctor X Z).obj U :=
  cokernel.π ((i1_relativeSubcomplexArrowFunctor X Z).obj U).hom

/-- Actual relative chain projections commute with every supplied ambient subcomplex inclusion.
Source: Hatcher, Algebraic Topology, §2.1, relative quotient naturality. -/
theorem i1_relativeSubcomplexProjection_naturality (X : SSet) (Z U V : X.Subcomplex)
    (hUV : U ≤ V) :
    i1_relativeSubcomplexProjection X Z U ≫
      (i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUV) =
      (i1_subcomplexChainFunctor X).map (homOfLE hUV) ≫
        i1_relativeSubcomplexProjection X Z V :=
  ((coker.π (ChainComplex (ModuleCat ℚ) ℕ)).naturality
    ((i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE hUV))).symm

end HodgeLean.Foundations.BundleThom
