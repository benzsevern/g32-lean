import HodgeLean.Foundations.BundleThom.Defs

/-! # Coclass detection in actual pair coordinates

An isomorphism of topological pairs detects classes by its actual pullback.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Pullback along an actual pair isomorphism is injective in every rational relative cohomology degree.
Source: Hatcher, Algebraic Topology, §3.1, functoriality for pair isomorphisms. -/
theorem i1_relativeCohomologyMap_iso_injective {P Q : TopPair} (e : P ≅ Q) (n : ℕ) :
    Function.Injective (relativeCohomologyMap ℚ n e.hom) := by
  have hi (u : RelativeCohomology ℚ Q n) :
      relativeCohomologyMap ℚ n e.inv (relativeCohomologyMap ℚ n e.hom u) = u := by
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      e.inv_hom_id, relativeCohomologyMap_id, LinearMap.id_apply]
  intro u v h
  exact (hi u).symm.trans ((congrArg (relativeCohomologyMap ℚ n e.inv) h).trans (hi v))

end HodgeLean.Foundations.BundleThom
