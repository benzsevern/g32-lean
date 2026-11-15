import HodgeLean.Foundations.BundleThom.DegreeZeroCoverHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.HomologyZeroNaturality
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing

/-! # Degree-zero homology maps into path-connected targets

The augmentation determines the map, and punctured positive complex coordinate space is path-connected.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Two actual continuous maps to a path-connected space induce equal degree-zero rational homology maps.
Source: Hatcher, Algebraic Topology, §2.1, degree-zero homology augmentation. -/
theorem i1_homologyZero_map_eq_of_pathConnectedTarget {X Y : TopCat} [PathConnectedSpace Y]
    (f g : X ⟶ Y) :
    HomologicalComplex.homologyMap (singularChainComplexMap ℚ f) 0 =
      HomologicalComplex.homologyMap (singularChainComplexMap ℚ g) 0 := by
  change ((singularHomologyFunctor.{0} (ModuleCat.{0} ℚ) 0).obj (ModuleCat.of ℚ ℚ)).map f =
    ((singularHomologyFunctor.{0} (ModuleCat.{0} ℚ) 0).obj (ModuleCat.of ℚ ℚ)).map g
  apply (cancel_mono (Y.singularHomology₀ε (ModuleCat.of ℚ ℚ))).mp
  rw [TopCat.singularHomology₀ε_naturality, TopCat.singularHomology₀ε_naturality]

/-- Punctured complex coordinate space in every positive complex rank is path-connected.
Source: Hatcher, Algebraic Topology, §0, path connectivity of punctured Euclidean space in real dimension at least two. -/
theorem i1_complexPunctured_pathConnectedSpace (k : ℕ) (hk : 0 < k) :
    PathConnectedSpace (puncturedPair ℂ k).snd := by
  haveI := puncturedPair_pathConnectedSpace (k * 2) (by omega)
  let e : (puncturedPair ℂ k).snd ≃ₜ (puncturedPair ℝ (k * 2)).snd :=
    TopCat.homeoOfIso (TopPair.proj₂.mapIso (standardComplexRealPairIso k))
  exact e.symm.pathConnectedSpace

end HodgeLean.Foundations.BundleThom
