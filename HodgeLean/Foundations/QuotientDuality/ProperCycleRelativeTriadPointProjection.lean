import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTriadUnion
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTriadNaturality

/-! # Original relative point restriction through the actual triad excision map
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original relative-to-triad map followed by actual point excision is precisely the original relative restriction to the point complement.
Source: properCycle_relative_triad_union; properCycle_subset_transport_map.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_triad_point_projection
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (x : X) (hU : A ∪ B = ({x} : Set X)ᶜ) (n : ℕ) :
    HomologicalComplex.homologyMap (properCycle_relative_to_triad_chain_map X A B) n ≫
        (properCycle_triad_local_homology_iso X A B hA hB x hU n).hom =
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (TopPair.ofSubsetHom (𝟙 X)
          (show Set.MapsTo (𝟙 X) A ({x} : Set X)ᶜ from fun _ ha => hU ▸ Or.inl ha))) n := by
  let i := TopPair.ofSubsetHom (𝟙 X)
    (show Set.MapsTo (𝟙 X) (A ∪ B) ({x} : Set X)ᶜ from fun _ h => hU ▸ h)
  let f := TopPair.ofSubsetHom (𝟙 X)
    (show Set.MapsTo (𝟙 X) A ({x} : Set X)ᶜ from fun _ ha => hU ▸ Or.inl ha)
  have hh : properCycle_relative_to_triad_chain_map X A B ≫
      triadToUnionRelativeChainMap ℚ X A B ≫ (relativeChainFunctor ℚ).map i =
      (relativeChainFunctor ℚ).map f := by
    rw [← Category.assoc, properCycle_relative_triad_union, ← CategoryTheory.Functor.map_comp]
    congr 1
  have he := congrArg (fun m => HomologicalComplex.homologyMap m n) hh
  simp only [HomologicalComplex.homologyMap_comp] at he
  unfold properCycle_triad_local_homology_iso
  dsimp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  dsimp only [i] at he
  rw [properCycle_subset_transport_map (A ∪ B) _ hU] at he
  exact he

end HodgeLean.Foundations.QuotientDuality
