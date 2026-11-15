import HodgeLean.Foundations.Program.SchoenCycleC2ExcisionHelpers
import HodgeLean.Adapters.NormalConeB4Defs
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An open embedding whose image contains a closed support induces bijective
pullback on rational supported cohomology. -/
theorem s2e_openEmbedding_supported_pullback_bijective
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
    (S : Set Y) (hS : IsClosed S) (hSf : S ⊆ Set.range f) (n : ℕ) :
    Function.Bijective (cohomologyWithSupportMap ℚ n f S) := by
  let e := hf.isEmbedding.toHomeomorph
  let I : TopPair.ofSubset (X := X) (f ⁻¹' S)ᶜ ≅
      neighborhoodSupportComplementPair (Set.range f) S :=
    TopPair.isoOfSubset e (fun _ => Iff.rfl)
  have hI : Function.Bijective (relativeCohomologyMap ℚ n I.hom) := by
    apply s2e_relativeCohomologyMap_bijective_of_homology
    exact ConcreteCategory.bijective_of_isIso ((relativeHomologyFunctor ℚ n).map I.hom)
  have hJ := s2e_supportedCohomology_excision hf.isOpen_range hS hSf n
  have hcomp : I.hom ≫ a3b4_neighborhoodPairMap (Set.range f) S =
      preimageSupportPairMap f S := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext x
      rfl
    · ext x
      rfl
  unfold cohomologyWithSupportMap
  rw [← hcomp, relativeCohomologyMap_comp]
  exact hI.comp hJ

/-- The same excision comparison allows the source support to be specified by
its pointwise inverse-image characterization. -/
theorem s2e_openEmbedding_supportPairMap_bijective
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
    (S : Set X) (T : Set Y) (hT : IsClosed T) (hTf : T ⊆ Set.range f)
    (hST : ∀ x, f x ∈ T ↔ x ∈ S) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap ℚ n
      (a3b4_supportPairMap f S T (fun x hx => (hST x).mp hx))) := by
  have heq : S = f ⁻¹' T := Set.ext fun x => (hST x).symm
  subst S
  exact s2e_openEmbedding_supported_pullback_bijective f hf T hT hTf n

end HodgeLean.Foundations.Program
