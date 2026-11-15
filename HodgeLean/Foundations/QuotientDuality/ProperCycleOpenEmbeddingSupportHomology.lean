import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingLocalHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodFundamental
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ComplexNeighborhoodOrientation

/-! # Actual support homology through original open embeddings -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- An original open embedding is bijective on the literal support homology map whenever the actual image support is closed.
Source: b6m_closed_support_excision_bijective; TopPair.isoOfSubset; imageSupportPairMap.
HC no distance; AV milestone no distance. -/
theorem properCycle_open_embedding_support_homology_bijective
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
    (S : Set X) (hS : IsClosed (f '' S)) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n (imageSupportPairMap f hf.injective S)) := by
  let U : Set Y := Set.range f
  have hU : IsOpen U := hf.isOpen_range
  let e : X ≃ₜ U := hf.isEmbedding.toHomeomorph
  let eP : TopPair.ofSubset (X := X) Sᶜ ≅ neighborhoodSupportComplementPair U (f '' S) :=
    TopPair.isoOfSubset e (by
      intro z
      change (f z ∉ f '' S) ↔ z ∉ S
      constructor
      · intro hz hs
        exact hz ⟨z, hs, rfl⟩
      · rintro hz ⟨w, hw, he⟩
        exact hz (hf.injective he ▸ hw))
  let i := b6m_subspacePairMap Y U (f '' S)ᶜ
  have he : Function.Bijective (relativeHomologyMap ℚ n eP.hom) :=
    ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map eP.hom) n)
  have hi : Function.Bijective (relativeHomologyMap ℚ n i) :=
    b6m_closed_support_excision_bijective ℚ hU hS
      (by rintro _ ⟨z, _, rfl⟩; exact ⟨z, rfl⟩) n
  have hp : eP.hom ≫ i = imageSupportPairMap f hf.injective S := by
    ext z : 2 <;> rfl
  have h := hi.comp he
  change Function.Bijective ((relativeHomologyMap ℚ n i).comp
    (relativeHomologyMap ℚ n eP.hom)) at h
  rw [← relativeHomologyMap_comp, hp] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
