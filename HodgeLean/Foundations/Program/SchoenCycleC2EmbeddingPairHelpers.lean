import HodgeLean.Foundations.Program.SchoenCycleC2EmbeddingExcisionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2LocalSupportHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An embedding identifies the supported pairs on a neighbourhood and its image. -/
def s2e_embeddingNeighbourhoodPairIso
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsEmbedding f)
    (S : Set X) (T : Set Y) (hST : ∀ x, f x ∈ T ↔ x ∈ S) (V : Set X) :
    neighborhoodSupportComplementPair V S ≅
      neighborhoodSupportComplementPair (f '' V) T :=
  TopPair.isoOfSubset (hf.homeomorphImage V) (fun x => not_congr (hST x.1))

/-- Supported restriction commutes with the neighbourhood pair identification. -/
theorem s2e_embeddingNeighbourhoodPairIso_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsEmbedding f)
    (S : Set X) (T : Set Y) (hST : ∀ x, f x ∈ T ↔ x ∈ S) (V : Set X) :
    (s2e_embeddingNeighbourhoodPairIso f hf S T hST V).hom ≫
      a3b4_neighborhoodPairMap (f '' V) T =
    a3b4_neighborhoodPairMap V S ≫
      a3b4_supportPairMap f S T (fun x hx => (hST x).mp hx) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    rfl
  · ext x
    rfl

/-- The neighbourhood pair identification preserves normal projection coclasses
when the chart coordinates commute with the embedding. -/
theorem s2e_embeddingNeighbourhoodPairIso_normalCoclass
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsEmbedding f)
    (S : Set X) (T : Set Y) (hST : ∀ x, f x ∈ T ↔ x ∈ S)
    (r k : ℕ)
    (E : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin k → ℂ)))
    (e : OpenPartialHomeomorph Y ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ x ∈ E.source, x ∈ S ↔ (E x).2 = 0)
    (hT : ∀ x ∈ e.source, x ∈ T ↔ (e x).2 = 0)
    (V : Set X) (hVE : V ⊆ E.source) (hVe : f '' V ⊆ e.source)
    (heval : ∀ x ∈ V, E x = e (f x)) :
    relativeCohomologyMap ℚ (2 * k)
      (s2e_embeddingNeighbourhoodPairIso f hf S T hST V).hom
      (chartNormalProjectionCoclass (Fin r → ℂ) k e T hT (f '' V) hVe) =
      chartNormalProjectionCoclass (Fin r → ℂ) k E S hS V hVE := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  congr 1
  congr 1
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    apply Subtype.ext
    exact (congrArg Prod.snd (heval x.1.1 x.1.2)).symm
  · ext x
    exact (congrArg Prod.snd (heval x.1 x.2)).symm

end HodgeLean.Foundations.Program
