import HodgeLean.Adapters.NormalConeB4Defs

/-! Maps between the specified support neighbourhoods and their ambient pairs. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The specified continuous map restricted to actual supported neighbourhoods. -/
def s4_q3_neighbourhood_support_map
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (f : C(M, N)) (S : Set M) (T : Set N) (V : Set M) (W : Set N)
    (hVW : ∀ y ∈ V, f y ∈ W) (hST : ∀ y ∈ V, f y ∈ T → y ∈ S) :
    neighborhoodSupportComplementPair V S ⟶ neighborhoodSupportComplementPair W T :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun y : V => ⟨f y.1, hVW y.1 y.2⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (by intro y hy h; exact hy (hST y.1 y.2 h))

/-- Restricting a supported pullback agrees with pulling back on the actual
source and target neighbourhoods. -/
theorem s4_q3_neighbourhood_support_map_ambient
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (f : C(M, N)) (S : Set M) (T : Set N) (V : Set M) (W : Set N)
    (hVW : ∀ y ∈ V, f y ∈ W) (hST : ∀ y, f y ∈ T → y ∈ S) :
    s4_q3_neighbourhood_support_map f S T V W hVW (fun y _ => hST y) ≫
      a3b4_neighborhoodPairMap W T =
    a3b4_neighborhoodPairMap V S ≫
      a3b4_supportPairMap (TopCat.ofHom f) S T hST := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl

end HodgeLean.Foundations.Program
