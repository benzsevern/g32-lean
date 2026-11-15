import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ComplexNeighborhoodOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarPointHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingLocalHomology

/-! # Actual ambient point excision for a retained support collar
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original triad excision followed by the actual neighborhood point map identifies the collar triad with ambient point homology, retaining the original inclusion point.
Source: ProperCycleSupportCollar.pointTriadIso; properCycle_open_embedding_local_homology_bijective.
HC no distance; AV milestone no distance. -/
def ProperCycleSupportCollar.pointAmbientIso {X : TopCat.{0}} {S : Set X} [T1Space X]
    (C : ProperCycleSupportCollar X S) (hS : IsClosed S) (z : S) (n : ℕ) :
    TriadRelativeHomology ℚ (TopCat.of C.neighborhood)
      (Subtype.val ⁻¹' Sᶜ) (C.retraction ⁻¹' ({z} : Set S)ᶜ) n ≅
      orientationGroup X n (C.inclusion z).val := by
  let i : TopCat.of C.neighborhood ⟶ X :=
    (TopPair.ofSubset (X := X) C.neighborhood).map
  let f := imagePointPairMap i Subtype.val_injective (C.inclusion z)
  letI : IsIso ((relativeHomologyFunctor ℚ n).map f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (properCycle_open_embedding_local_homology_bijective i
        C.isOpen.isOpenEmbedding_subtypeVal (C.inclusion z) n)
  exact C.pointTriadIso hS z n ≪≫ asIso ((relativeHomologyFunctor ℚ n).map f)

end HodgeLean.Foundations.QuotientDuality
