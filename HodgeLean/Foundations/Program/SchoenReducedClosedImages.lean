import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- Two reduced scheme closed immersions with the same actual image identify their source schemes over the target. -/
theorem s2_reducedClosedImmersion_iso_of_range_eq {X Y Z : Scheme.{0}}
    [IsReduced X] [IsReduced Y] (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] (h : Set.range f = Set.range g) :
    ∃ e : X ≅ Y, e.hom ≫ g = f := by
  haveI : Surjective (pullback.fst f g) := ⟨by
    intro x
    change x ∈ Set.range (pullback.fst f g)
    rw [Scheme.Pullback.range_fst, ← h]
    exact Set.mem_range_self x⟩
  haveI : Surjective (pullback.snd f g) := ⟨by
    intro y
    change y ∈ Set.range (pullback.snd f g)
    rw [Scheme.Pullback.range_snd, h]
    exact Set.mem_range_self y⟩
  haveI : IsIso (pullback.fst f g) := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso (pullback.snd f g) := isIso_of_isClosedImmersion_of_surjective _
  let e : X ≅ Y := (asIso (pullback.fst f g)).symm ≪≫ asIso (pullback.snd f g)
  refine ⟨e, ?_⟩
  change (inv (pullback.fst f g) ≫ pullback.snd f g) ≫ g = f
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

/-- The image of an integral scheme under a closed immersion is the closure of its generic image point. -/
theorem s2_closedImmersion_range_genericPoint {X Z : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Z) [IsClosedImmersion f] :
    Set.range f = closure ({f (genericPoint X)} : Set Z) := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ closure ({genericPoint X} : Set X) := by
      rw [genericPoint_closure]
      trivial
    have h := image_closure_subset_closure_image f.continuous (Set.mem_image_of_mem f hx)
    simpa only [Set.image_singleton] using h
  · exact closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_range_self _))
      (f.isClosedEmbedding.isClosed_range)

end HodgeLean.Foundations.Program
