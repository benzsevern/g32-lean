import HodgeLean.Foundations.Program.G32Native.PairedResidualDiagram

/-! # Immersions and supports of the canonical residual diagram -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

variable {C : Scheme} {P V : Over C} (i : P ⟶ V)
  [IsClosedImmersion i.left] (J : V.left.IdealSheafData)

instance residualUnionι_closed : IsClosedImmersion (residualUnionι i J).left :=
  inferInstanceAs (IsClosedImmersion (i.left.ker ⊓ J).subschemeι)

instance residualComponentι_closed :
    IsClosedImmersion (residualComponentι (V := V) J).left :=
  inferInstanceAs (IsClosedImmersion J.subschemeι)

instance residualUnionFirst_closed : IsClosedImmersion (residualUnionFirst i J).left := by
  haveI : IsClosedImmersion
      ((residualUnionFirst i J).left ≫ (residualUnionι i J).left) := by
    change IsClosedImmersion (residualUnionFirst i J ≫ residualUnionι i J).left
    rw [residualUnionFirst_fac]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (residualUnionι i J).left

instance residualIntersectionFirst_closed :
    IsClosedImmersion (residualIntersectionFirst i J).left := by
  haveI : IsClosedImmersion ((residualIntersectionFirst i J).left ≫ i.left) := by
    change IsClosedImmersion (residualIntersectionFirst i J ≫ i).left
    rw [residualIntersectionFirst_fac]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ i.left

instance residualIntersectionSecond_closed :
    IsClosedImmersion (residualIntersectionSecond i J).left := by
  have he : (residualIntersectionSecond i J).left ≫
      (residualComponentι (V := V) J).left = (i.left.ker ⊔ J).subschemeι :=
    (congrArg Over.Hom.left (residualIntersection_square i J)).symm.trans
      (residualIntersectionFirst_fac i J)
  haveI : IsClosedImmersion ((residualIntersectionSecond i J).left ≫
      (residualComponentι (V := V) J).left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (residualComponentι (V := V) J).left

/-- Noncontainment is a support comparison for the specified residual ideal. -/
theorem residual_noncontainment_iff :
    (¬ Set.range i.left ⊆ Set.range (residualComponentι (V := V) J).left) ↔
      ¬ (i.left.ker.support : Set V.left) ⊆ J.support := by
  have hi : (i.left.ker.support : Set V.left) = Set.range i.left := by
    rw [Scheme.Hom.support_ker, i.left.isClosedEmbedding.isClosed_range.closure_eq]
  change (¬ Set.range i.left ⊆ Set.range J.subschemeι) ↔ _
  rw [Scheme.IdealSheafData.range_subschemeι, hi]

/-- The canonical intersection has exactly the inverse-image support on the retained component. -/
theorem residualIntersectionFirst_range :
    Set.range (residualIntersectionFirst i J).left = i.left ⁻¹' (J.support : Set V.left) := by
  have he : (residualIntersectionFirst i J).left ≫ i.left =
      (i.left.ker ⊔ J).subschemeι := residualIntersectionFirst_fac i J
  have hi : (i.left.ker.support : Set V.left) = Set.range i.left := by
    rw [Scheme.Hom.support_ker, i.left.isClosedEmbedding.isClosed_range.closure_eq]
  ext p
  constructor
  · rintro ⟨s, rfl⟩
    have hs : (i.left.ker ⊔ J).subschemeι s ∈ (i.left.ker ⊔ J).support := by
      change (i.left.ker ⊔ J).subschemeι s ∈ ((i.left.ker ⊔ J).support : Set V.left)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨s, rfl⟩
    rw [Scheme.IdealSheafData.support_sup] at hs
    change i.left ((residualIntersectionFirst i J).left s) ∈ J.support
    rw [← Scheme.Hom.comp_apply, he]
    exact hs.2
  · intro hp
    have hs : i.left p ∈ (i.left.ker ⊔ J).support := by
      rw [Scheme.IdealSheafData.support_sup]
      exact ⟨hi.symm ▸ ⟨p, rfl⟩, hp⟩
    change i.left p ∈ ((i.left.ker ⊔ J).support : Set V.left) at hs
    rw [← Scheme.IdealSheafData.range_subschemeι] at hs
    obtain ⟨s, hs⟩ := hs
    refine ⟨s, i.left.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, he]
    exact hs

#print axioms residualUnionFirst_closed
#print axioms residualIntersectionFirst_closed
#print axioms residualIntersectionSecond_closed
#print axioms residual_noncontainment_iff
#print axioms residualIntersectionFirst_range

end HodgeLean.Foundations.Program.G32Native
