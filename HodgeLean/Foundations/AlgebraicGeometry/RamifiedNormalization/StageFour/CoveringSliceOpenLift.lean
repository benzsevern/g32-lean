import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual covering-slice scheme lifts into an open normalization model containing the original centre neighbourhood. -/
theorem covering_slice_open_lift
    {N W X B : Over (Spec ↧ℂ)}
    (β : W ⟶ X) (b : X ⟶ B) (x : ComplexPoint B)
    (U : B.left.Opens) (hx : x.left (IsLocalRing.closedPoint ℂ) ∈ U)
    (J : N ⟶ W) [IsOpenImmersion J.left]
    (hrange : Set.range J.left = β.left ⁻¹' (b.left ⁻¹ᵁ U : Set X.left)) :
    ∃! l : coveringSlice β b x ⟶ N,
      l ≫ J = pullback.fst β (pullback.fst b x) := by
  let F := coveringSlice β b x
  let a := pullback.fst β (pullback.fst b x)
  let P := sliceProjection β b x
  have hbase : a ≫ β ≫ b = P ≫ pullback.snd b x ≫ x := by
    change pullback.fst β (pullback.fst b x) ≫ β ≫ b = _
    rw [← Category.assoc, pullback.condition, Category.assoc, pullback.condition]
  have hsub : Set.range a.left ⊆ Set.range J.left := by
    rintro _ ⟨z, rfl⟩
    rw [hrange]
    change b.left (β.left (a.left z)) ∈ U
    have hh := congrArg (fun m : F ⟶ B => m.left z) hbase
    change b.left (β.left (a.left z)) = x.left ((pullback.snd b x).left (P.left z)) at hh
    have hz : (pullback.snd b x).left (P.left z) = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := Spec ↧ℂ) _ _
    rw [hz] at hh
    rw [hh]
    exact hx
  let l := IsOpenImmersion.lift J.left a.left hsub
  have hl : l ≫ J.left = a.left := IsOpenImmersion.lift_fac _ _ _
  let lO : F ⟶ N := Over.homMk l (by
    rw [← J.w, ← Category.assoc, hl]
    exact a.w)
  haveI : Mono J := Over.mono_of_mono_left J
  refine ⟨lO, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hl
  · intro k hk
    apply (cancel_mono J).mp
    exact hk.trans (by apply Over.OverMorphism.ext; exact hl.symm)

end AlgebraicGeometry.RamifiedNormalization.StageFour
