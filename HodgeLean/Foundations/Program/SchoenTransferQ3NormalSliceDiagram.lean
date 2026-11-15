import HodgeLean.Foundations.Program.SchoenTransferQ3CartesianSlices
import HodgeLean.Foundations.Program.SchoenTransferQ3ClosedBaseFibreLength
import HodgeLean.Foundations.Program.SchoenTransferQ3FibrePoints

/-! The actual finite flat diagram of compatible normal slices over a complex point. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Pullbacks over the same complex point construct smooth finite flat slices,
their ambient inclusions, and preservation of the unreduced point-fibre length. -/
theorem s4_q3_normal_slice_diagram
    {X W T : Over (Spec ↧ℂ)} (q : X ⟶ W) [IsFinite q.left] [Flat q.left]
    (h : W ⟶ T) [Smooth h.left] [Smooth (q ≫ h).left] (t : ComplexPoint T) :
    ∃ (P Q : Over (Spec ↧ℂ)) (u : P ⟶ X) (v : Q ⟶ W) (g : P ⟶ Q),
      u ≫ q = g ≫ v ∧
      IsPullback u.left g.left q.left v.left ∧
      IsPullback u.left P.hom (q ≫ h).left t.left ∧
      IsPullback v.left Q.hom h.left t.left ∧
      IsClosedImmersion u.left ∧ IsClosedImmersion v.left ∧
      IsFinite g.left ∧ Flat g.left ∧ Smooth P.hom ∧ Smooth Q.hom ∧
      ∀ p : P.left, SingularCycles.pointFibreLength g.left p =
        SingularCycles.pointFibreLength q.left (u.left p) := by
  let Q : Over (Spec ↧ℂ) := Over.mk (pullback.snd h.left t.left)
  let v : Q ⟶ W := Over.homMk (pullback.fst h.left t.left) (by
    change pullback.fst h.left t.left ≫ W.hom = pullback.snd h.left t.left
    rw [← Over.w h, ← Category.assoc, pullback.condition, Category.assoc, Over.w t]
    exact Category.comp_id _)
  let P : Over (Spec ↧ℂ) := Over.mk (pullback.snd q.left v.left ≫ Q.hom)
  let g : P ⟶ Q := Over.homMk (pullback.snd q.left v.left) rfl
  let u : P ⟶ X := Over.homMk (pullback.fst q.left v.left) (by
    change pullback.fst q.left v.left ≫ X.hom = pullback.snd q.left v.left ≫ Q.hom
    rw [← Over.w q, ← Category.assoc, pullback.condition, Category.assoc, Over.w v])
  have hq : IsPullback u.left g.left q.left v.left := IsPullback.of_hasPullback _ _
  have ht : IsPullback v.left Q.hom h.left t.left := IsPullback.of_hasPullback _ _
  have hp : IsPullback u.left P.hom (q ≫ h).left t.left := hq.paste_vert ht
  letI : IsClosedImmersion t.left := isClosedImmersion_of_comp_eq_id T.hom t.left (Over.w t)
  letI : IsClosedImmersion v.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) ht.flip inferInstance
  letI : IsClosedImmersion u.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hq.flip inferInstance
  have hP : Smooth P.hom := MorphismProperty.of_isPullback (P := @Smooth) hp inferInstance
  have hQ : Smooth Q.hom := inferInstanceAs (Smooth (pullback.snd h.left t.left))
  refine ⟨P, Q, u, v, g, ?_, hq, hp, ht, inferInstance, inferInstance,
    inferInstanceAs (IsFinite (pullback.snd q.left v.left)),
    inferInstanceAs (Flat (pullback.snd q.left v.left)), hP, hQ, ?_⟩
  · apply Over.OverMorphism.ext
    exact hq.w
  · intro p
    exact s4_q3_point_fibre_length_of_closed_base_change u.left g.left q.left v.left hq p

end HodgeLean.Foundations.Program
