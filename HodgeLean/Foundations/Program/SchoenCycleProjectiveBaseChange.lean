import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Extend an integral projective-coordinate morphism to the complex base.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; base change of coordinate maps. -/
def s2e_projectiveBaseChange {X Y : Scheme.{0}} (f : X ⟶ Y) :
    pullback (terminal.from (Spec ↧ℂ)) (terminal.from X) ⟶
      pullback (terminal.from (Spec ↧ℂ)) (terminal.from Y) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f) (Subsingleton.elim _ _)

/-- The coordinate base-change map gives the required Cartesian square.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_projectiveBaseChange_isPullback {X Y : Scheme.{0}} (f : X ⟶ Y) :
    IsPullback (pullback.snd _ _) (s2e_projectiveBaseChange f) f
      (pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from Y)) := by
  have hw : pullback.snd _ _ ≫ f = s2e_projectiveBaseChange f ≫ pullback.snd _ _ :=
    (pullback.lift_snd _ _ _).symm
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun s => pullback.lift (s.snd ≫ pullback.fst _ _) s.fst (Subsingleton.elim _ _))
    (fun s => by simp only [pullback.lift_snd]) ?_ ?_⟩⟩
  · intro s
    apply pullback.hom_ext
    · simp only [s2e_projectiveBaseChange, Category.assoc, pullback.lift_fst]
    · simp only [s2e_projectiveBaseChange, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_snd]
      exact s.condition
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      have h := congrArg (fun g => g ≫ pullback.fst _ _) hm₂
      simpa only [s2e_projectiveBaseChange, Category.assoc, pullback.lift_fst] using h
    · rw [pullback.lift_snd]
      exact hm₁

/-- Coordinate closed immersions remain closed immersions after complex base change.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_projectiveBaseChange_isClosedImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] : IsClosedImmersion (s2e_projectiveBaseChange f) := by
  exact MorphismProperty.of_isPullback (s2e_projectiveBaseChange_isPullback f) inferInstance

/-- Complex base change pulls back the image of the integral coordinate morphism.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_projectiveBaseChange_range {X Y : Scheme.{0}} (f : X ⟶ Y) :
    Set.range (s2e_projectiveBaseChange f) =
      (pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from Y)) ⁻¹' Set.range f := by
  have h := Scheme.image_preimage_eq_of_isPullback
    (s2e_projectiveBaseChange_isPullback f) Set.univ
  simpa only [Set.preimage_univ, Set.image_univ] using h

/-- Reindexing the homogeneous coordinates gives the corresponding complex projective isomorphism.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_complexProjectiveSpace_iso_of_equiv {ι κ : Type} (e : ι ≃ κ) :
    Nonempty (ProjectiveSpace ι (Spec ↧ℂ) ≅ ProjectiveSpace κ (Spec ↧ℂ)) := by
  obtain ⟨E⟩ := HodgeLean.Foundations.spec_g3c_nonempty_proj_iso_of_equiv_aux e
  haveI : IsIso (s2e_projectiveBaseChange E.hom) :=
    (s2e_projectiveBaseChange_isPullback E.hom).isIso_snd_of_isIso
  exact ⟨asIso (s2e_projectiveBaseChange E.hom)⟩

/-- Complex projective space is reduced on its normalized polynomial charts.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_complexProjectiveSpace_reduced (k : ℕ) :
    IsReduced (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) := by
  let U (i : Fin (k + 1)) :=
    AlgebraicGeometry.ComplexProjectiveSpace.projectiveSpaceBasicOpen k (MvPolynomial.X i)
  have hc : ⨆ i, U i = ⊤ :=
    (pullback.snd (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (AlgebraicGeometry.ComplexProjectiveSpace.UniversalGrading.{0} k)))).iSup_preimage_eq_top
        (AlgebraicGeometry.ComplexProjectiveSpace.iSup_coordinateBasicOpen_eq_top k)
  let C := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).openCoverOfIsOpenCover U hc
  letI (i : Fin (k + 1)) : IsReduced (C.X i) := by
    change IsReduced (U i).toScheme
    exact isReduced_of_isOpenImmersion (s2e_chartOpenIso i).inv
  exact IsReduced.of_openCover _ C

end HodgeLean.Foundations.Program
