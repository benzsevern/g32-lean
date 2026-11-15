import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartScheme

/-! # The actual standard affine chart morphism into projective space -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The actual affine tensor chart maps to the repository's retained projective scheme by base change of the standard integral chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_standardProjectiveChart {n : ℕ} (i : Fin (n + 1)) :
    Spec (CommRingCat.of (ℂ ⊗[ℤ]
      HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i))) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec (CommRingCat.of ℂ)) := by
  let A := HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)
  let j := Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  let f := terminal.from (Spec (CommRingCat.of ℂ))
  let g := terminal.from (Spec (CommRingCat.of A))
  exact (s2e_specTensorProductTerminalIso ℂ A).hom ≫
    pullback.lift (pullback.fst f g) (pullback.snd f g ≫ j) (by
      apply terminalIsTerminal.hom_ext)

/-- The actual tensor chart is the scheme pullback of the integral projective chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
theorem s2e_standardProjectiveChart_isPullback {n : ℕ} (i : Fin (n + 1)) :
    let A := HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)
    let j := Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
    let f := terminal.from (Spec (CommRingCat.of ℂ))
    let g := terminal.from (Spec (CommRingCat.of A))
    IsPullback (s2e_standardProjectiveChart i)
      ((s2e_specTensorProductTerminalIso ℂ A).hom ≫ pullback.snd f g)
      (pullback.snd f (terminal.from (Proj (UniversalGrading n)))) j := by
  let A := HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)
  let j := Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  let f := terminal.from (Spec (CommRingCat.of ℂ))
  let g := terminal.from (Spec (CommRingCat.of A))
  let t := terminal.from (Proj (UniversalGrading n))
  let e := s2e_specTensorProductTerminalIso ℂ A
  have hProd : IsPullback (e.hom ≫ pullback.fst f g) (e.hom ≫ pullback.snd f g) f g := by
    exact (IsPullback.of_hasPullback f g).of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have hFst : s2e_standardProjectiveChart i ≫ pullback.fst f t = e.hom ≫ pullback.fst f g := by
    change (e.hom ≫ pullback.lift (pullback.fst f g) (pullback.snd f g ≫ j) _) ≫
      pullback.fst f t = _
    rw [Category.assoc, pullback.lift_fst]
  have hSnd : s2e_standardProjectiveChart i ≫ pullback.snd f t =
      (e.hom ≫ pullback.snd f g) ≫ j := by
    change (e.hom ≫ pullback.lift (pullback.fst f g) (pullback.snd f g ≫ j) _) ≫
      pullback.snd f t = _
    rw [Category.assoc, pullback.lift_snd, Category.assoc]
  have houter : IsPullback (s2e_standardProjectiveChart i ≫ pullback.fst f t)
      (e.hom ≫ pullback.snd f g) f (j ≫ t) := by
    rw [hFst, show j ≫ t = g from terminalIsTerminal.hom_ext _ _]
    exact hProd
  exact houter.of_right hSnd (IsPullback.of_hasPullback f t)

/-- The actual tensor chart is an open immersion into the retained projective scheme.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
theorem s2e_standardProjectiveChart_isOpenImmersion {n : ℕ} (i : Fin (n + 1)) :
    IsOpenImmersion (s2e_standardProjectiveChart i) := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsOpenImmersion) (s2e_standardProjectiveChart_isPullback i).flip inferInstance

/-- The actual standard tensor chart has an affine open image in the retained projective scheme.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_standardProjectiveAffineOpen {n : ℕ} (i : Fin (n + 1)) :
    (ProjectiveSpace (Fin (n + 1)) (Spec (CommRingCat.of ℂ))).affineOpens := by
  letI : IsOpenImmersion (s2e_standardProjectiveChart i) :=
    s2e_standardProjectiveChart_isOpenImmersion i
  exact ⟨s2e_standardProjectiveChart i ''ᵁ ⊤,
    (isAffineOpen_top _).image_of_isOpenImmersion (s2e_standardProjectiveChart i)⟩

/-- The actual standard chart respects its complex structural morphism.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_standardProjectiveChart_over {n : ℕ} (i : Fin (n + 1)) :
    s2e_standardProjectiveChart i ≫
      ProjectiveSpace.toBase (Fin (n + 1)) (Spec (CommRingCat.of ℂ)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (ℂ ⊗[ℤ]
        HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)))) := by
  unfold s2e_standardProjectiveChart
  change (_ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullback.lift_fst]
  exact s2e_specTensorProductTerminalIso_hom_fst _ _

end HodgeLean.Foundations.Program
