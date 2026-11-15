import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveRestriction
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # The polynomial chart of the actual projective line -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The affine coordinate ring of the projective chart after extending
integer coefficients to the complex numbers is the polynomial line. -/
theorem pairedC3_projective_chart_pushout (i : Fin 2) :
    IsPushout
      (CommRingCat.ofHom (Int.castRingHom ℂ))
      (CommRingCat.ofHom (Int.castRingHom
        (HomogeneousLocalization.Away (UniversalGrading 1)
          (MvPolynomial.X i : UniversalRing 1))))
      (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ))
      (CommRingCat.ofHom (projectiveLineChartCoordinateHom i (Polynomial.X : Polynomial ℂ))) := by
  let H := HomogeneousLocalization.Away (UniversalGrading 1)
    (MvPolynomial.X i : UniversalRing 1)
  let j : Fin 2 := if i = 0 then 1 else 0
  have hji : j ≠ i := by
    dsimp [j]
    split_ifs with h
    · subst i; decide
    · have : i = 1 := by omega
      subst i; decide
  have hother (k : Fin 2) (hk : k ≠ i) : k = j := by
    dsimp [j]
    split_ifs <;> omega
  let f := CommRingCat.ofHom (Int.castRingHom ℂ)
  let g := CommRingCat.ofHom (Int.castRingHom H)
  let a := CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)
  let b := CommRingCat.ofHom (projectiveLineChartCoordinateHom i (Polynomial.X : Polynomial ℂ))
  have hw : f ≫ a = g ≫ b := by
    apply CommRingCat.hom_ext
    exact Subsingleton.elim _ _
  let desc (s : PushoutCocone f g) := CommRingCat.ofHom
    (Polynomial.eval₂RingHom s.inl.hom (s.inr.hom (chartCoordinate i j)))
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hw desc ?_ ?_ ?_)
  · intro s
    ext r
    change Polynomial.eval₂ s.inl.hom (s.inr.hom (chartCoordinate i j))
      (Polynomial.C r) = s.inl.hom r
    rw [Polynomial.eval₂_C]
  · intro s
    apply CommRingCat.hom_ext
    apply HodgeLean.Foundations.Program.s2e_u1_projective_chart_ringHom_ext i
    intro k
    change Polynomial.eval₂ s.inl.hom (s.inr.hom (chartCoordinate i j))
      (projectiveLineChartCoordinateHom i Polynomial.X (chartCoordinate i k)) =
        s.inr.hom (chartCoordinate i k)
    rw [projectiveLineChartCoordinateHom_coordinate]
    by_cases hk : k = i
    · subst k
      rw [if_pos rfl, Polynomial.eval₂_one, chartCoordinate_self, map_one]
    · rw [if_neg hk, Polynomial.eval₂_X, hother k hk]
  · intro s m hl hr
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      have hh := congrArg (fun F : CommRingCat.of ℂ ⟶ s.pt => F.hom r) hl
      change m.hom (Polynomial.C r) = s.inl.hom r at hh
      simpa only [desc, CommRingCat.hom_ofHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C] using hh
    · have hh := congrArg (fun F : CommRingCat.of H ⟶ s.pt =>
        F.hom (chartCoordinate i j)) hr
      change m.hom (projectiveLineChartCoordinateHom i Polynomial.X
        (chartCoordinate i j)) = _ at hh
      rw [projectiveLineChartCoordinateHom_coordinate, if_neg hji] at hh
      simpa only [desc, CommRingCat.hom_ofHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X] using hh

/-- The polynomial line is the actual standard open chart in the
projective line over the complex base. -/
theorem pairedC3_projective_chart_open (i : Fin 2) :
    IsOpenImmersion (projectiveLineChart i (Polynomial.X : Polynomial ℂ)).left := by
  let H := HomogeneousLocalization.Away (UniversalGrading 1)
    (MvPolynomial.X i : UniversalRing 1)
  let f := Spec.map (CommRingCat.ofHom
    (projectiveLineChartCoordinateHom i (Polynomial.X : Polynomial ℂ)))
  let c := ComplexPoint.affineSpecStructureMap (Polynomial ℂ)
  have h := (pairedC3_projective_chart_pushout i).op.map Scheme.Spec
  have h' : IsPullback f c (terminal.from (Spec (CommRingCat.of H)))
      (terminal.from (Spec ↧ℂ)) := by
    exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (specZIsTerminal.uniqueUpToIso terminalIsTerminal)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
      (by apply terminalIsTerminal.hom_ext)
      (by apply terminalIsTerminal.hom_ext)
  let j := (projectiveLineChart i (Polynomial.X : Polynomial ℂ)).left
  let a := Proj.awayι (UniversalGrading 1) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  have hc : j ≫ pullback.fst (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (UniversalGrading 1))) = c :=
    pullback.lift_fst _ _ _
  have ha : a ≫ terminal.from _ = terminal.from _ := terminal.comp_from a
  rw [← hc, ← ha] at h'
  have hs : IsPullback f j a (pullback.snd
      (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading 1)))) := by
    apply h'.of_bot ?_ (IsPullback.of_hasPullback
      (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading 1)))).flip
    dsimp only [j, projectiveLineChart, Over.homMk_left]
    exact (pullback.lift_snd _ _ _).symm
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hs inferInstance

#print axioms pairedC3_projective_chart_pushout
#print axioms pairedC3_projective_chart_open
end HodgeLean.Foundations.Program.G32Native
