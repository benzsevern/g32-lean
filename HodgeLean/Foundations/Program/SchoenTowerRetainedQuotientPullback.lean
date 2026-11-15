import HodgeLean.Foundations.Program.SchoenTowerRetainedOpenQuotient

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The specified projective categorical quotient has the actual scheme-point orbit fibres.
Source: SGA 1, Exposé V, §1, finite invariant quotients. -/
theorem s2t_retained_quotient_orbits (X B : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsProjective X.hom]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) (γ : X ⟶ B)
    (hinv : ∀ g, (ρ g).asIso.hom ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g, (ρ g).asIso.hom ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f) :
    Function.Surjective γ.left ∧ ∀ x y : X.left,
      γ.left x = γ.left y ↔ ∃ g, (ρ g).asIso.hom.left x = y := by
  let α := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ
  have hover (g : G) : (α g).asIso.hom ≫ X.hom = X.hom := Over.w (ρ g).asIso.hom
  let hcover := s2_projective_invariantAffineIndex_cover ℂ X.left X.hom G α
  let W := s2_gluedQuotientOver X G α hover hcover
  let q := s2_gluedQuotientOverMap X G α hover hcover
  have hi : ∀ g, (ρ g).asIso.hom ≫ q = q := by
    intro g
    apply Over.OverMorphism.ext
    exact s2_gluedQuotientMap_invariant X.left G α hcover g
  have hq : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g, (ρ g).asIso.hom ≫ f = f) → ∃! d : W ⟶ T, q ≫ d = f := by
    intro T f hf
    exact s2_gluedQuotientOverDesc_arbitrary X G α hover hcover T f
      (fun g => congrArg (fun f : X ⟶ T => f.left) (hf g))
  obtain ⟨e, he⟩ := s2_invariantQuotient_iso (fun g => (ρ g).asIso.hom) γ q hinv hquot hi hq
  let e' : W.left ≅ B.left := (Over.forget (Spec ↧ℂ)).mapIso e
  have he' : q.left ≫ e'.hom = γ.left := congrArg (fun f : X ⟶ B => f.left) he
  constructor
  · intro z
    obtain ⟨x, hx⟩ := s2_gluedQuotientMap_surjective X.left G α hcover (e'.inv z)
    refine ⟨x, ?_⟩
    rw [← he', Scheme.Hom.comp_apply]
    change e'.hom (s2_gluedQuotientMap X.left G α hcover x) = z
    rw [hx, ← Scheme.Hom.comp_apply, e'.inv_hom_id]
    rfl
  · intro x y
    have hi' : Function.Injective e'.hom := e'.schemeIsoToHomeo.injective
    rw [← he', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hi'.eq_iff]
    exact s2_gluedQuotientMap_fibres X.left G α hcover x y

/-- The invariant affine open quotient square is an actual scheme pullback.
Source: SGA 1, Exposé V, §1, invariant affine quotient charts and orbit fibres. -/
theorem s2t_retained_open_quotient_isPullback (X Y A B : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsProjective X.hom]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    [IsAffine Y.left] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (j : Y ⟶ X) [IsOpenImmersion j.left]
    (hj : ∀ g, j ≫ (ρX g).asIso.hom = (ρY g).asIso.hom ≫ j)
    (π : Y ⟶ A) (γ : X ⟶ B)
    (hπinv : ∀ g, (ρY g).asIso.hom ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : Y ⟶ T),
      (∀ g, (ρY g).asIso.hom ≫ f = f) → ∃! d : A ⟶ T, π ≫ d = f)
    (hγinv : ∀ g, (ρX g).asIso.hom ≫ γ = γ)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g, (ρX g).asIso.hom ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : A ⟶ B) (ha : π ≫ a = j ≫ γ) :
    IsPullback π.left j.left a.left γ.left := by
  letI := s2t_retained_open_quotient X Y A B G ρX ρY j hj π γ hπinv hπquot hγinv hγquot a ha
  obtain ⟨e, he⟩ := s2t_retainedAffineQuotient_iso Y G ρY A π hπinv hπquot
  let e' : (s2t_affineQuotientOver Y G ρY).left ≅ A.left :=
    (Over.forget (Spec ↧ℂ)).mapIso e
  have he' : (s2t_affineQuotientOverMap Y G ρY).left ≫ e'.hom = π.left :=
    congrArg (fun f : Y ⟶ A => f.left) he
  have hs : Function.Surjective π.left := by
    intro z
    obtain ⟨w, hw⟩ := e'.schemeIsoToHomeo.surjective z
    change e'.hom w = z at hw
    obtain ⟨y, hy⟩ := s2_affineSchemeQuotientMap_surjective Y.left G
      (((Over.forget (Spec ↧ℂ)).mapAut Y).comp ρY) w
    refine ⟨y, ?_⟩
    rw [← he', Scheme.Hom.comp_apply]
    change e'.hom (s2_affineSchemeQuotientMap Y.left G _ y) = z
    rw [hy, hw]
  have horb := (s2t_retained_quotient_orbits X B G ρX γ hγinv hγquot).2
  have hpre : γ.left ⁻¹' Set.range a.left = Set.range j.left := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := hs z
      have hxy : γ.left (j.left y) = γ.left x := by
        have he := congrArg (fun f : Y ⟶ B => f.left y) ha
        exact he.symm.trans hz
      obtain ⟨g, hg⟩ := (horb (j.left y) x).mp hxy
      refine ⟨(ρY g).asIso.hom.left y, ?_⟩
      have ht := congrArg (fun f : Y ⟶ X => f.left y) (hj g)
      exact ht.symm.trans hg
    · rintro ⟨y, rfl⟩
      exact ⟨π.left y, congrArg (fun f : Y ⟶ B => f.left y) ha⟩
  apply IsOpenImmersion.isPullback π.left j.left a.left γ.left
    (congrArg (fun f : Y ⟶ B => f.left) ha).symm
  apply TopologicalSpace.Opens.ext
  exact hpre

end HodgeLean.Foundations.Program
