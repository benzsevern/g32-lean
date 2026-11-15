import HodgeLean.Foundations.Program.SchoenTowerRetainedAffineQuotient
import HodgeLean.Foundations.Program.SchoenProjectiveActionQuotient
import HodgeLean.Foundations.Program.SchoenQuotientOpenImmersions
import HodgeLean.Foundations.Program.SchoenInvariantQuotientEpi

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An invariant affine open induces an open immersion of the specified categorical quotients.
Source: SGA 1, Exposé V, §1, invariant affine quotient charts. -/
theorem s2t_retained_open_quotient (X Y A B : Over (Spec ↧ℂ))
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
    (a : A ⟶ B) (ha : π ≫ a = j ≫ γ) : IsOpenImmersion a.left := by
  letI : IsAffine ((Over.forget (Spec ↧ℂ)).obj Y) := inferInstanceAs (IsAffine Y.left)
  let α := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρX
  let β := ((Over.forget (Spec ↧ℂ)).mapAut Y).comp ρY
  have hj' (g) : j.left ≫ (α g).asIso.hom = (β g).asIso.hom ≫ j.left :=
    congrArg (fun f : Y ⟶ X => f.left) (hj g)
  have hpt (g) (y : Y.left) : (α g).asIso.hom (j.left y) =
      j.left ((β g).asIso.hom y) := congrArg (fun f : Y.left ⟶ X.left => f y) (hj' g)
  have hU (g : G) : (α g).asIso.hom ⁻¹ᵁ j.left.opensRange = j.left.opensRange := by
    ext x
    change ((α g).asIso.hom x ∈ Set.range j.left) ↔ x ∈ Set.range j.left
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(β g).asIso.inv y, ?_⟩
      apply (α g).asIso.schemeIsoToHomeo.injective
      have hv : (β g).asIso.hom ((β g).asIso.inv y) = y := by
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
        rfl
      exact (hpt g _).trans ((congrArg j.left hv).trans hy)
    · rintro ⟨y, rfl⟩
      exact ⟨(β g).asIso.hom y, (hpt g y).symm⟩
  let U : s2_InvariantAffineOpen X.left G α :=
    ⟨j.left.opensRange, isAffineOpen_opensRange j.left,
      ⟨j.left (Classical.choice (inferInstance : Nonempty Y.left)), ⟨_, rfl⟩⟩, hU⟩
  letI : IsAffine U.val.toScheme := U.property.1
  let e := j.left.isoOpensRange
  let δ := s2_invariantAffineOpenAction X.left G α U
  have he (g : G) : e.hom ≫ (δ g).asIso.hom = (β g).asIso.hom ≫ e.hom := by
    apply (cancel_mono U.val.ι).mp
    simp only [Category.assoc]
    change e.hom ≫ (s2_invariantOpenMap U.val (α g).asIso.hom ((U.property.2.2 g).ge) ≫ U.val.ι) =
      (β g).asIso.hom ≫ e.hom ≫ U.val.ι
    rw [s2_invariantOpenMap_ι]
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact hj' g
  let c := s2_quotientComparison G β δ e.hom he
  letI : IsIso c := s2_affineSchemeQuotientMap_isIso_of_isIso G β δ e.hom he
  have hover (g : G) : (α g).asIso.hom ≫ X.hom = X.hom := Over.w (ρX g).asIso.hom
  let hcover := s2_projective_invariantAffineIndex_cover ℂ X.left X.hom G α
  let W := s2_gluedQuotientOver X G α hover hcover
  let qX := s2_gluedQuotientOverMap X G α hover hcover
  let qY := s2t_affineQuotientOverMap Y G ρY
  let k := c ≫ s2_invariantAffineGluedι X.left G α U
  have hk : qY.left ≫ k = j.left ≫ qX.left := by
    change s2_affineSchemeQuotientMap Y.left G β ≫
      (c ≫ s2_invariantAffineGluedι X.left G α U) =
        j.left ≫ s2_gluedQuotientMap X.left G α hcover
    have hc : s2_affineSchemeQuotientMap Y.left G β ≫ c =
        e.hom ≫ s2_affineSchemeQuotientMap U.val.toScheme G δ :=
      s2_affineSchemeQuotientMap_naturality (X := Y.left) (Y := U.val.toScheme)
        G β δ e.hom he
    rw [← Category.assoc, hc, Category.assoc]
    change e.hom ≫ (s2_invariantAffineProjection X.left G α U ≫
      s2_invariantAffineGluedι X.left G α U) = _
    rw [← s2_gluedQuotientMap_ι X.left G α hcover U, ← Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι]
  letI : Epi qY.left := s2_affineSchemeQuotientMap_epi Y.left G β
  let t : s2t_affineQuotientOver Y G ρY ⟶ W := Over.homMk k (by
    apply (cancel_epi qY.left).mp
    rw [← Category.assoc, hk, Category.assoc, Over.w qX, Over.w j, Over.w qY])
  have ht : qY ≫ t = j ≫ qX := by exact Over.OverMorphism.ext hk
  have hinvX : ∀ g, (ρX g).asIso.hom ≫ qX = qX := by
    intro g
    apply Over.OverMorphism.ext
    exact s2_gluedQuotientMap_invariant X.left G α hcover g
  have hquotX : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      (∀ g, (ρX g).asIso.hom ≫ f = f) → ∃! d : W ⟶ T, qX ≫ d = f := by
    intro T f hf
    exact s2_gluedQuotientOverDesc_arbitrary X G α hover hcover T f
      (fun g => congrArg (fun f : X ⟶ T => f.left) (hf g))
  obtain ⟨eX, heX⟩ := s2_invariantQuotient_iso (fun g => (ρX g).asIso.hom)
    γ qX hγinv hγquot hinvX hquotX
  obtain ⟨eY, heY⟩ := s2t_retainedAffineQuotient_iso Y G ρY A π hπinv hπquot
  letI : Epi π := s2_invariantQuotient_epi (fun g => (ρY g).asIso.hom) π hπinv hπquot
  have hae : a = eY.inv ≫ t ≫ eX.hom := by
    apply (cancel_epi π).mp
    rw [ha]
    symm
    calc
      π ≫ (eY.inv ≫ t ≫ eX.hom) = qY ≫ t ≫ eX.hom := by
        rw [← heY]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rfl
      _ = j ≫ γ := by rw [← Category.assoc, ht, Category.assoc, heX]

  rw [hae, Over.comp_left, Over.comp_left]
  letI : IsOpenImmersion t.left := by change IsOpenImmersion k; dsimp only [k]; infer_instance
  infer_instance

end HodgeLean.Foundations.Program
