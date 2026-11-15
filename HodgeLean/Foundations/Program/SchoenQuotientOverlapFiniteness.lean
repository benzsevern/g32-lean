import HodgeLean.Foundations.Program.SchoenQuotientFiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import HodgeLean.Foundations.Program.SchoenQuotientOverlapProducts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The source intersection has a finite composite into the relative product of
its two quotient charts for a separated finite-type source over an affine base. -/
theorem s2_quotientOverlapPair_composite_finite {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) [LocallyOfFiniteType s] [IsSeparated s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U V : s2_InvariantAffineOpen X G ρ) :
    IsFinite (s2_invariantAffineProjection X G ρ (s2_invariantAffineOpenInf X G ρ U V) ≫
      s2_quotientOverlapPair s G ρ hover hcover U V) := by
  let W := s2_invariantAffineOpenInf X G ρ U V
  let tU := s2_invariantAffineGluedι X G ρ U ≫ s2_gluedQuotientStructure s G ρ hover hcover
  let tV := s2_invariantAffineGluedι X G ρ V ≫ s2_gluedQuotientStructure s G ρ hover hcover
  let qU := s2_invariantAffineProjection X G ρ U
  let qV := s2_invariantAffineProjection X G ρ V
  let hU := s2_invariantAffineProjection_base s G ρ hover hcover U
  let hV := s2_invariantAffineProjection_base s G ρ hover hcover V
  let Φ := pullback.map (U.val.ι ≫ s) (V.val.ι ≫ s) tU tV qU qV (𝟙 S)
    ((Category.comp_id _).trans hU) ((Category.comp_id _).trans hV)
  haveI : IsFinite qU := s2_invariantAffineProjection_finite_over s G ρ hover U
  haveI : IsFinite qV := s2_invariantAffineProjection_finite_over s G ρ hover V
  haveI : IsFinite Φ := MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance hU hV
  let H := isPullback_opens_inf U.val V.val
  have hfactor : s2_invariantAffineProjection X G ρ W ≫
      s2_quotientOverlapPair s G ρ hover hcover U V =
      H.isoPullback.hom ≫ pullback.mapDesc U.val.ι V.val.ι s ≫ Φ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, s2_quotientOverlapPair, pullback.lift_fst,
        Φ, tU, tV, pullback.mapDesc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
      rw [← Category.assoc, H.isoPullback_hom_fst]
      exact s2_invariantAffineProjection_naturality X G ρ W U
        (by change U.val ⊓ V.val ≤ U.val; exact inf_le_left)
    · simp only [Category.assoc, s2_quotientOverlapPair, pullback.lift_snd,
        Φ, tU, tV, pullback.mapDesc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      rw [← Category.assoc, H.isoPullback_hom_snd]
      exact s2_invariantAffineProjection_naturality X G ρ W V
        (by change U.val ⊓ V.val ≤ V.val; exact inf_le_right)
  rw [hfactor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual quotient overlap morphism into the relative chart product is finite
over a Noetherian affine base. -/
theorem s2_quotientOverlapPair_finite {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S] [IsLocallyNoetherian S]
    (s : X ⟶ S) [LocallyOfFiniteType s] [IsSeparated s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U V : s2_InvariantAffineOpen X G ρ) :
    IsFinite (s2_quotientOverlapPair s G ρ hover hcover U V) := by
  haveI (A : s2_InvariantAffineOpen X G ρ) : IsAffine (s2_invariantAffineQuotientObj X G ρ A) := by
    dsimp only [s2_invariantAffineQuotientObj]
    infer_instance
  haveI : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  haveI := s2_gluedQuotientStructure_locallyOfFiniteType s G ρ hover hcover
  haveI : IsLocallyNoetherian (s2_invariantAffineQuotientObj X G ρ V) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (s2_invariantAffineGluedι X G ρ V ≫ s2_gluedQuotientStructure s G ρ hover hcover)
  let P := pullback
    (s2_invariantAffineGluedι X G ρ U ≫ s2_gluedQuotientStructure s G ρ hover hcover)
    (s2_invariantAffineGluedι X G ρ V ≫ s2_gluedQuotientStructure s G ρ hover hcover)
  haveI : IsLocallyNoetherian P := inferInstance
  haveI : IsNoetherianRing Γ(P, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top P⟩
  haveI := s2_quotientOverlapPair_composite_finite s G ρ hover hcover U V
  apply s2_affine_finite_descent
    (s2_invariantAffineProjection X G ρ (s2_invariantAffineOpenInf X G ρ U V))
  exact s2_affineSchemeQuotientMap_appTop_injective _ G _

/-- Actual quotient overlaps embed as closed subschemes of the relative chart products. -/
theorem s2_quotientOverlapPair_closedImmersion {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S] [IsLocallyNoetherian S]
    (s : X ⟶ S) [LocallyOfFiniteType s] [IsSeparated s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U V : s2_InvariantAffineOpen X G ρ) :
    IsClosedImmersion (s2_quotientOverlapPair s G ρ hover hcover U V) := by
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨s2_quotientOverlapPair_finite s G ρ hover hcover U V,
      s2_quotientOverlapPair_mono s G ρ hover hcover U V⟩

end HodgeLean.Foundations.Program
