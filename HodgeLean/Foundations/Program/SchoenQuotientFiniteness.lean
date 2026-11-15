import HodgeLean.Foundations.Program.SchoenGluedQuotientOrbits

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A scalar-compatible finite action on a finitely generated affine algebra
has a finite affine scheme quotient projection. -/
theorem s2_affineSchemeQuotientMap_finite_of_finiteType (R : Type) [CommRing R]
    (X : Scheme.{0}) [IsAffine X] [Algebra R Γ(X, ⊤)] [Algebra.FiniteType R Γ(X, ⊤)]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hcomm : letI := s2_schemeSectionAction X G ρ; SMulCommClass G R Γ(X, ⊤)) :
    IsFinite (s2_affineSchemeQuotientMap X G ρ) := by
  letI := s2_schemeSectionAction X G ρ
  letI := hcomm
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (FixedPoints.subring Γ(X, ⊤) G).subtype)) :=
    s2_fixedAlgebra_spec_finite R Γ(X, ⊤) G
  unfold s2_affineSchemeQuotientMap
  infer_instance

/-- An action over a base scheme fixes pullbacks of every global base section. -/
theorem s2_schemeSectionAction_over_fixed {X S : Scheme.{0}} (s : X ⟶ S)
    (G : Type) [Group G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s) (b : Γ(S, ⊤)) (g : G) :
    letI := s2_schemeSectionAction X G ρ
    g • s.appTop b = s.appTop b := by
  exact congrArg (fun f : X ⟶ S => f.appTop b) (hover g⁻¹)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite actions over an affine base have finite quotient projections on
finite-type affine source schemes. -/
theorem s2_affineSchemeQuotientMap_finite_over {X S : Scheme.{0}}
    [IsAffine X] [IsAffine S] (s : X ⟶ S) [LocallyOfFiniteType s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s) :
    IsFinite (s2_affineSchemeQuotientMap X G ρ) := by
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := s.appTop.hom.toAlgebra
  haveI : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) := by
    apply RingHom.finiteType_algebraMap.mp
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := s)).mp inferInstance
  apply s2_affineSchemeQuotientMap_finite_of_finiteType Γ(S, ⊤) X G ρ
  letI := s2_schemeSectionAction X G ρ
  constructor
  intro g a b
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
  change (g • s.appTop a) * (g • b) = s.appTop a * (g • b)
  rw [s2_schemeSectionAction_over_fixed s G ρ hover a g]

/-- Quotient projections on the actual invariant source charts are finite for
a finite-type source action over an affine base. -/
theorem s2_invariantAffineProjection_finite_over {X S : Scheme.{0}}
    [IsAffine S] (s : X ⟶ S) [LocallyOfFiniteType s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (U : s2_InvariantAffineOpen X G ρ) : IsFinite (s2_invariantAffineProjection X G ρ U) := by
  apply s2_affineSchemeQuotientMap_finite_over (U.val.ι ≫ s) G
    (s2_invariantAffineOpenAction X G ρ U)
  intro g
  rw [← Category.assoc]
  change s2_invariantOpenMap U.val (ρ g).asIso.hom (U.property.2.2 g).ge ≫ U.val.ι ≫ s = _
  rw [s2_invariantOpenMap_ι_assoc, hover g]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The globally glued projection is finite for finite-type actions over an affine base. -/
theorem s2_gluedQuotientMap_finite_over {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) [LocallyOfFiniteType s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    IsFinite (s2_gluedQuotientMap X G ρ hcover) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (Scheme.IsLocallyDirected.openCover (s2_invariantAffineDiagram X G ρ))
  intro U
  haveI : IsFinite (s2_invariantAffineProjection X G ρ U) :=
    s2_invariantAffineProjection_finite_over s G ρ hover U
  have h := (s2_gluedQuotientMap_chart_isPullback X G ρ hcover U).flip
  change IsFinite (pullback.snd (s2_gluedQuotientMap X G ρ hcover) (s2_invariantAffineGluedι X G ρ U))
  rw [← h.isoPullback_inv_snd]
  infer_instance

end HodgeLean.Foundations.Program
