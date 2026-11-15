import HodgeLean.Foundations.Program.SchoenSchemeSectionAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The basic open of an invariant global section is invariant under the scheme action. -/
theorem s2_fixedSection_basicOpen_invariant (X : Scheme.{0})
    (G : Type) [Group G] (ρ : G →* Aut X) :
    letI := s2_schemeSectionAction X G ρ
    ∀ (r : FixedPoints.subring Γ(X, ⊤) G) (g : G),
      (ρ g).asIso.hom ⁻¹ᵁ X.basicOpen (r : Γ(X, ⊤)) = X.basicOpen (r : Γ(X, ⊤)) := by
  letI := s2_schemeSectionAction X G ρ
  intro r g
  rw [Scheme.preimage_basicOpen_top]
  apply congrArg X.basicOpen
  have h := r.property g⁻¹
  change (ρ (g⁻¹)⁻¹).asIso.hom.appTop r.val = r.val at h
  simpa only [inv_inv] using h

/-- Equivariant pullback equips section rings with compatible scalar actions. -/
theorem s2_schemeSectionAction_smulDistribClass {X Y : Scheme.{0}}
    (G : Type) [Group G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    letI := s2_schemeSectionAction X G ρX
    letI := s2_schemeSectionAction Y G ρY
    letI := f.appTop.hom.toAlgebra
    SMulDistribClass G Γ(Y, ⊤) Γ(X, ⊤) := by
  letI := s2_schemeSectionAction X G ρX
  letI := s2_schemeSectionAction Y G ρY
  letI := f.appTop.hom.toAlgebra
  constructor
  intro g b a
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
  change g • f.appTop b * g • a = f.appTop (g • b) * g • a
  rw [s2_schemeSectionAction_naturality G ρX ρY f hf]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Global sections of a principal open subscheme form the expected localization,
with algebra structure induced by its scheme inclusion. -/
theorem s2_basicOpen_globalSections_isLocalization (X : Scheme.{0}) [IsAffine X]
    (r : Γ(X, ⊤)) :
    letI := (X.basicOpen r).ι.appTop.hom.toAlgebra
    IsLocalization.Away r Γ((X.basicOpen r).toScheme, ⊤) := by
  let U := X.basicOpen r
  letI := U.ι.appTop.hom.toAlgebra
  let e : Γ(U.toScheme, ⊤) ≃ₐ[Γ(X, ⊤)] Γ(X, U) :=
    { U.topIso.commRingCatIsoToRingEquiv with
      commutes' := by
        intro b
        change U.topIso.hom (U.ι.appTop b) =
          (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) b
        have he : U.ι.appTop ≫ U.topIso.hom =
            X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
          dsimp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso, Functor.mapIso]
          rw [← Functor.map_comp]
          rfl
        exact congrArg (fun f => f b) he }
  exact (IsLocalization.isLocalization_iff_of_algEquiv (Submonoid.powers r) e).mpr inferInstance

/-- The restricted scheme action on a principal open defined by a fixed section. -/
def s2_fixedSection_basicOpenAction (X : Scheme.{0})
    (G : Type) [Group G] (ρ : G →* Aut X) :
    letI := s2_schemeSectionAction X G ρ
    ∀ r : FixedPoints.subring Γ(X, ⊤) G,
      G →* Aut (X.basicOpen (r : Γ(X, ⊤))).toScheme := by
  letI := s2_schemeSectionAction X G ρ
  intro r
  exact s2_invariantOpenAction G ρ (X.basicOpen (r : Γ(X, ⊤)))
    (s2_fixedSection_basicOpen_invariant X G ρ r)

/-- The principal chart inclusion intertwines the restricted and original actions. -/
theorem s2_fixedSection_basicOpenAction_ι (X : Scheme.{0})
    (G : Type) [Group G] (ρ : G →* Aut X) :
    letI := s2_schemeSectionAction X G ρ
    ∀ (r : FixedPoints.subring Γ(X, ⊤) G) (g : G),
      (X.basicOpen (r : Γ(X, ⊤))).ι ≫ (ρ g).asIso.hom =
        (s2_fixedSection_basicOpenAction X G ρ r g).asIso.hom ≫
          (X.basicOpen (r : Γ(X, ⊤))).ι := by
  letI := s2_schemeSectionAction X G ρ
  intro r g
  exact (s2_invariantOpenMap_ι (X.basicOpen (r : Γ(X, ⊤)))
    (ρ g).asIso.hom (s2_fixedSection_basicOpen_invariant X G ρ r g).ge).symm

end HodgeLean.Foundations.Program
