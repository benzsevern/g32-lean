import HodgeLean.Foundations.Program.SchoenSchemeSectionAction
import HodgeLean.Foundations.Program.SchoenInvariantRings
import HodgeLean.Foundations.Program.SchoenAffineQuotientDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The invariant-spectrum projection of an affine scheme with a group action. -/
def s2_affineSchemeQuotientMap (X : Scheme) [IsAffine X]
    (G : Type) [Group G] (ρ : G →* Aut X) :
    letI := s2_schemeSectionAction X G ρ
    X ⟶ Spec (CommRingCat.of (FixedPoints.subring Γ(X, ⊤) G)) :=
  letI := s2_schemeSectionAction X G ρ
  X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (FixedPoints.subring Γ(X, ⊤) G).subtype)

/-- Every element of the scheme action preserves the invariant-spectrum projection. -/
theorem s2_affineSchemeQuotientMap_invariant (X : Scheme) [IsAffine X]
    (G : Type) [Group G] (ρ : G →* Aut X) (g : G) :
    (ρ g).asIso.hom ≫ s2_affineSchemeQuotientMap X G ρ =
      s2_affineSchemeQuotientMap X G ρ := by
  letI := s2_schemeSectionAction X G ρ
  unfold s2_affineSchemeQuotientMap
  rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  ext s
  change (ρ g).asIso.hom.appTop s.val = s.val
  have hs := s.property g⁻¹
  change (ρ (g⁻¹)⁻¹).asIso.hom.appTop s.val = s.val at hs
  simpa only [inv_inv] using hs

/-- Equivariant maps induce commuting squares between invariant spectra. -/
theorem s2_affineSchemeQuotientMap_naturality {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (G : Type) [Group G] (ρX : G →* Aut X) (ρY : G →* Aut Y) (f : X ⟶ Y)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    s2_affineSchemeQuotientMap X G ρX ≫
      Spec.map (CommRingCat.ofHom (s2_fixedSectionPullback G ρX ρY f hf)) =
      f ≫ s2_affineSchemeQuotientMap Y G ρY := by
  unfold s2_affineSchemeQuotientMap
  rw [Category.assoc, ← Spec.map_comp, ← Category.assoc,
    ← Scheme.isoSpec_hom_naturality, Category.assoc, ← Spec.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient projection of an affine domain is an epimorphism. -/
theorem s2_affineSchemeQuotientMap_epi (X : Scheme.{0}) [IsAffine X]
    [IsDomain Γ(X, ⊤)] (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    Epi (s2_affineSchemeQuotientMap X G ρ) := by
  letI := s2_schemeSectionAction X G ρ
  haveI : Epi (Spec.map (CommRingCat.ofHom (FixedPoints.subring Γ(X, ⊤) G).subtype)) := by
    exact s2_affineQuotient_epi ℤ Γ(X, ⊤) G
  unfold s2_affineSchemeQuotientMap
  infer_instance

/-- Finite group quotients of affine schemes are surjective on scheme points. -/
theorem s2_affineSchemeQuotientMap_surjective (X : Scheme.{0}) [IsAffine X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    Function.Surjective (s2_affineSchemeQuotientMap X G ρ) := by
  letI := s2_schemeSectionAction X G ρ
  have hq : Function.Surjective
      (Spec.map (CommRingCat.ofHom (FixedPoints.subring Γ(X, ⊤) G).subtype)) :=
    s2_fixedAlgebra_spec_surjective ℤ Γ(X, ⊤) G
  exact hq.comp X.isoSpec.hom.homeomorph.surjective

/-- Invariant maps from affine domains to affine schemes descend uniquely. -/
theorem s2_affineSchemeQuotientDesc {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    [IsDomain Γ(X, ⊤)] (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (f : X ⟶ Y) (hf : ∀ g : G, (ρ g).asIso.hom ≫ f = f) :
    letI := s2_schemeSectionAction X G ρ
    ∃! d : Spec (CommRingCat.of (FixedPoints.subring Γ(X, ⊤) G)) ⟶ Y,
      s2_affineSchemeQuotientMap X G ρ ≫ d = f := by
  letI := s2_schemeSectionAction X G ρ
  have hfix (s : Γ(Y, ⊤)) (g : G) : g • f.appTop s = f.appTop s := by
    have he := congrArg (fun k : X ⟶ Y => k.appTop) (hf g⁻¹)
    exact congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(X, ⊤) => k s) he
  let ψ : Γ(Y, ⊤) →+* FixedPoints.subring Γ(X, ⊤) G :=
    f.appTop.hom.codRestrict _ hfix
  let d := Spec.map (CommRingCat.ofHom ψ) ≫ Y.isoSpec.inv
  have hd : s2_affineSchemeQuotientMap X G ρ ≫ d = f := by
    apply (cancel_mono Y.isoSpec.hom).mp
    dsimp only [d, s2_affineSchemeQuotientMap]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Spec.map_comp]
    exact X.isoSpec_hom_naturality f
  haveI := s2_affineSchemeQuotientMap_epi X G ρ
  refine ⟨d, hd, ?_⟩
  intro e he
  exact (cancel_epi (s2_affineSchemeQuotientMap X G ρ)).mp (he.trans hd.symm)

end HodgeLean.Foundations.Program
