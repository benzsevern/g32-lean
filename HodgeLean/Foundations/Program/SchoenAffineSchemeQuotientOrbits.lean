import HodgeLean.Foundations.Program.SchoenAffineSchemeQuotient
import HodgeLean.Foundations.Program.SchoenIntegralQuotientTopology

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The spectrum action on affine global sections matches the original scheme action. -/
theorem s2_schemeSectionAction_prime_smul (X : Scheme.{0}) [IsAffine X]
    (G : Type) [Group G] (ρ : G →* Aut X) (g : G) (x : X) :
    letI := s2_schemeSectionAction X G ρ
    @SMul.smul G (PrimeSpectrum (↑Γ(X, ⊤))) _ g (X.isoSpec.hom x) =
      X.isoSpec.hom ((ρ g).asIso.hom x) := by
  letI := s2_schemeSectionAction X G ρ
  have hsmul : @SMul.smul G (PrimeSpectrum (↑Γ(X, ⊤))) _ g (X.isoSpec.hom x) =
      PrimeSpectrum.comap (MulSemiringAction.toRingHom G Γ(X, ⊤) g⁻¹)
        (X.isoSpec.hom x) := by
    apply PrimeSpectrum.ext
    exact Ideal.pointwise_smul_eq_comap (X.isoSpec.hom x).asIdeal
  rw [hsmul]
  have he := congrArg (fun f : X ⟶ Spec Γ(X, ⊤) => f x)
    (s2_schemeSectionAction_isoSpec X G ρ g⁻¹)
  simp only [Scheme.Hom.comp_apply, inv_inv, Spec.map_apply] at he
  exact he

/-- The fibres of an affine finite-group quotient are precisely the scheme-point orbits. -/
theorem s2_affineSchemeQuotientMap_fibres (X : Scheme.{0}) [IsAffine X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) (x y : X) :
    s2_affineSchemeQuotientMap X G ρ x = s2_affineSchemeQuotientMap X G ρ y ↔
      ∃ g : G, (ρ g).asIso.hom x = y := by
  letI := s2_schemeSectionAction X G ρ
  constructor
  · intro hxy
    have hxy' : PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra ℤ Γ(X, ⊤) G) Γ(X, ⊤))
        (X.isoSpec.hom x) = PrimeSpectrum.comap
        (algebraMap (FixedPoints.subalgebra ℤ Γ(X, ⊤) G) Γ(X, ⊤)) (X.isoSpec.hom y) := hxy
    obtain ⟨g, hg⟩ := (s2_fixedAlgebra_spec_fibres ℤ Γ(X, ⊤) G _ _).mp hxy'
    have he : (X.isoSpec.hom y : PrimeSpectrum Γ(X, ⊤)) =
        @SMul.smul G (PrimeSpectrum (↑Γ(X, ⊤))) _ g (X.isoSpec.hom x) :=
      PrimeSpectrum.ext hg
    have he' : X.isoSpec.hom y = X.isoSpec.hom ((ρ g).asIso.hom x) :=
      he.trans (s2_schemeSectionAction_prime_smul X G ρ g x)
    exact ⟨g, X.isoSpec.hom.homeomorph.injective he'.symm⟩
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact (congrArg (fun f => f x) (s2_affineSchemeQuotientMap_invariant X G ρ g)).symm

/-- The affine finite-group quotient projection is open on scheme points. -/
theorem s2_affineSchemeQuotientMap_isOpenMap (X : Scheme.{0}) [IsAffine X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    IsOpenMap (s2_affineSchemeQuotientMap X G ρ) := by
  letI := s2_schemeSectionAction X G ρ
  have hq : IsOpenMap
      (Spec.map (CommRingCat.ofHom (FixedPoints.subring Γ(X, ⊤) G).subtype)) :=
    s2_fixedAlgebra_isOpenMap_integral ℤ Γ(X, ⊤) G
  exact hq.comp X.isoSpec.hom.homeomorph.isOpenMap

/-- An equivariant open immersion of affine schemes induces an injection on
invariant spectra. -/
theorem s2_affineSchemeQuotientMap_injective_of_openImmersion
    {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (G : Type) [Group G] [Finite G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y) [IsOpenImmersion f]
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    Function.Injective (Spec.map (CommRingCat.ofHom (s2_fixedSectionPullback G ρX ρY f hf))) := by
  let k := Spec.map (CommRingCat.ofHom (s2_fixedSectionPullback G ρX ρY f hf))
  have he (x : X) : k (s2_affineSchemeQuotientMap X G ρX x) =
      s2_affineSchemeQuotientMap Y G ρY (f x) :=
    congrArg (fun m => m x) (s2_affineSchemeQuotientMap_naturality G ρX ρY f hf)
  intro a b hab
  obtain ⟨x, rfl⟩ := s2_affineSchemeQuotientMap_surjective X G ρX a
  obtain ⟨y, rfl⟩ := s2_affineSchemeQuotientMap_surjective X G ρX b
  have hxy := (he x).symm.trans (hab.trans (he y))
  obtain ⟨g, hg⟩ := (s2_affineSchemeQuotientMap_fibres Y G ρY (f x) (f y)).mp hxy
  have hxg : f ((ρX g).asIso.hom x) = (ρY g).asIso.hom (f x) :=
    (congrArg (fun m : X ⟶ Y => m x) (hf g)).symm
  apply (s2_affineSchemeQuotientMap_fibres X G ρX x y).mpr
  exact ⟨g, f.isOpenEmbedding.injective (hxg.trans hg)⟩

/-- Equivariant open immersions induce open embeddings of invariant spectra
on their underlying topological spaces. -/
theorem s2_affineSchemeQuotientMap_isOpenEmbedding_of_openImmersion
    {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (G : Type) [Group G] [Finite G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y) [IsOpenImmersion f]
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    IsOpenEmbedding (Spec.map (CommRingCat.ofHom (s2_fixedSectionPullback G ρX ρY f hf))) := by
  let k := Spec.map (CommRingCat.ofHom (s2_fixedSectionPullback G ρX ρY f hf))
  let qX := s2_affineSchemeQuotientMap X G ρX
  let qY := s2_affineSchemeQuotientMap Y G ρY
  have he (x : X) : k (qX x) = qY (f x) :=
    congrArg (fun m => m x) (s2_affineSchemeQuotientMap_naturality G ρX ρY f hf)
  have hopen : IsOpenMap k := by
    intro U hU
    have him : k '' U = qY '' (f '' (qX ⁻¹' U)) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨x, rfl⟩ := s2_affineSchemeQuotientMap_surjective X G ρX a
        exact ⟨f x, ⟨x, ha, rfl⟩, (he x).symm⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨qX x, hx, he x⟩
    rw [him]
    exact s2_affineSchemeQuotientMap_isOpenMap Y G ρY _
      (f.isOpenEmbedding.isOpenMap _ (hU.preimage qX.continuous))
  exact .of_continuous_injective_isOpenMap k.continuous
    (s2_affineSchemeQuotientMap_injective_of_openImmersion G ρX ρY f hf) hopen

/-- Equivariant scheme isomorphisms induce isomorphisms of invariant spectra. -/
theorem s2_affineSchemeQuotientMap_isIso_of_isIso
    {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (G : Type) [Group G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y) [IsIso f]
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    IsIso (Spec.map (CommRingCat.ofHom (s2_fixedSectionPullback G ρX ρY f hf))) := by
  letI := s2_schemeSectionAction X G ρX
  letI := s2_schemeSectionAction Y G ρY
  haveI : IsIso f.appTop := by
    change IsIso (Scheme.Γ.map f.op)
    infer_instance
  have hbij : Function.Bijective (s2_fixedSectionPullback G ρX ρY f hf) := by
    constructor
    · intro a b hab
      apply Subtype.val_injective
      exact (ConcreteCategory.bijective_of_isIso f.appTop).injective (congrArg Subtype.val hab)
    · intro a
      obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso f.appTop).surjective a.val
      have hfixed (g : G) : g • b = b := by
        apply (ConcreteCategory.bijective_of_isIso f.appTop).injective
        rw [s2_schemeSectionAction_naturality G ρX ρY f hf, hb, a.property g]
      exact ⟨⟨b, hfixed⟩, Subtype.ext hb⟩
  haveI : IsIso (CommRingCat.ofHom (s2_fixedSectionPullback G ρX ρY f hf)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  infer_instance

end HodgeLean.Foundations.Program
