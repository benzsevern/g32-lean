import HodgeLean.Foundations.Program.SchoenAffineSchemeQuotientOrbits
import HodgeLean.Foundations.Program.SchoenPrincipalQuotientComparisons

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The image of an equivariant morphism is saturated under an affine finite-group quotient. -/
theorem s2_affineQuotient_preimage_image_range
    {X Y : Scheme.{0}} [IsAffine Y]
    (G : Type) [Group G] [Finite G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    s2_affineSchemeQuotientMap Y G ρY ⁻¹'
      (s2_affineSchemeQuotientMap Y G ρY '' Set.range f) = Set.range f := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, he⟩
    obtain ⟨g, hg⟩ := (s2_affineSchemeQuotientMap_fibres Y G ρY (f x) y).mp he
    refine ⟨(ρX g).asIso.hom x, ?_⟩
    exact (congrArg (fun m : X ⟶ Y => m x) (hf g)).symm.trans hg
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- Principal opens of the invariant spectrum pull back to the corresponding
principal opens of the affine scheme. -/
theorem s2_affineSchemeQuotientMap_preimage_basicOpen (X : Scheme.{0}) [IsAffine X]
    (G : Type) [Group G] (ρ : G →* Aut X) :
    letI := s2_schemeSectionAction X G ρ
    ∀ r : FixedPoints.subring Γ(X, ⊤) G,
      s2_affineSchemeQuotientMap X G ρ ⁻¹'
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (FixedPoints.subring Γ(X, ⊤) G))) =
      (X.basicOpen (r : Γ(X, ⊤)) : Set X) := by
  letI := s2_schemeSectionAction X G ρ
  intro r
  change X.isoSpec.hom ⁻¹' (PrimeSpectrum.basicOpen (r : Γ(X, ⊤)) : Set (PrimeSpectrum Γ(X, ⊤))) = _
  exact congrArg (fun U : X.Opens => (U : Set X)) (X.toSpecΓ_preimage_basicOpen (r : Γ(X, ⊤)))

/-- Every point in an equivariant affine open image has an invariant principal
neighborhood contained in that image. -/
theorem s2_equivariantOpenImmersion_principal_refinement
    {X Y : Scheme.{0}} [IsAffine Y]
    (G : Type) [Group G] [Finite G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y) [IsOpenImmersion f]
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) (x : X) :
    letI := s2_schemeSectionAction Y G ρY
    ∃ r : FixedPoints.subring Γ(Y, ⊤) G,
      f x ∈ Y.basicOpen (r : Γ(Y, ⊤)) ∧
      (Y.basicOpen (r : Γ(Y, ⊤)) : Set Y) ⊆ Set.range f := by
  letI := s2_schemeSectionAction Y G ρY
  let q := s2_affineSchemeQuotientMap Y G ρY
  have hopen : IsOpen (q '' Set.range f) :=
    s2_affineSchemeQuotientMap_isOpenMap Y G ρY _ f.isOpenEmbedding.isOpen_range
  obtain ⟨_, ⟨r, rfl⟩, hxr, hr⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hopen (q (f x))
      ⟨f x, ⟨x, rfl⟩, rfl⟩
  have hpre := s2_affineSchemeQuotientMap_preimage_basicOpen Y G ρY r
  refine ⟨r, ?_, ?_⟩
  · exact (congrArg (fun T : Set Y => f x ∈ T) hpre).mp hxr
  · intro y hy
    have hyq : q y ∈ PrimeSpectrum.basicOpen r := (congrArg (fun T : Set Y => y ∈ T) hpre).mpr hy
    have hsat := s2_affineQuotient_preimage_image_range G ρX ρY f hf
    exact hsat ▸ hr hyq

end HodgeLean.Foundations.Program
