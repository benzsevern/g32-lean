import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantAffine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Dominance for actual invariant charts

Injective ring maps induce dominant affine morphisms.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- An injective ring map induces a dominant map of the actual spectra.
Source: Stacks Project, tag 00FL, density of the image on prime spectra. -/
theorem s2v_l1a_specMap_dominant_of_injective
    {R A : CommRingCat} (φ : R ⟶ A) (hφ : Function.Injective φ.hom) :
    IsDominant (Spec.map φ) := by
  constructor
  change DenseRange (PrimeSpectrum.comap φ.hom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot φ.hom).mp hφ]
  exact bot_le

/-- Dominant affine chart maps with compatible source maps give a dominant global morphism.
Source: Hartshorne, Algebraic Geometry, II.3, locality of density on an open cover. -/
theorem s2v_l1a_dominant_of_chart_factorizations
    {X Y : Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)
    (V : 𝒰.I₀ → Scheme) (v : ∀ i, V i ⟶ X)
    (q : ∀ i, V i ⟶ 𝒰.X i) [∀ i, IsDominant (q i)]
    (h : ∀ i, v i ≫ f = q i ≫ 𝒰.f i) : IsDominant f := by
  constructor
  intro y
  obtain ⟨i, z, rfl⟩ := 𝒰.exists_eq y
  apply closure_mono (s := (𝒰.f i) '' Set.range (q i)) ?_
    (mem_closure_image (𝒰.f i).continuous.continuousAt ((q i).denseRange z))
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  have heq := congrArg (fun g : V i ⟶ Y => g w) (h i)
  exact ⟨v i w, by simpa only [Scheme.Hom.comp_apply] using heq⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical map to the actual invariant-ring scheme has dense image.
Source: Stacks Project, tags 00FL and 01LH, dominance of injective ring maps and relative affine gluing. -/
theorem s2v_l1a_toInvariantSpace_dominant
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    IsDominant (s2v_l1a_toInvariantSpace f a ha) := by
  let q (U : Y.AffineZariskiSite) :=
    (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (s2v_l1a_fixedSectionSubring f a ha U.1).subtype)
  have (U : Y.AffineZariskiSite) : IsDominant (q U) := by
    have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
    have : IsDominant (Spec.map (CommRingCat.ofHom
        (s2v_l1a_fixedSectionSubring f a ha U.1).subtype)) :=
      s2v_l1a_specMap_dominant_of_injective _ Subtype.val_injective
    dsimp [q, Scheme.Opens.toSpecΓ]
    infer_instance
  exact s2v_l1a_dominant_of_chart_factorizations _
    (s2v_l1a_invariantSpaceCover f a ha)
    (fun U : Y.AffineZariskiSite => (f ⁻¹ᵁ U.1).toScheme)
    (fun U => (f ⁻¹ᵁ U.1).ι) q
    (fun U => s2v_l1a_toInvariantSpace_chart f a ha ⟨U.1, U.2⟩)

end HodgeLean.Foundations.Program
