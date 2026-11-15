import HodgeLean.Foundations.Program.SchoenAffineSchemeQuotientOrbits
import HodgeLean.Foundations.Program.SchoenInvariantPrincipalSchemeCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting an open immersion over an open contained in its image gives an isomorphism. -/
theorem s2_openImmersion_restriction_isIso {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens)
    (hU : (U : Set Y) ⊆ Set.range f) : IsIso (f ∣_ U) := by
  have hsurj : Function.Surjective (f ∣_ U) := by
    intro y
    obtain ⟨x, hx⟩ := hU y.property
    have hxU : x ∈ f ⁻¹ᵁ U := by
      change f x ∈ U
      rw [hx]
      exact y.property
    let z : (f ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
    refine ⟨z, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    have he := congrArg (fun g => g z) (morphismRestrict_ι f U)
    exact he.trans hx
  haveI : Epi (f ∣_ U).base := ConcreteCategory.epi_of_surjective _ hsurj
  exact IsOpenImmersion.isIso (f ∣_ U)

/-- Equivariant morphisms pull invariant opens back to invariant opens. -/
theorem s2_equivariant_preimage_invariant {X Y : Scheme.{0}}
    (G : Type) [Group G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f)
    (U : Y.Opens) (hU : ∀ g : G, (ρY g).asIso.hom ⁻¹ᵁ U = U) :
    ∀ g : G, (ρX g).asIso.hom ⁻¹ᵁ (f ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
  intro g
  rw [← Scheme.Hom.comp_preimage, ← hf g, Scheme.Hom.comp_preimage, hU g]

/-- Restricting an equivariant map to an invariant open preserves equivariance
for the constructed restricted group actions. -/
theorem s2_equivariant_morphismRestrict {X Y : Scheme.{0}}
    (G : Type) [Group G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f)
    (U : Y.Opens) (hU : ∀ g : G, (ρY g).asIso.hom ⁻¹ᵁ U = U) (g : G) :
    (f ∣_ U) ≫ (s2_invariantOpenAction G ρY U hU g).asIso.hom =
      (s2_invariantOpenAction G ρX (f ⁻¹ᵁ U)
        (s2_equivariant_preimage_invariant G ρX ρY f hf U hU) g).asIso.hom ≫ (f ∣_ U) := by
  apply (cancel_mono U.ι).mp
  change ((f ∣_ U) ≫ s2_invariantOpenMap U (ρY g).asIso.hom (hU g).ge) ≫ U.ι =
    (s2_invariantOpenMap (f ⁻¹ᵁ U) (ρX g).asIso.hom
      (s2_equivariant_preimage_invariant G ρX ρY f hf U hU g).ge ≫ (f ∣_ U)) ≫ U.ι
  simp only [Category.assoc, s2_invariantOpenMap_ι, morphismRestrict_ι,
    s2_invariantOpenMap_ι_assoc, morphismRestrict_ι_assoc]
  exact congrArg (fun k : X ⟶ Y => (f ⁻¹ᵁ U).ι ≫ k) (hf g)

/-- Over an invariant affine open contained in an equivariant open image, the
restricted invariant spectra are isomorphic through their actual pullback map. -/
theorem s2_equivariant_restriction_quotient_isIso {X Y : Scheme.{0}}
    (G : Type) [Group G] (ρX : G →* Aut X) (ρY : G →* Aut Y)
    (f : X ⟶ Y) [IsOpenImmersion f]
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f)
    (U : Y.Opens) (hU : ∀ g : G, (ρY g).asIso.hom ⁻¹ᵁ U = U)
    [IsAffine U.toScheme] [IsAffine (f ⁻¹ᵁ U).toScheme]
    (him : (U : Set Y) ⊆ Set.range f) :
    IsIso (Spec.map (CommRingCat.ofHom (s2_fixedSectionPullback G
      (s2_invariantOpenAction G ρX (f ⁻¹ᵁ U)
        (s2_equivariant_preimage_invariant G ρX ρY f hf U hU))
      (s2_invariantOpenAction G ρY U hU) (f ∣_ U)
      (s2_equivariant_morphismRestrict G ρX ρY f hf U hU)))) := by
  haveI := s2_openImmersion_restriction_isIso f U him
  exact s2_affineSchemeQuotientMap_isIso_of_isIso G
    (s2_invariantOpenAction G ρX (f ⁻¹ᵁ U)
      (s2_equivariant_preimage_invariant G ρX ρY f hf U hU))
    (s2_invariantOpenAction G ρY U hU) (f ∣_ U)
    (s2_equivariant_morphismRestrict G ρX ρY f hf U hU)

end HodgeLean.Foundations.Program
