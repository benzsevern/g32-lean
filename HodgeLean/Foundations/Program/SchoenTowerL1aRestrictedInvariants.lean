import HodgeLean.Foundations.Program.SchoenTowerL1aRetainedInvariants
import HodgeLean.Foundations.Program.SchoenTowerL1aConjugateInvariants

/-! # Actual invariant rings on restricted affine schemes

The affine invariant-ring identification transports to global sections on the
actual open subschemes. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- The actual restricted affine map has injective global section pullback with invariant image.
Source: Stacks Project, tags 04A9 and 01LH, invariant sections and affine restriction. -/
theorem s2v_l1a_restricted_invariant_image
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y)
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) (U : Y.Opens)
    (hinj : Function.Injective (f.app U).hom)
    (himage : ∀ s : Γ(X, f ⁻¹ᵁ U), s ∈ Set.range (f.app U).hom ↔
      ∀ t, (s2v_l1a_saturatedSectionEnd f a ha U t).hom s = s) :
    let hpre : ∀ t, f ⁻¹ᵁ U ≤ (a t) ⁻¹ᵁ (f ⁻¹ᵁ U) := fun t => by
      rw [← Scheme.Hom.comp_preimage, ha t]
    Function.Injective (f ∣_ U).appTop.hom ∧
      ∀ s : Γ((f ⁻¹ᵁ U).toScheme, ⊤), s ∈ Set.range (f ∣_ U).appTop.hom ↔
        ∀ t, ((a t).resLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) (hpre t)).appTop.hom s = s := by
  let hpre : ∀ t, f ⁻¹ᵁ U ≤ (a t) ⁻¹ᵁ (f ⁻¹ᵁ U) := fun t => by
    rw [← Scheme.Hom.comp_preimage, ha t]
  apply s2v_l1a_conjugate_invariant_image (f.app U).hom
    (fun t => (s2v_l1a_saturatedSectionEnd f a ha U t).hom) hinj himage
    U.topIso.commRingCatIsoToRingEquiv (f ⁻¹ᵁ U).topIso.commRingCatIsoToRingEquiv
  · intro r
    have heq := (arrowResLEAppIso f U (f ⁻¹ᵁ U) le_rfl).hom.w
    change U.topIso.hom ≫ f.appLE U (f ⁻¹ᵁ U) le_rfl =
      (f.resLE U (f ⁻¹ᵁ U) le_rfl).appTop ≫ (f ⁻¹ᵁ U).topIso.hom at heq
    rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at heq
    exact congrArg (fun p : Γ(U.toScheme, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U) => p.hom r) heq.symm
  · intro t s
    have heq := (arrowResLEAppIso (a t) (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) (hpre t)).hom.w
    exact congrArg (fun p : Γ((f ⁻¹ᵁ U).toScheme, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U) => p.hom s) heq.symm

/-- Any specified lifts to the actual restricted source have the same invariant-image identification.
Source: Stacks Project, tag 04A9, invariant sections under open restriction. -/
theorem s2v_l1a_restricted_lift_invariant_image
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y)
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) (U : Y.Opens)
    (hinj : Function.Injective (f.app U).hom)
    (himage : ∀ s : Γ(X, f ⁻¹ᵁ U), s ∈ Set.range (f.app U).hom ↔
      ∀ t, (s2v_l1a_saturatedSectionEnd f a ha U t).hom s = s)
    (ρ : T → ((f ⁻¹ᵁ U).toScheme ⟶ (f ⁻¹ᵁ U).toScheme))
    (hρ : ∀ t, ρ t ≫ (f ⁻¹ᵁ U).ι = (f ⁻¹ᵁ U).ι ≫ a t) :
    Function.Injective (f ∣_ U).appTop.hom ∧
      ∀ s : Γ((f ⁻¹ᵁ U).toScheme, ⊤), s ∈ Set.range (f ∣_ U).appTop.hom ↔
        ∀ t, (ρ t).appTop.hom s = s := by
  have H := s2v_l1a_restricted_invariant_image f a ha U hinj himage
  let hpre : ∀ t, f ⁻¹ᵁ U ≤ (a t) ⁻¹ᵁ (f ⁻¹ᵁ U) := fun t => by
    rw [← Scheme.Hom.comp_preimage, ha t]
  have heq (t : T) : ρ t = (a t).resLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) (hpre t) := by
    rw [← cancel_mono (f ⁻¹ᵁ U).ι, hρ, Scheme.Hom.resLE_comp_ι]
  simpa only [← heq] using H

end HodgeLean.Foundations.Program
