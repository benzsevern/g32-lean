import HodgeLean.Foundations.Program.SchoenCycleU1SectionJets
import Mathlib.RingTheory.Localization.Basic

/-! # Detecting local first-order variation on affine sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A stationary dual-number map on a ring stays stationary on every
localization to which it extends.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, localization and tangent vectors. -/
theorem s2e_u1_localization_jet_stationary
    (A S : Type*) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S]
    (f : S →+* DualNumber ℂ)
    (hf : ∀ a : A, (f (algebraMap A S a)).snd = 0) :
    ∀ s : S, (f s).snd = 0 := by
  let g : S →+* DualNumber ℂ := (TrivSqZeroExt.inlHom ℂ ℂ).comp
    ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp f)
  have he : f = g := by
    apply IsLocalization.ringHom_ext M
    ext a : 1
    apply TrivSqZeroExt.ext
    · rfl
    · exact hf a
  intro s
  rw [he]
  rfl

/-- A nonzero first-order variation on a localization is already visible on
an element of the original ring.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_u1_localization_jet_detected
    (A S : Type*) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S]
    (f : S →+* DualNumber ℂ) (h : ∃ s : S, (f s).snd ≠ 0) :
    ∃ a : A, (f (algebraMap A S a)).snd ≠ 0 := by
  by_contra hn
  have hz : ∀ a : A, (f (algebraMap A S a)).snd = 0 := by
    simpa only [not_exists, not_not] using hn
  obtain ⟨s, hs⟩ := h
  exact hs (s2e_u1_localization_jet_stationary A S M f hz s)

/-- Every nonstationary dual-number map on an actual scheme stalk is detected
by a regular section of any affine neighbourhood of that point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, local rings of affine schemes. -/
theorem s2e_u1_stalk_jet_detected_on_affine
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U) (p : U)
    (f : X.presheaf.stalk p.val →+* DualNumber ℂ)
    (h : ∃ s : X.presheaf.stalk p.val, (f s).snd ≠ 0) :
    ∃ a : Γ(X, U), (f ((X.presheaf.germ U p.val p.property).hom a)).snd ≠ 0 := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf p
  letI := hU.isLocalization_stalk p
  exact s2e_u1_localization_jet_detected Γ(X, U) (X.presheaf.stalk p.val)
    (hU.primeIdealOf p).asIdeal.primeCompl f h

end HodgeLean.Foundations.Program
