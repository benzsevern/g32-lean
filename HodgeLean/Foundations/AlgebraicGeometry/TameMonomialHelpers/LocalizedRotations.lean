import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.RootCoverNormality

/-! # Localizing rotations at a fixed evaluation
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.TameMonomialCover.Helpers

/-- An automorphism fixing a field evaluation extends to its prime localization and fixes the induced evaluation there.
Source: Mathlib, IsLocalization.ringEquivOfRingEquiv, IsLocalization.lift and IsLocalization.ringHom_ext. -/
theorem localized_rotation
    {A C S : Type*} [CommRing A] [Field C] [CommRing S]
    (p : A →+* C) [(RingHom.ker p).IsPrime] [Algebra A S] [IsLocalization.AtPrime S (RingHom.ker p)]
    (g : A ≃+* A) (hg : p.comp g.toRingHom = p) :
    ∃ (G : S ≃+* S) (pS : S →+* C),
      (∀ a, G (algebraMap A S a) = algebraMap A S (g a)) ∧
      pS.comp (algebraMap A S) = p ∧ pS.comp G.toRingHom = pS := by
  let q := RingHom.ker p
  haveI : q.IsPrime := RingHom.ker_isPrime p
  have hq : q.comap g.toRingHom = q := by
    change (RingHom.ker p).comap g.toRingHom = RingHom.ker p
    rw [RingHom.comap_ker, hg]
  have hM : q.primeCompl.map g.toMonoidHom = q.primeCompl := by
    have H : (q.comap g.toRingHom).primeCompl.map g.toMonoidHom = q.primeCompl :=
      g.map_primeCompl_comap_eq q
    simpa only [hq] using H
  let G : S ≃+* S := IsLocalization.ringEquivOfRingEquiv S S g hM
  have hG (a : A) : G (algebraMap A S a) = algebraMap A S (g a) :=
    IsLocalization.ringEquivOfRingEquiv_eq hM a
  have hunit : ∀ a : q.primeCompl, IsUnit (p a) := by
    intro a
    exact isUnit_iff_ne_zero.mpr a.2
  let pS : S →+* C := IsLocalization.lift hunit
  have hpS : pS.comp (algebraMap A S) = p := IsLocalization.lift_comp hunit
  refine ⟨G, pS, hG, hpS, ?_⟩
  apply IsLocalization.ringHom_ext q.primeCompl
  apply RingHom.ext
  intro a
  change pS (G (algebraMap A S a)) = pS (algebraMap A S a)
  rw [hG, IsLocalization.lift_eq, IsLocalization.lift_eq]
  exact RingHom.congr_fun hg a

end AlgebraicGeometry.TameMonomialCover.Helpers
