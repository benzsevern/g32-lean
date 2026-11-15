import HodgeLean.Foundations.Program.SchoenTowerI2aUnitRootCover

/-! # Automorphisms of the universal unit-root cover
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Maps from a standard etale ring agree when they agree on its coefficients and distinguished root.
Source: Mathlib, StandardEtalePair.hom_ext. -/
theorem s2v_i2a_standardEtale_ringHom_ext
    {R S : Type*} [CommRing R] [CommRing S] (P : StandardEtalePair R)
    (f g : P.Ring →+* S)
    (hR : f.comp (algebraMap R P.Ring) = g.comp (algebraMap R P.Ring))
    (hX : f P.X = g P.X) : f = g := by
  letI : Algebra R S := (f.comp (algebraMap R P.Ring)).toAlgebra
  let fA : P.Ring →ₐ[R] S := { f with commutes' := fun _ => rfl }
  let gA : P.Ring →ₐ[R] S := { g with commutes' := fun r => (RingHom.congr_fun hR r).symm }
  have H : fA = gA := P.hom_ext hX
  exact congrArg AlgHom.toRingHom H

/-- A coefficient automorphism fixing the unit extends to the unit-root cover while fixing its distinguished root.
Source: Mathlib, StandardEtalePair.lift and s2v_i2a_standardEtale_ringHom_ext. -/
theorem s2v_i2a_unitRoot_rotation
    (R : Type*) [CommRing R] (m : ℕ) (hm : 0 < m) (ε a : R)
    (ha : (m : R) * a = 1) (g : R ≃+* R) (hg : g ε = ε) :
    let Q := s2v_i2a_unitRootPair R m hm ε a ha
    ∃ G : Q.Ring ≃+* Q.Ring,
      (∀ r, G (algebraMap R Q.Ring r) = algebraMap R Q.Ring (g r)) ∧ G Q.X = Q.X := by
  intro Q
  have hX : Q.X ^ m = algebraMap R Q.Ring ε := by
    have H := Q.hasMap_X.1
    change Polynomial.aeval Q.X (Polynomial.X ^ m - Polynomial.C ε) = 0 at H
    simpa only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] using H
  have hunit : IsUnit Q.X := by
    have H := Q.hasMap_X.2
    change IsUnit (Polynomial.aeval Q.X Polynomial.X) at H
    simpa only [Polynomial.aeval_X] using H
  have hg' : g.symm ε = ε := by
    apply g.injective
    rw [g.apply_symm_apply, hg]
  obtain ⟨φ, hφ, hφX⟩ := s2v_i2a_unitRootPair_lift m hm ε a ha
    ((algebraMap R Q.Ring).comp g.toRingHom) Q.X (by change Q.X ^ m = algebraMap R Q.Ring (g ε); rw [hg, hX]) hunit
  obtain ⟨ψ, hψ, hψX⟩ := s2v_i2a_unitRootPair_lift m hm ε a ha
    ((algebraMap R Q.Ring).comp g.symm.toRingHom) Q.X (by change Q.X ^ m = algebraMap R Q.Ring (g.symm ε); rw [hg', hX]) hunit
  change (∀ r, φ (algebraMap R Q.Ring r) = algebraMap R Q.Ring (g r)) at hφ
  change (∀ r, ψ (algebraMap R Q.Ring r) = algebraMap R Q.Ring (g.symm r)) at hψ
  change φ Q.X = Q.X at hφX
  change ψ Q.X = Q.X at hψX
  have hleft : ψ.comp φ = RingHom.id Q.Ring := by
    apply s2v_i2a_standardEtale_ringHom_ext Q
    · apply RingHom.ext
      intro r
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ, hψ, g.symm_apply_apply]
    · simp only [RingHom.comp_apply, RingHom.id_apply, hφX, hψX]
  have hright : φ.comp ψ = RingHom.id Q.Ring := by
    apply s2v_i2a_standardEtale_ringHom_ext Q
    · apply RingHom.ext
      intro r
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ, hψ, g.apply_symm_apply]
    · simp only [RingHom.comp_apply, RingHom.id_apply, hφX, hψX]
  let G : Q.Ring ≃+* Q.Ring :=
    { φ with
      invFun := ψ
      left_inv := fun x => RingHom.congr_fun hleft x
      right_inv := fun x => RingHom.congr_fun hright x }
  exact ⟨G, hφ, hφX⟩

end HodgeLean.Foundations.Program
