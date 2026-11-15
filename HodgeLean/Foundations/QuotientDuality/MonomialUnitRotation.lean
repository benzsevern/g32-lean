import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.UnitRootRotations

/-! Scalar rotations of the distinguished unit root in the tame cover. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem unit_root_scalar_rotation
    (R : Type*) [CommRing R] (m : ℕ) (hm : 0 < m) (ε a : R)
    (ha : (m : R) * a = 1) (ζ : Rˣ) (hζ : (ζ : R) ^ m = 1) :
    let Q := unitRootPair R m hm ε a ha
    ∃ G : Q.Ring ≃ₐ[R] Q.Ring,
      G Q.X = algebraMap R Q.Ring (ζ : R) * Q.X := by
  intro Q
  have hX : Q.X ^ m = algebraMap R Q.Ring ε := by
    have H := Q.hasMap_X.1
    change Polynomial.aeval Q.X (Polynomial.X ^ m - Polynomial.C ε) = 0 at H
    simpa only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] using H
  have hunit : IsUnit Q.X := by
    have H := Q.hasMap_X.2
    change IsUnit (Polynomial.aeval Q.X Polynomial.X) at H
    simpa only [Polynomial.aeval_X] using H
  have hζinv : ((ζ⁻¹ : Rˣ) : R) ^ m = 1 := by
    have ht : ζ ^ m = 1 := Units.ext hζ
    have ht' : (ζ⁻¹) ^ m = 1 := by rw [inv_pow, ht, inv_one]
    exact congrArg Units.val ht'
  obtain ⟨φ, hφ, hφX⟩ := unitRootPair_lift m hm ε a ha
    (algebraMap R Q.Ring) (algebraMap R Q.Ring (ζ : R) * Q.X)
    (by rw [mul_pow, ← map_pow, hζ, map_one, one_mul, hX])
    (((ζ.isUnit).map (algebraMap R Q.Ring)).mul hunit)
  obtain ⟨ψ, hψ, hψX⟩ := unitRootPair_lift m hm ε a ha
    (algebraMap R Q.Ring) (algebraMap R Q.Ring ((ζ⁻¹ : Rˣ) : R) * Q.X)
    (by rw [mul_pow, ← map_pow, hζinv, map_one, one_mul, hX])
    (((ζ⁻¹).isUnit.map (algebraMap R Q.Ring)).mul hunit)
  change Q.Ring →+* Q.Ring at φ ψ
  change (∀ r, φ (algebraMap R Q.Ring r) = algebraMap R Q.Ring r) at hφ
  change (∀ r, ψ (algebraMap R Q.Ring r) = algebraMap R Q.Ring r) at hψ
  change φ Q.X = algebraMap R Q.Ring (ζ : R) * Q.X at hφX
  change ψ Q.X = algebraMap R Q.Ring ((ζ⁻¹ : Rˣ) : R) * Q.X at hψX
  have hleft : ψ.comp φ = RingHom.id Q.Ring := by
    apply standardEtale_ringHom_ext Q
    · apply RingHom.ext
      intro r
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ, hψ]
    · simp only [RingHom.comp_apply, RingHom.id_apply, hφX, map_mul, hψ, hψX]
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, one_mul]
  have hright : φ.comp ψ = RingHom.id Q.Ring := by
    apply standardEtale_ringHom_ext Q
    · apply RingHom.ext
      intro r
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ, hψ]
    · simp only [RingHom.comp_apply, RingHom.id_apply, hψX, map_mul, hφ, hφX]
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, one_mul]
  let G : Q.Ring ≃ₐ[R] Q.Ring :=
    { φ with
      invFun := ψ
      left_inv := fun x => RingHom.congr_fun hleft x
      right_inv := fun x => RingHom.congr_fun hright x
      commutes' := hφ }
  exact ⟨G, hφX⟩

#print axioms unit_root_scalar_rotation
end HodgeLean.Foundations.QuotientDuality
