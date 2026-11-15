import HodgeLean.Foundations.QuotientDuality.MonomialUnitRotation

/-! The distinguished unit root generates its actual standard etale algebra. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem unit_root_adjoin_eq_top
    (R : Type*) [CommRing R] (m : ℕ) (hm : 0 < m) (ε a : R)
    (ha : (m : R) * a = 1) (hε : IsUnit ε) :
    let Q := unitRootPair R m hm ε a ha
    Algebra.adjoin R ({Q.X} : Set Q.Ring) = ⊤ := by
  intro Q
  let S := Algebra.adjoin R ({Q.X} : Set Q.Ring)
  let u : S := ⟨Q.X, Algebra.subset_adjoin rfl⟩
  have hpow : u ^ m = algebraMap R S ε := by
    apply Subtype.ext
    change Q.X ^ m = algebraMap R Q.Ring ε
    have H := Q.hasMap_X.1
    change Polynomial.aeval Q.X (Polynomial.X ^ m - Polynomial.C ε) = 0 at H
    simpa only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] using H
  have hu : IsUnit u := (isUnit_pow_iff hm.ne').mp (by
    rw [hpow]
    exact hε.map (algebraMap R S))
  obtain ⟨φ, hφ, hφX⟩ := unitRootPair_lift m hm ε a ha (algebraMap R S) u hpow hu
  change Q.Ring →+* S at φ
  change (∀ r, φ (algebraMap R Q.Ring r) = algebraMap R S r) at hφ
  change φ Q.X = u at hφX
  have hid : S.val.toRingHom.comp φ = RingHom.id Q.Ring := by
    apply standardEtale_ringHom_ext Q
    · ext r
      change (φ (algebraMap R Q.Ring r) : S).val = algebraMap R Q.Ring r
      rw [hφ]
      rfl
    · change (φ Q.X : S).val = Q.X
      rw [hφX]
  apply eq_top_iff.mpr
  intro x hx
  have he : (φ x : S).val = x := RingHom.congr_fun hid x
  exact he ▸ (φ x).property

#print axioms unit_root_adjoin_eq_top
end HodgeLean.Foundations.QuotientDuality
