import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Group.Units.Hom

/-! # Integral orders of local rational eigenfunctions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A rational eigenfunction's integral parameter exponent records the
residue character of the parameter multiplier, including negative orders. -/
theorem s2e_c1_local_rational_eigenorder_character
    {k R K : Type*} [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K] [IsFractionRing R K]
    (φ : R →ₐ[k] k) (τ : R ≃ₐ[k] R) (σ : K ≃ₐ[k] K)
    (hσ : ∀ r : R, σ (algebraMap R K r) = algebraMap R K (τ r))
    (hφ : ∀ r : R, φ (τ r) = φ r)
    (t : R) (ht : algebraMap R K t ≠ 0) (v u : Rˣ)
    (hτt : τ t = t * (v : R))
    (z : K) (n : ℤ) (hz : z = algebraMap R K (u : R) * algebraMap R K t ^ n)
    (η : k) (heig : σ z = algebraMap k K η * z) :
    φ (v : R) ^ n = η := by
  have hmapK : algebraMap R K ((v ^ n : Rˣ) : R) =
      algebraMap R K (v : R) ^ n := by
    change ((Units.map (algebraMap R K).toMonoidHom (v ^ n) : Kˣ) : K) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hmapk : φ ((v ^ n : Rˣ) : R) = φ (v : R) ^ n := by
    change ((Units.map φ.toMonoidHom (v ^ n) : kˣ) : k) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have he : algebraMap R K (τ (u : R) * ((v ^ n : Rˣ) : R)) =
      algebraMap R K (algebraMap k R η * (u : R)) := by
    apply mul_right_cancel₀ (zpow_ne_zero n ht)
    rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply k R K, hmapK]
    have he := heig
    rw [hz, map_mul, map_zpow₀, hσ, hσ, hτt, map_mul, mul_zpow] at he
    convert he using 1 <;> ring
  have heR := (IsFractionRing.injective R K) he
  have heResidue := congrArg φ heR
  rw [map_mul, map_mul, hφ, φ.commutes, hmapk] at heResidue
  apply mul_right_cancel₀ (show φ (u : R) ≠ 0 from
    (u.isUnit.map φ.toRingHom).ne_zero)
  simpa only [mul_comm, Algebra.algebraMap_self_apply] using heResidue

end HodgeLean.Foundations.Program
