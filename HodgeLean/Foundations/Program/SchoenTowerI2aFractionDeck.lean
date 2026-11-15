import Mathlib.Algebra.Ring.Aut
import HodgeLean.Foundations.Program.SchoenTowerI2aFractionBase

/-! # The deck action over the coefficient fraction field
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An automorphism fixing the affine coefficient ring fixes its embedded fraction field.
Source: Mathlib, IsFractionRing.div_surjective and preservation of division by field automorphisms. -/
theorem s2v_i2a_deck_fixes_coefficient_fractions
    {R F K : Type*} [CommRing R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] (d : K ≃ₐ[R] K) (a : F) :
    d (algebraMap F K a) = algebraMap F K a := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective R a
  rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply R F K,
    ← IsScalarTower.algebraMap_apply R F K, d.commutes, d.commutes]

/-- The actual affine-ring deck automorphism acts over the embedded coefficient fraction field.
Source: Mathlib, AlgEquiv and fraction-field denominator expressions. -/
def s2v_i2a_fractionDeck
    {R F K : Type*} [CommRing R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] (d : K ≃ₐ[R] K) : K ≃ₐ[F] K :=
  { d.toRingEquiv with
    commutes' := s2v_i2a_deck_fixes_coefficient_fractions d }

/-- Changing from affine coefficients to their fraction field preserves the entire automorphism group.
Source: Mathlib, AlgEquiv.restrictScalars and fraction-field denominator expressions. -/
def s2v_i2a_fractionDeckEquiv
    {R F K : Type*} [CommRing R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] : (K ≃ₐ[R] K) ≃* (K ≃ₐ[F] K) where
  toFun := s2v_i2a_fractionDeck
  invFun := AlgEquiv.restrictScalars R
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- Passing from affine coefficients to their fraction field preserves the underlying field automorphism order.
Source: Mathlib, orderOf_injective, AlgEquiv.toRingEquiv_injective and MulEquiv.orderOf_eq. -/
theorem s2v_i2a_fractionDeck_order_eq
    {R F K : Type*} [CommRing R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] (d : K ≃ₐ[R] K) :
    orderOf (s2v_i2a_fractionDeck (F := F) d) = orderOf d.toRingEquiv := by
  let forget : (K ≃ₐ[R] K) →* (K ≃+* K) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hforget := orderOf_injective forget AlgEquiv.toRingEquiv_injective d
  have hfrac := (s2v_i2a_fractionDeckEquiv (R := R) (F := F) (K := K)).orderOf_eq d
  exact hfrac.trans hforget.symm

end HodgeLean.Foundations.Program
