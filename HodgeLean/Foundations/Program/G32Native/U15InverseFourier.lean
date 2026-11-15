import HodgeLean.Foundations.Program.G32Native.U15Defs
import HodgeLean.Foundations.Representation.OrderedKunnethStageTwoFourier
import Mathlib.Algebra.Group.Commute.Units

/-! # Inverse-power Fourier combinations with the retained variance -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.OrderedKunneth.StageTwo
namespace HodgeLean.Foundations.Program.G32Native

/-- In a finite-order monoid orbit, the retained inverse exponent is a power of the inverse generator. -/
theorem inverse_power_eq {M : Type*} [Monoid M]
    (T : M) (m : ℕ) (hm : 0 < m) (hT : T ^ m = 1) (t : Fin m) :
    T ^ (m - t.val) = (T ^ (m - 1)) ^ t.val := by
  have hu : IsUnit T := IsUnit.of_pow_eq_one hT hm.ne'
  apply (hu.pow t.val).mul_right_cancel
  have h₁ : T ^ (m - t.val) * T ^ t.val = 1 := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt t.isLt), hT]
  have hbase : T ^ (m - 1) * T = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hm, hT]
  have h₂ : (T ^ (m - 1)) ^ t.val * T ^ t.val = 1 := by
    rw [← (Commute.pow_left (Commute.refl T) (m - 1)).mul_pow, hbase, one_pow]
  exact h₁.trans h₂.symm

#print axioms inverse_power_eq
/-- The residue character at a negative index is the inverse of its ordinary power. -/
theorem inverse_character_coefficient {K : Type*} [Field K]
    (m : ℕ) (hm : 0 < m) (ζ : K) (hζ : IsPrimitiveRoot ζ m) (t : Fin m) :
    ζ ^ (-(t.val : ZMod m)).val = (ζ ^ t.val)⁻¹ := by
  letI : NeZero m := ⟨hm.ne'⟩
  rw [ZMod.neg_val]
  by_cases ht : t.val = 0
  · simp only [ht, Nat.cast_zero, ite_true, pow_zero, inv_one]
  · have hz : (t.val : ZMod m) ≠ 0 := by
      intro he
      have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt t.isLt, ZMod.val_zero] at hv
      exact ht hv
    rw [ite_eq_right hz, ZMod.val_natCast_of_lt t.isLt,
      pow_sub₀ ζ (hζ.ne_zero hm.ne') (Nat.le_of_lt t.isLt), hζ.pow_eq_one, one_mul]

#print axioms inverse_character_coefficient
/-- The retained inverse-power combination is the Fourier projector for the inverse generator. -/
theorem primitiveOrbit_eq_fourier
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (m : ℕ) (hm : 1 < m) (hT : T ^ m = 1)
    (ζ : K) (hζ : IsPrimitiveRoot ζ m) (v : V) :
    primitiveOrbit T m (fun t : ZMod m => ζ ^ t.val) v =
      (m : K) • fourierProjector m ζ (T ^ (m - 1)) ⟨1, hm⟩ v := by
  have hm0 : 0 < m := by omega
  have hchar : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
  unfold primitiveOrbit s2e_weightedSum fourierProjector
  rw [LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hchar, one_smul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pow_one]
  apply Finset.sum_congr rfl
  intro t _
  rw [inverse_character_coefficient m hm0 ζ hζ t, inverse_power_eq T m hm0 hT t]

#print axioms primitiveOrbit_eq_fourier
/-- The retained inverse-power character combination has the inverse character eigenvalue. -/
theorem primitiveOrbit_eigen
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (m : ℕ) (hm : 1 < m) (hT : T ^ m = 1)
    (ζ : K) (hζ : IsPrimitiveRoot ζ m) (v : V) :
    T (primitiveOrbit T m (fun t : ZMod m => ζ ^ t.val) v) =
      ζ⁻¹ • primitiveOrbit T m (fun t : ZMod m => ζ ^ t.val) v := by
  have hm0 : 0 < m := by omega
  have hz : ζ ≠ 0 := hζ.ne_zero hm0.ne'
  have hchar : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
  let B := T ^ (m - 1)
  let u := primitiveOrbit T m (fun t : ZMod m => ζ ^ t.val) v
  have hB : B ^ m = 1 := by
    dsimp only [B]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hT, one_pow]
  have hBu : B u = ζ • u := by
    dsimp only [u]
    rw [primitiveOrbit_eq_fourier T m hm hT ζ hζ v, map_smul,
      fourier_eigen m hm0 ζ hζ hchar B hB ⟨1, hm⟩ v, pow_one]
    exact smul_comm _ _ _
  have hTB : T.comp B = LinearMap.id := by
    change T * T ^ (m - 1) = 1
    rw [← pow_succ', Nat.sub_add_cancel hm0, hT]
  have he := congrArg T hBu
  rw [map_smul, ← LinearMap.comp_apply T B, hTB, LinearMap.id_apply] at he
  calc
    T u = ζ⁻¹ • (ζ • T u) := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
    _ = ζ⁻¹ • u := congrArg (fun z => ζ⁻¹ • z) he.symm

#print axioms primitiveOrbit_eigen
end HodgeLean.Foundations.Program.G32Native
