import HodgeLean.Foundations.Program.SchoenTowerSheafDefs
import Mathlib.Algebra.Ring.GeomSum

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2v_character_average_eigen {R : Type*} [Ring R] [Algebra ℂ R]
    (T : R) (m : ℕ) (hT : T ^ m = 1) (ζ : ℂ)
    (hζ : ζ ^ m = 1) (hζ0 : ζ ≠ 0) :
    T * (∑ t ∈ Finset.range m, ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) • T ^ t) =
      ζ • (∑ t ∈ Finset.range m, ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) • T ^ t) := by
  let Q : R := ζ⁻¹ • T
  let S : R := ∑ t ∈ Finset.range m, Q ^ t
  have hQ : Q ^ m = 1 := by
    dsimp only [Q]
    rw [smul_pow, hT, inv_pow, hζ, inv_one, one_smul]
  have hQS : Q * S = S := by
    have h := mul_geom_sum Q m
    rw [hQ, sub_self, sub_mul, one_mul] at h
    exact sub_eq_zero.mp h
  have hTS : T * S = ζ • S := by
    have h := congrArg (fun x : R => ζ • x) hQS
    simpa only [Q, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hζ0, one_smul] using h
  have hP : (∑ t ∈ Finset.range m,
      ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) • T ^ t) = (m : ℂ)⁻¹ • S := by
    dsimp only [S, Q]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [smul_pow, smul_smul]
    simp only [zpow_neg, zpow_natCast, inv_pow]
  rw [hP, mul_smul_comm, hTS, smul_comm]

theorem s2v_locallyConstant_comap_pow {X : Type*} [TopologicalSpace X]
    (g : C(X, X)) (n : ℕ) (s : LocallyConstant X ℂ) (x : X) :
    ((LocallyConstant.comapₗ ℂ g : Module.End ℂ (LocallyConstant X ℂ)) ^ n) s x =
      s (g^[n] x) := by
  induction n generalizing s x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    change s (g (g^[n] x)) = s (g^[n + 1] x)
    rw [Function.iterate_succ_apply']

end HodgeLean.Foundations.Program
