import HodgeLean.Foundations.Program.SchoenCycleC1KummerScaleHelpers
import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # Primitive divided coordinates and their actual minimal polynomials -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Dividing a primitive coordinate by a nonzero base scalar retains a
power basis. Its Kummer equation is minimal when its degree is the field degree. -/
theorem s2e_c1_divided_powerBasis
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (B : PowerBasis K L) (m : ℕ) (hm : 0 < m)
    (hdim : Module.finrank K L = m) (x c : K) (hx : x ≠ 0)
    (hz : B.gen ^ m = algebraMap K L (x ^ m * c)) :
    ∃ B' : PowerBasis K L, B'.gen = B.gen / algebraMap K L x ∧
      minpoly K B'.gen = X ^ m - C c := by
  letI : Module.Finite K L := B.finite
  let w := B.gen / algebraMap K L x
  have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
  have htop : Algebra.adjoin K ({w} : Set L) = ⊤ := by
    apply B.adjoin_eq_top_of_gen_mem_adjoin
    have hw : w ∈ Algebra.adjoin K ({w} : Set L) :=
      Algebra.subset_adjoin (Set.mem_singleton w)
    have h := (Algebra.adjoin K ({w} : Set L)).mul_mem hw
      ((Algebra.adjoin K ({w} : Set L)).algebraMap_mem x)
    simpa only [w, div_mul_cancel₀ _ hxL] using h
  let B' := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite K w) htop
  have hw : w ^ m = algebraMap K L c := by
    dsimp only [w]
    rw [div_pow, hz, map_mul, map_pow]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hxL)
  have hdeg : (minpoly K w).natDegree = m :=
    B'.natDegree_minpoly.trans (B'.finrank.symm.trans hdim)
  refine ⟨B', rfl, ?_⟩
  change minpoly K w = _
  symm
  refine minpoly.unique K w (monic_X_pow_sub_C c (Nat.ne_of_gt hm)) ?_ ?_
  · simp only [map_sub, map_pow, aeval_X, aeval_C, hw, sub_self]
  · intro q hq hq'
    refine le_trans ?_ (degree_le_of_dvd (minpoly.dvd K w hq') hq.ne_zero)
    rw [degree_X_pow_sub_C hm,
      degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite K w)), hdeg]

end HodgeLean.Foundations.Program
