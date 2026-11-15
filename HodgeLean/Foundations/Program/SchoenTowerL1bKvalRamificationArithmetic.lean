import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

namespace HodgeLean.Foundations.Program

/-- The binomial order equation transports an inertia character residue to the base order. -/
theorem s2v_l1b_kval_ramification_residue
    {m e q v w k : ℤ} (he : e ≠ 0) (hm : m = e * q)
    (horder : m * v = e * w) (hres : Int.ModEq e v k) :
    Int.ModEq m w (q * k) := by
  have hc : e * w = e * (q * v) := by
    calc
      e * w = m * v := horder.symm
      _ = e * (q * v) := by rw [hm, mul_assoc]
  have hw : w = q * v := mul_left_cancel₀ he hc
  obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp hres
  apply Int.modEq_iff_dvd.mpr
  refine ⟨z, ?_⟩
  rw [hw, hm, ← mul_sub, hz]
  ring

end HodgeLean.Foundations.Program
