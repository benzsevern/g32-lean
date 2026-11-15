import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver
import Mathlib.RingTheory.DualNumber

/-! # The single actual point of the complex dual-number spectrum -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every prime of the complex dual-number ring is the kernel of its residue map.
Source: Hartshorne, Algebraic Geometry, II.8, the dual-number infinitesimal point. -/
theorem s2e_u1_dualSpectrum_subsingleton : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
  have hm (p : PrimeSpectrum (DualNumber ℂ)) (d : DualNumber ℂ) :
      d ∈ p.asIdeal ↔ d.fst = 0 := by
    constructor
    · intro hd
      by_contra h
      have hu : IsUnit d := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)
      exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hd hu)
    · intro hd
      have hs : d ^ 2 = 0 := by
        apply TrivSqZeroExt.ext <;> simp [pow_two, DualNumber.snd_mul, hd]
      apply p.isPrime.mem_of_pow_mem 2
      rw [hs]
      exact p.asIdeal.zero_mem
  refine ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun d => ?_)⟩
  exact (hm p d).trans (hm q d).symm

end HodgeLean.Foundations.Program
