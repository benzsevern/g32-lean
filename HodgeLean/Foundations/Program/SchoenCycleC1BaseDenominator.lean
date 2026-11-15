import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- Every rational function in the algebraic source extension has a
nonzero denominator from the original base ring, retaining the given
source section ring and its actual fraction-field embedding. -/
theorem s2e_c1_base_denominator
    {R S L : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L] (f : L) :
    ∃ r : R, r ≠ 0 ∧ ∃ b : S, algebraMap R L r * f = algebraMap S L b := by
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)
  obtain ⟨⟨b, d⟩, hd⟩ := IsLocalization.surj M f
  obtain ⟨r, hr, hdr⟩ := d.property
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, b, ?_⟩
  rw [IsScalarTower.algebraMap_apply R S L, hdr, mul_comm]
  exact hd

end HodgeLean.Foundations.Program
