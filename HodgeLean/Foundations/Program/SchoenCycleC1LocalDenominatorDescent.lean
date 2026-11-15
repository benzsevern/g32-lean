import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.Algebra.Basic

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- Rational representatives with a denominator outside each maximal ideal
come from a single original ring element. -/
theorem s2e_c1_local_denominator_descent
    {R K : Type*} [CommRing R] [Field K] (φ : R →+* K) (t : K)
    (ht : ∀ M : Ideal R, M.IsMaximal →
      ∃ s : R, s ∉ M ∧ ∃ a : R, φ s * t = φ a) :
    ∃ a : R, φ a = t := by
  let I : Ideal R :=
    { carrier := {s | ∃ a : R, φ s * t = φ a}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro s u ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by simp only [map_add, add_mul, ha, hb]⟩
      smul_mem' := by
        rintro c s ⟨a, ha⟩
        exact ⟨c * a, by simp only [smul_eq_mul, map_mul, mul_assoc, ha]⟩ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, hs, a, ha⟩ := ht M hM
    exact hs (hIM (show s ∈ I from ⟨a, ha⟩))
  have hone : (1 : R) ∈ I := by rw [hI]; trivial
  obtain ⟨a, ha⟩ := hone
  exact ⟨a, by simpa only [map_one, one_mul] using ha.symm⟩

end HodgeLean.Foundations.Program
