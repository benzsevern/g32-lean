import HodgeLean.Ported.Hironaka.Algebra.Local.QuotientParameters
import HodgeLean.Ported.Hironaka.Algebra.Local.Defs

/-! Adapt a regular parameter system to a regular quotient of a specified codimension. -/
noncomputable section
set_option maxHeartbeats 400000
open IsLocalRing
namespace HodgeLean.Foundations.Program

/-- The dimension drop fixes the number of initial parameters generating a regular quotient ideal. -/
theorem g32l4_regular_quotient_parameters_of_codimension
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) [IsRegularLocalRing (R ⧸ I)] (r : ℕ)
    (hcodim : ringKrullDim (R ⧸ I) + r = ringKrullDim R) :
    ∃ (n : ℕ) (z : Fin n → R), r ≤ n ∧ IsRegularSystemOfParameters z ∧
      I = Ideal.span (z '' {j | j.val < r}) := by
  obtain ⟨n, c, z, hcn, hn, hm, hIz⟩ :=
    IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt I
  have hdim := ringKrullDim_quotient_span_image_lt z hm hn hcn
  rw [← hIz] at hdim
  obtain ⟨q, hq⟩ := exists_ringKrullDim_eq_natCast (R ⧸ I)
  have hqc : q + c = n := by
    rw [hq, ← hn] at hdim
    exact_mod_cast hdim
  have hqr : q + r = n := by
    rw [hq, ← hn] at hcodim
    exact_mod_cast hcodim
  have hcr : c = r := by omega
  subst c
  exact ⟨n, z, hcn, ⟨hm.symm, hn⟩, hIz⟩

end HodgeLean.Foundations.Program
