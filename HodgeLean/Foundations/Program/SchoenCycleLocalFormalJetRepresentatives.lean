import HodgeLean.Foundations.Program.SchoenCycleAdicIdealPowerValues

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every finite formal local jet is represented by an actual local-ring element with the specified power-ideal error.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_local_formal_jet_representative
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : ℕ) (z : AdicCompletion (IsLocalRing.maximalIdeal R) R) :
    ∃ r : R, AdicCompletion.of (IsLocalRing.maximalIdeal R) R r - z ∈
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ N := by
  let I := IsLocalRing.maximalIdeal R
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (z.val N)
  refine ⟨r, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map]
  apply (s2e_adic_extended_power_mem_iff I (IsNoetherian.noetherian I) N _).mpr
  change (AdicCompletion.of I R r).val N - z.val N = 0
  exact sub_eq_zero.mpr hr

#print axioms s2e_local_formal_jet_representative
end HodgeLean.Foundations.Program
