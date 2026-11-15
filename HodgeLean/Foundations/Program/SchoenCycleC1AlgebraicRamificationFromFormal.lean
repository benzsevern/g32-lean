import HodgeLean.Foundations.Program.SchoenCycleC1CompletedParameterOrder
import Mathlib.RingTheory.PowerSeries.Expand

/-! # Actual local ramification equations from the formal power model -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- A power-expansion identity for the actual completed local map constructs
the same ramification power in the original DVR, with an original-ring unit. -/
theorem s2e_c1_algebraic_ramification_of_formal_power
    {k R S : Type*} [Field k]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (φ : R →+* S)
    (F : AdicCompletion (IsLocalRing.maximalIdeal R) R →+*
      AdicCompletion (IsLocalRing.maximalIdeal S) S)
    (hF : ∀ r, F (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
      algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (φ r))
    (ER : PowerSeries k ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (ES : PowerSeries k ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S)
    (e : ℕ) (he : 0 < e)
    (hpower : ∀ f, F (ER f) = ES (PowerSeries.expand e (Nat.ne_of_gt he) f))
    (t : R) (ht : Irreducible t) (s : S) (hs : Irreducible s) :
    ∃ w : Sˣ, φ t = (w : S) * s ^ e := by
  let CS := AdicCompletion (IsLocalRing.maximalIdeal S) S
  let Ψ : S →+* PowerSeries k := ES.symm.toRingHom.comp (algebraMap S CS)
  have htorder := s2e_c1_completed_parameter_order t ht ER
  have hsorder : (Ψ s).order = 1 := s2e_c1_completed_parameter_order s hs ES
  have himage : Ψ (φ t) = PowerSeries.expand e (Nat.ne_of_gt he)
      (ER.symm (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) t)) := by
    apply ES.injective
    change ES (ES.symm (algebraMap S CS (φ t))) = _
    rw [ES.apply_symm_apply, ← hpower, ER.apply_symm_apply, hF]
  have horder : (Ψ (φ t)).order = (e : ℕ∞) := by
    rw [himage, PowerSeries.order_expand, htorder, nsmul_one]
  have hnonzero : φ t ≠ 0 := by
    intro hzero
    have ho := horder
    rw [hzero, map_zero, PowerSeries.order_zero] at ho
    exact ENat.top_ne_natCast e ho
  obtain ⟨q, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hnonzero hs
  have hqorder : (Ψ (φ t)).order = (q : ℕ∞) := by
    rw [hw, map_mul, map_pow, PowerSeries.order_mul,
      PowerSeries.order_zero_of_isUnit (w.isUnit.map Ψ), zero_add,
      PowerSeries.order_pow, hsorder, nsmul_one]
  have hq : q = e := ENat.natCast_inj.mp (hqorder.symm.trans horder)
  exact ⟨w, by simpa only [hq] using hw⟩

end HodgeLean.Foundations.Program
