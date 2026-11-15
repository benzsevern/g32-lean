import HodgeLean.Foundations.Program.SchoenTowerL1bParameterCoordinates
import HodgeLean.Foundations.Program.SchoenCycleAdicCoordinates
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite regular parameter coordinates assemble into one-variable series
coordinates on the adic ring, preserving polynomial evaluation. -/
theorem s2v_l1b_parameter_adic_coordinates
    {k : Type*} [Field k] (R : Type*) [CommRing R] [Algebra k R] [IsLocalRing R]
    (φ : R →ₐ[k] k) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x)) :
    ∃ E : PowerSeries k ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R,
      ∀ p : MvPolynomial Unit k,
        E (p : MvPowerSeries Unit k) =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R
            (MvPolynomial.aeval (fun _ : Unit => t) p) := by
  let I := MvPolynomial.idealOfVars Unit k
  let J := IsLocalRing.maximalIdeal R
  choose e he using s2v_l1b_parameter_finite_coordinates R φ t ht hreg
  have hc : ∀ {a b : ℕ} (h : a ≤ b) z,
      Ideal.Quotient.factorPow J h (e b z) =
        e a (Ideal.Quotient.factorPow I h z) := by
    intro a b h z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    dsimp only [I, J]
    simp only [he, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  obtain ⟨E, hE⟩ := s2e_adic_coordinates_equiv I J e hc
  refine ⟨(MvPowerSeries.toAdicCompletionAlgEquiv Unit k).toRingEquiv.trans E, ?_⟩
  intro p
  change E (MvPowerSeries.toAdicCompletion Unit k p) = _
  rw [MvPowerSeries.toAdicCompletion_coe]
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [hE, AdicCompletion.evalₐ_of, he, AdicCompletion.evalₐ_of]

/-- In an IsAdicComplete local algebra a regular parameter and its coefficient field
give series coordinates preserving the parameter and all constants. -/
theorem s2v_l1b_complete_parameter_coordinates
    {k : Type*} [Field k] (R : Type*) [CommRing R] [Algebra k R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (φ : R →ₐ[k] k) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x)) :
    ∃ E : PowerSeries k ≃+* R, E PowerSeries.X = t ∧
      ∀ c : k, E (PowerSeries.C c) = algebraMap k R c := by
  obtain ⟨E, hE⟩ := s2v_l1b_parameter_adic_coordinates R φ t ht hreg
  have hX : E PowerSeries.X = AdicCompletion.of (IsLocalRing.maximalIdeal R) R t := by
    simpa only [MvPolynomial.coe_X, MvPolynomial.aeval_X, PowerSeries.X_apply] using hE (MvPolynomial.X ())
  have hC (c : k) : E (PowerSeries.C c) =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R (algebraMap k R c) := by
    simpa only [MvPolynomial.coe_C, MvPolynomial.aeval_C, PowerSeries.C_apply] using hE (MvPolynomial.C c)
  let e := (AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal R)).symm.toRingEquiv
  refine ⟨E.trans e, ?_, ?_⟩
  · change e (E PowerSeries.X) = t
    rw [hX]
    exact AdicCompletion.ofAlgEquiv_symm_of _ t
  · intro c
    change e (E (PowerSeries.C c)) = algebraMap k R c
    rw [hC]
    exact AdicCompletion.ofAlgEquiv_symm_of _ _

end HodgeLean.Foundations.Program
