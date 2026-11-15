import HodgeLean.Foundations.Program.SchoenTowerL1bCharZeroCoefficients
import HodgeLean.Foundations.Program.SchoenTowerL1bAdicParameter
import HodgeLean.Foundations.Program.SchoenTowerL1bParameterAdicCoordinates
import Mathlib.RingTheory.AdicCompletion.Noetherian

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A principal regular local domain over a characteristic-zero field embeds in series
over its residue field, preserving the parameter and the base scalars. -/
theorem s2v_l1b_dvr_series_expansion
    {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] [Algebra k R]
    (p : R) (hp : IsLocalRing.maximalIdeal R = Ideal.span {p})
    (hreg : Function.Injective (fun x : R => p * x)) :
    ∃ j : R →+* PowerSeries (IsLocalRing.ResidueField R),
      Function.Injective j ∧ j p = PowerSeries.X ∧
      ∀ c : k, j (algebraMap k R c) =
        PowerSeries.C (algebraMap k (IsLocalRing.ResidueField R) c) := by
  let I := IsLocalRing.maximalIdeal R
  let A := AdicCompletion I R
  let K := IsLocalRing.ResidueField R
  obtain ⟨σ, hσinj, hσ⟩ := s2v_l1b_charZero_residue_field_section (k := k) (R := R)
  letI : Algebra K A := σ.toRingHom.toAlgebra
  let φ : A →ₐ[K] K :=
    { toRingHom := (AdicCompletion.evalOneₐ I).toRingHom
      commutes' := fun c => congrArg (fun f => f c) hσ }
  have hmax : IsLocalRing.maximalIdeal A =
      I.map (algebraMap R A) := AdicCompletion.maximalIdeal_eq_map
  have hparam : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap R A p} := by
    rw [hmax]
    change (IsLocalRing.maximalIdeal R).map (algebraMap R A) = _
    rw [hp, Ideal.map_span, Set.image_singleton]
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    rw [hmax]
    exact AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  obtain ⟨E, hEX, hEC⟩ := s2v_l1b_complete_parameter_coordinates A φ
    (algebraMap R A p) hparam (s2v_l1b_adic_parameter_regular I p hreg)
  let j : R →+* PowerSeries K := E.symm.toRingHom.comp (algebraMap R A)
  refine ⟨j, E.symm.injective.comp (AdicCompletion.of_injective I R), ?_, ?_⟩
  · change E.symm (algebraMap R A p) = PowerSeries.X
    rw [← hEX, E.symm_apply_apply]
  · intro c
    apply E.injective
    change E (E.symm (algebraMap R A (algebraMap k R c))) =
      E (PowerSeries.C (algebraMap k K c))
    rw [E.apply_symm_apply, hEC]
    exact (σ.commutes c).symm

end HodgeLean.Foundations.Program
