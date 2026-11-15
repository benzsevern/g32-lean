import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The order of an actual uniformizer in arbitrary formal coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- Any formal coordinate isomorphism sends a completed actual DVR
uniformizer to a series of order one. No value for that coordinate is assumed. -/
theorem s2e_c1_completed_parameter_order
    {k R : Type*} [Field k] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (t : R) (ht : Irreducible t)
    (E : PowerSeries k ≃+* AdicCompletion (IsLocalRing.maximalIdeal R) R) :
    (E.symm (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) t)).order = 1 := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have hspan : Ideal.span {algebraMap R C t} = IsLocalRing.maximalIdeal C := by
    calc
      Ideal.span {algebraMap R C t} = Ideal.map (algebraMap R C) (Ideal.span {t}) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap R C) (IsLocalRing.maximalIdeal R) :=
        (congrArg (Ideal.map (algebraMap R C)) ht.maximalIdeal_eq).symm
      _ = IsLocalRing.maximalIdeal C := AdicCompletion.maximalIdeal_eq_map.symm
  have he := congrArg (fun I : Ideal C => Ideal.map E.symm.toRingHom I) hspan
  rw [Ideal.map_span, Set.image_singleton,
    IsLocalRing.map_maximalIdeal_of_surjective E.symm.toRingHom E.symm.surjective,
    PowerSeries.maximalIdeal_eq_span_X] at he
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he
  have ho := congrArg PowerSeries.order hu
  rw [PowerSeries.order_mul, PowerSeries.order_zero_of_isUnit u.isUnit, add_zero,
    PowerSeries.order_X] at ho
  exact ho

end HodgeLean.Foundations.Program
