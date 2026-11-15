import HodgeLean.Foundations.Program.SchoenTowerFoundB2b
import HodgeLean.Foundations.Program.SchoenCycleCartierLocalization
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- On an actual Rees fraction chart of an integral base, a nonzero selected
centre section generates a free rank-one image ideal.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `IsLocalization.injective`. -/
theorem s2v_i2a_rees_chart_cartier_image
    (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (x : R)
    (hxI : x ∈ I) (hx : x ≠ 0) :
    Nonempty ((I.map (algebraMap R (s2t_reesChart I x))) ≃ₗ[s2t_reesChart I x]
      s2t_reesChart I x) := by
  letI : IsDomain (Localization.Away x) := Localization.Away.isDomain hx
  have hinj : Function.Injective (algebraMap R (Localization.Away x)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  have hxc : algebraMap R (s2t_reesChart I x) x ≠ 0 := by
    intro H
    have h := congrArg Subtype.val H
    exact hx (hinj (h.trans (map_zero _).symm))
  rw [s2t_reesChart_image R I x hxI]
  exact s2e_regular_principal_ideal_free _ (fun _ _ h => mul_right_cancel₀ hxc h)

end HodgeLean.Foundations.Program
