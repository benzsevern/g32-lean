import HodgeLean.Foundations.Program.SchoenTowerL1bSeriesRoots
import HodgeLean.Foundations.Program.SchoenTowerL1bTameSeriesAction
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- After ramified substitution, the order identity gives a binomial root
fraction with specified numerator and denominator rescaling characters. -/
theorem s2v_l1b_tame_binomial_fraction
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (A B : PowerSeries K) (hA : A ≠ 0) (hB : B ≠ 0)
    (m e r s : ℕ) (hm : m ≠ 0) (he : e ≠ 0)
    (horders : r * m + e * B.order.toNat = e * A.order.toNat + s * m) :
    ∃ F G : PowerSeries K, F ≠ 0 ∧ G ≠ 0 ∧
      F ^ m * PowerSeries.expand e he B = PowerSeries.expand e he A * G ^ m ∧
      ∀ ζ : K, ζ ^ e = 1 →
        PowerSeries.rescale ζ F = PowerSeries.C (ζ ^ r) * F ∧
        PowerSeries.rescale ζ G = PowerSeries.C (ζ ^ s) * G := by
  obtain ⟨U, hU, hUA⟩ := s2v_l1b_series_monomial_root_factor A hA m hm
  obtain ⟨V, hV, hVB⟩ := s2v_l1b_series_monomial_root_factor B hB m hm
  let W := PowerSeries.expand e he U
  let Z := PowerSeries.expand e he V
  have hW : W ≠ 0 := by
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    change (PowerSeries.expand e he U).constantCoeff = (0 : PowerSeries K).constantCoeff at hh
    rw [PowerSeries.constantCoeff_expand, map_zero] at hh
    exact hU hh
  have hZ : Z ≠ 0 := by
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    change (PowerSeries.expand e he V).constantCoeff = (0 : PowerSeries K).constantCoeff at hh
    rw [PowerSeries.constantCoeff_expand, map_zero] at hh
    exact hV hh
  let F := PowerSeries.X ^ r * W
  let G := PowerSeries.X ^ s * Z
  refine ⟨F, G, mul_ne_zero (pow_ne_zero r PowerSeries.X_ne_zero) hW,
    mul_ne_zero (pow_ne_zero s PowerSeries.X_ne_zero) hZ, ?_, ?_⟩
  · change (PowerSeries.X ^ r * W) ^ m * PowerSeries.expand e he B =
      PowerSeries.expand e he A * (PowerSeries.X ^ s * Z) ^ m
    rw [hUA, hVB]
    simp only [map_mul, map_pow, PowerSeries.expand_X, mul_pow, ← pow_mul]
    change PowerSeries.X ^ (r * m) * W ^ m *
        (PowerSeries.X ^ (e * B.order.toNat) * Z ^ m) =
      (PowerSeries.X ^ (e * A.order.toNat) * W ^ m) *
        (PowerSeries.X ^ (s * m) * Z ^ m)
    calc
      _ = PowerSeries.X ^ (r * m + e * B.order.toNat) * (W ^ m * Z ^ m) := by
        rw [pow_add]
        ring
      _ = PowerSeries.X ^ (e * A.order.toNat + s * m) * (W ^ m * Z ^ m) := by rw [horders]
      _ = _ := by rw [pow_add]; ring
  · intro ζ hζ
    exact ⟨s2v_l1b_rescale_expanded_monomial e he ζ hζ U r,
      s2v_l1b_rescale_expanded_monomial e he ζ hζ V s⟩

end HodgeLean.Foundations.Program
