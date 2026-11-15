import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bRootRemovable
import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bValueCoordinates

noncomputable section
open Filter Manifold
open scoped Topology ContDiff Manifold

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6a_value_root_exponent (r : ((Fin 10 → ℂ) × ℂ) → ℂ)
    (x : (Fin 10 → ℂ) × ℂ) (j k : Fin 13) (m e : ℕ) (hm : 0 < m) (he : 0 < e)
    (hr : ∀ᶠ z in 𝓝 x, ContinuousAt r z) (hz : r x = 0) (hx : x.2 ≠ 0)
    (hv : ∀ᶠ z in 𝓝 x, b6a_value z.1 j (z.2 ^ m) = b6a_value z.1 k (r z ^ e)) :
    e = 1 := by
  have hvx : b6a_value x.1 j (x.2 ^ m) = b6a_value x.1 k 0 := by
    simpa only [hz, zero_pow he.ne'] using hv.self_of_nhds
  have hfinite : ∃ w : ℂ, b6a_value x.1 j (x.2 ^ m) = (w : OnePoint ℂ) := by
    by_cases hj : j.val = 12
    · exact ⟨(x.2 ^ m)⁻¹, by rw [b6a_value_infinite _ _ hj, b4cov_sphInv_coe (pow_ne_zero _ hx)]⟩
    · exact ⟨b6a_valueShift x.1 j + x.2 ^ m, b6a_value_finite _ _ hj _⟩
  have hk : k.val ≠ 12 := by
    intro hk
    obtain ⟨w, hw⟩ := hfinite
    rw [hw, b6a_value_infinite _ _ hk, b4cov_sphInv_zero] at hvx
    exact OnePoint.coe_ne_infty w hvx
  let R : ℂ → ℂ := fun w ↦ r (x.1, w)
  have hs : Continuous (fun w : ℂ ↦ (x.1, w)) := continuous_const.prodMk continuous_id
  have hR : ∀ᶠ w in 𝓝 x.2, ContinuousAt R w := by
    filter_upwards [hs.continuousAt hr] with w hw
    exact hw.comp (f := fun v : ℂ ↦ (x.1, v)) hs.continuousAt
  have hvs : ∀ᶠ w in 𝓝 x.2,
      b6a_value x.1 j (w ^ m) = b6a_value x.1 k (R w ^ e) := hs.continuousAt hv
  have hdne : (m : ℂ) * x.2 ^ (m - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') (pow_ne_zero _ hx)
  by_cases hj : j.val = 12
  · apply b6a_root_exponent_eq_one R (fun w ↦ (w ^ m)⁻¹ - b6a_valueShift x.1 k)
      x.2 (-((m : ℂ) * x.2 ^ (m - 1)) / (x.2 ^ m) ^ 2) e he hR hz
    · exact ((contDiffAt_id.pow m).inv (pow_ne_zero _ hx)).sub contDiffAt_const
    · exact ((hasDerivAt_pow m x.2).inv (pow_ne_zero _ hx)).sub_const _
    · exact div_ne_zero (neg_ne_zero.mpr hdne) (pow_ne_zero _ (pow_ne_zero _ hx))
    · filter_upwards [hvs, continuous_id.continuousAt.eventually_ne hx] with w hw hwne
      change w ≠ 0 at hwne
      rw [b6a_value_infinite _ _ hj, b4cov_sphInv_coe (pow_ne_zero m hwne),
        b6a_value_finite _ _ hk] at hw
      have hh := OnePoint.coe_injective hw
      change R w ^ e = (w ^ m)⁻¹ - b6a_valueShift x.1 k
      linear_combination -hh
  · apply b6a_root_exponent_eq_one R
      (fun w ↦ b6a_valueShift x.1 j + w ^ m - b6a_valueShift x.1 k)
      x.2 ((m : ℂ) * x.2 ^ (m - 1)) e he hR hz
    · fun_prop
    · simpa using (((hasDerivAt_const x.2 (b6a_valueShift x.1 j)).add
        (hasDerivAt_pow m x.2)).sub_const (b6a_valueShift x.1 k))
    · exact hdne
    · filter_upwards [hvs] with w hw
      rw [b6a_value_finite _ _ hj, b6a_value_finite _ _ hk] at hw
      have hh := OnePoint.coe_injective hw
      change R w ^ e = b6a_valueShift x.1 j + w ^ m - b6a_valueShift x.1 k
      linear_combination -hh

end HodgeLean.Foundations.Program
