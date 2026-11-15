import HodgeLean.Foundations.Program.CodifferentialDictionaryResidueAlgebraProofs

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.Program

theorem b66d_normalized_power_residue {a b s₀ : ℂ} {n : ℕ} {J : ℂ → ℂ}
    (hab : a * b ≠ 0) (hba : b - a ≠ 0) (hs₀ : s₀ ≠ 0)
    (hn : 0 < n) (hJ : AnalyticAt ℂ J s₀) :
    TauCeti.Contour.residue (fun z : ℂ =>
      ((n : ℂ) * z ^ (n - 1))⁻¹ *
        ((1 / 4 : ℂ) * J (b66d_inverseNormalize a b (b65s_normalize a b s₀ + z ^ n)) /
          (b66d_inverseNormalize a b (b65s_normalize a b s₀ + z ^ n) - s₀) *
          ((b66d_inverseNormalize a b (b65s_normalize a b s₀ + z ^ n)) ^ 2 /
            (a * b / (b - a)) * ((n : ℂ) * z ^ (n - 1))) ^ 2)) 0 =
      (n : ℂ) * ((1 / 4 : ℂ) * s₀ ^ 2 / (a * b / (b - a)) * J s₀) := by
  let w₀ := b65s_normalize a b s₀
  let C := a * b / (b - a)
  let S := b66d_inverseNormalize a b
  have hC : C ≠ 0 := div_ne_zero hab hba
  have hcenter : S w₀ = s₀ := b66d_inverseNormalize_center hab hba hs₀
  have hden : b - w₀ * (b - a) ≠ 0 := by
    intro h
    have hz : S w₀ = 0 := by simp [S, b66d_inverseNormalize, h]
    exact hs₀ (hcenter.symm.trans hz)
  have hS : AnalyticAt ℂ S w₀ := by
    apply analyticAt_const.div
    · fun_prop
    · exact hden
  have hJS : AnalyticAt ℂ (fun w => J (S w)) w₀ := by
    apply AnalyticAt.comp _ hS
    simpa only [hcenter] using hJ
  let H : ℂ → ℂ := fun w => (1 / 4 : ℂ) * S w ^ 3 / (C * s₀) * J (S w)
  have hH : AnalyticAt ℂ H w₀ := by
    exact ((analyticAt_const.mul (hS.pow 3)).div_const (c := C * s₀)).mul hJS
  have hw : Tendsto (fun z : ℂ => w₀ + z ^ n) (𝓝 0) (𝓝 w₀) := by
    have hc : ContinuousAt (fun z : ℂ => w₀ + z ^ n) 0 := by fun_prop
    have ht := hc.tendsto
    simpa only [zero_pow (Nat.ne_of_gt hn), add_zero] using ht
  have hdenNear : ∀ᶠ z : ℂ in 𝓝 0, b - (w₀ + z ^ n) * (b - a) ≠ 0 :=
    (show ContinuousAt (fun w : ℂ => b - w * (b - a)) w₀ by fun_prop).tendsto.comp hw |>.eventually (eventually_ne_nhds hden)
  have hsNear : ∀ᶠ z : ℂ in 𝓝 0, S (w₀ + z ^ n) ≠ 0 :=
    (hS.continuousAt.tendsto.comp hw).eventually (eventually_ne_nhds (hcenter ▸ hs₀))
  have heq : (fun z : ℂ => ((n : ℂ) * z ^ (n - 1))⁻¹ *
      ((1 / 4 : ℂ) * J (S (w₀ + z ^ n)) / (S (w₀ + z ^ n) - s₀) *
        (S (w₀ + z ^ n) ^ 2 / C * ((n : ℂ) * z ^ (n - 1))) ^ 2)) =ᶠ[𝓝[≠] 0]
      (fun z : ℂ => (n : ℂ) * z ^ (n - 1) * H (w₀ + z ^ n) / z ^ n) := by
    filter_upwards [hdenNear.filter_mono nhdsWithin_le_nhds,
      hsNear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hd hs hz
    have hz' : z ≠ 0 := hz
    have hrel : S (w₀ + z ^ n) - s₀ = S (w₀ + z ^ n) * s₀ / C * z ^ n := by
      simpa only [w₀, add_sub_cancel_left] using
        b66d_inverseNormalize_difference hab hba hs₀ hd
    simpa only [H, mul_one, div_one] using
      b66d_residue_integrand_algebra (n : ℂ) (S (w₀ + z ^ n)) s₀ C z
        (J (S (w₀ + z ^ n))) 1 n (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
        hs hs₀ hC hz' one_ne_zero hrel
  change TauCeti.Contour.residue _ 0 = _
  rw [TauCeti.Contour.residue_congr_nhdsNE heq, b66d_residue_power_simple hn hH]
  dsimp [H]
  rw [hcenter]
  dsimp [C]
  field_simp

end HodgeLean.Foundations.Program
