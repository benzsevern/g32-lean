import HodgeLean.Foundations.Program.CodifferentialDictionaryNormalizationProofs

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b66d_residue_integrand_algebra (e s s₀ C z P R : ℂ) (n : ℕ)
    (he : e ≠ 0) (hs : s ≠ 0) (hs₀ : s₀ ≠ 0) (hC : C ≠ 0)
    (hz : z ≠ 0) (hR : R ≠ 0)
    (hrel : s - s₀ = s * s₀ / C * z ^ n) :
    (e * z ^ (n - 1))⁻¹ *
      ((1 / 4 : ℂ) * P / ((s - s₀) * R) * ((s ^ 2 / C) * (e * z ^ (n - 1))) ^ 2) =
    e * z ^ (n - 1) * ((1 / 4 : ℂ) * s ^ 3 / (C * s₀) * P / R) / z ^ n := by
  rw [hrel]
  field_simp

end HodgeLean.Foundations.Program
