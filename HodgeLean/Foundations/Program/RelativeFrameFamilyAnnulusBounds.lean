import HodgeLean.Foundations.Program.RelativeFrameFamilyGeometry

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

/-- A translated offset in a separated marked disc avoids every smaller marked disc.
Source: `rf7_radius_separation`, the triangle inequality. -/
theorem rf7_offset_avoids {b : Fin 10 → ℂ} (hb : b ∈ b6_chart)
    (i : Fin 10) (v : ℂ) (R : ℝ) (hR : R ≤ 3 * b6t_radius b)
    (hlo : R < ‖v‖) (hhi : ‖v‖ ≤ 3 * b6t_radius b) :
    ∀ j, R < dist (b i + v) (b j) := by
  intro j
  by_cases hij : i = j
  · subst j
    simpa [dist_eq_norm] using hlo
  · have hs := (rf7_radius_separation b hb).1 i j hij
    have ht := dist_triangle (b i) (b i + v) (b j)
    have hd : dist (b i) (b i + v) = ‖v‖ := by rw [dist_comm]; simp [dist_eq_norm]
    rw [hd] at ht
    have hr := (b6t_discs b hb).1
    linarith

end HodgeLean.Foundations.Program
