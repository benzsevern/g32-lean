import HodgeLean.Foundations.Program.RelativeFrameFamilyBase
import HodgeLean.Foundations.Program.RelativeFrameFamilyTentRoot

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem rf7_tent_preimage (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ)
    (ht : t ∈ b6t_polydisc b) :
    (∀ z : ℂ, (∀ i, b6t_radius b ≤ dist z (b i)) → b6t_plane b t z = z) ∧
      (∀ i : Fin 10, b6t_plane b t (b i) = t i ∧
        MapsTo (b6t_plane b t) (Metric.ball (b i) (b6t_radius b))
          (Metric.ball (b i) (b6t_radius b)) ∧
        ∀ ρ : ℝ, b6t_radius b < ρ → ρ ≤ 3 * b6t_radius b →
          b6t_plane b t ⁻¹' Metric.ball (b i) ρ = Metric.ball (b i) ρ) := by
  classical
  have hr := (b6t_discs b hb).1
  have hsep := (rf7_radius_separation b hb).1
  have hfix (z : ℂ) (hz : ∀ i, b6t_radius b ≤ dist z (b i)) : b6t_plane b t z = z := by
    unfold b6t_plane
    have hh (i) : max 0 (1 - dist z (b i) / b6t_radius b) = 0 := by
      exact max_eq_left (sub_nonpos.mpr ((le_div_iff₀ hr).2 (by simpa using hz i)))
    simp only [hh, zero_smul, Finset.sum_const_zero, add_zero]
  have hlocal (i : Fin 10) (z : ℂ) (hz : dist z (b i) < b6t_radius b) :
      b6t_plane b t z = z + (1 - dist z (b i) / b6t_radius b) • (t i - b i) := by
    rw [b6t_plane, Finset.sum_eq_single i]
    · rw [max_eq_right (sub_nonneg.mpr ((div_le_one hr).2 hz.le))]
    · intro j _ hji
      have hd := dist_triangle (b i) z (b j)
      rw [dist_comm (b i) z] at hd
      have hj := hsep i j (Ne.symm hji)
      have hjz : b6t_radius b ≤ dist z (b j) := by linarith
      rw [max_eq_left (sub_nonpos.mpr ((le_div_iff₀ hr).2 (by simpa using hjz))), zero_smul]
    · simp
  have hmaps (i : Fin 10) : MapsTo (b6t_plane b t)
      (Metric.ball (b i) (b6t_radius b)) (Metric.ball (b i) (b6t_radius b)) := by
    intro z hz
    have hs : 0 < 1 - dist z (b i) / b6t_radius b :=
      sub_pos.mpr ((div_lt_one hr).2 hz)
    have ht' : ‖t i - b i‖ < b6t_radius b := by simpa [Metric.mem_ball, dist_eq_norm] using ht i
    rw [Metric.mem_ball, hlocal i z hz, dist_eq_norm]
    calc
      ‖z + (1 - dist z (b i) / b6t_radius b) • (t i - b i) - b i‖ =
          ‖(z - b i) + (1 - dist z (b i) / b6t_radius b) • (t i - b i)‖ := by congr 1; abel
      _ ≤ ‖z - b i‖ + ‖(1 - dist z (b i) / b6t_radius b) • (t i - b i)‖ := norm_add_le _ _
      _ = dist z (b i) + (1 - dist z (b i) / b6t_radius b) * ‖t i - b i‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, dist_eq_norm]
      _ < dist z (b i) + (1 - dist z (b i) / b6t_radius b) * b6t_radius b := by nlinarith
      _ = b6t_radius b := by field_simp; ring
  refine ⟨hfix, fun i ↦ ⟨?_, hmaps i, ?_⟩⟩
  · rw [hlocal i (b i) (by simpa using hr)]
    simp
  · intro ρ hρ hρmax
    ext z
    change dist (b6t_plane b t z) (b i) < ρ ↔ dist z (b i) < ρ
    by_cases hz : ∃ j, z ∈ Metric.ball (b j) (b6t_radius b)
    · obtain ⟨j, hj⟩ := hz
      have hm := hmaps j hj
      by_cases hji : j = i
      · subst j
        exact ⟨fun _ ↦ lt_trans hj hρ, fun _ ↦ lt_trans hm hρ⟩
      · have hh := hsep i j (Ne.symm hji)
        have hd := dist_triangle (b i) z (b j)
        have hd' := dist_triangle (b i) (b6t_plane b t z) (b j)
        rw [dist_comm (b i) z] at hd
        rw [dist_comm (b i) (b6t_plane b t z)] at hd'
        have hzout : ¬ dist z (b i) < ρ := by change dist z (b j) < _ at hj; linarith
        have hmout : ¬ dist (b6t_plane b t z) (b i) < ρ := by
          change dist (b6t_plane b t z) (b j) < _ at hm
          linarith
        exact iff_of_false hmout hzout
    · have hh : ∀ j, b6t_radius b ≤ dist z (b j) := by
        simpa only [not_exists, Metric.mem_ball, not_lt] using hz
      rw [hfix z hh]


theorem rf7_tent_plane_power (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ)
    (i : Fin 10) (n : ℕ) (u : ℂ) (hu : ‖u‖ ^ n < 3 * b6t_radius b) :
    b6t_plane b t (b i + u ^ n) - t i =
      u ^ n - (rf7_tentCoeff n (b6t_radius b) u : ℂ) * (t i - b i) := by
  classical
  have hr := (b6t_discs b hb).1
  have hsep := (rf7_radius_separation b hb).1
  rw [b6t_plane, Finset.sum_eq_single i]
  · rw [dist_eq_norm, add_sub_cancel_left, norm_pow, Complex.real_smul]
    have hmin : max 0 (1 - ‖u‖ ^ n / b6t_radius b) = 1 - min 1 (‖u‖ ^ n / b6t_radius b) := by
      by_cases h : ‖u‖ ^ n / b6t_radius b ≤ 1
      · rw [max_eq_right (sub_nonneg.mpr h), min_eq_right h]
      · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge h)), min_eq_left (le_of_not_ge h), sub_self]
    rw [hmin]
    simp only [rf7_tentCoeff, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  · intro j _ hji
    have hs := hsep i j hji.symm
    have hd := dist_triangle (b i) (b i + u ^ n) (b j)
    have hdz : dist (b i) (b i + u ^ n) = ‖u‖ ^ n := by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_pow]
    rw [hdz] at hd
    have hdist : b6t_radius b ≤ dist (b i + u ^ n) (b j) := by linarith
    rw [max_eq_left (sub_nonpos.mpr ((le_div_iff₀ hr).mpr (by simpa using hdist))), zero_smul]
  · simp

end HodgeLean.Foundations.Program
