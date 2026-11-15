import HodgeLean.Foundations.Program.HolomorphicODEDefs

noncomputable section

namespace HodgeLean.Foundations.Program

theorem b65_radius_pos {R S M : ℝ} (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M) :
    0 < b65_radius R S M := by
  unfold b65_radius
  exact lt_min (half_pos hR) (div_pos hS (by positivity))

theorem b65_radius_le_half {R S M : ℝ} : b65_radius R S M ≤ R / 2 :=
  min_le_left _ _

theorem b65_radius_displacement_lt {R S M : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hM : 0 ≤ M) :
    b65_radius R S M * M < S / 4 := by
  have hr := b65_radius_pos hR hS hM
  have hd : 0 < 4 * (M + 1) := by positivity
  have hb : b65_radius R S M * (4 * (M + 1)) ≤ S :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  nlinarith

theorem b65_radius_contraction_le {R S M : ℝ} (hS : 0 < S) (hM : 0 ≤ M) :
    b65_radius R S M * (4 * M / S) ≤ M / (M + 1) := by
  have hp : 0 < M + 1 := by positivity
  have hd : 0 < 4 * (M + 1) := by positivity
  have hb : b65_radius R S M * (4 * (M + 1)) ≤ S :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  calc
    b65_radius R S M * (4 * M / S) =
        (b65_radius R S M * (4 * (M + 1)) / S) * (M / (M + 1)) := by
      field_simp
      <;> ring
    _ ≤ 1 * (M / (M + 1)) :=
      mul_le_mul_of_nonneg_right ((div_le_one hS).mpr hb) (div_nonneg hM hp.le)
    _ = M / (M + 1) := one_mul _

theorem b65_radius_contraction_lt_one {R S M : ℝ} (hS : 0 < S) (hM : 0 ≤ M) :
    b65_radius R S M * (4 * M / S) < 1 := by
  refine (b65_radius_contraction_le hS hM).trans_lt ?_
  exact (div_lt_one (by positivity : 0 < M + 1)).mpr (lt_add_one M)

end HodgeLean.Foundations.Program
