import HodgeLean.Foundations.Program.RelativeFrameFamilyMovingAnalytic

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The radial coefficient in the centred tent displacement after subtracting the moving mark.
Source: `b6t_plane`, `max_min_distrib_left`. -/
def rf7_tentCoeff (n : ℕ) (r : ℝ) (u : ℂ) : ℝ := min 1 (‖u‖ ^ n / r)

example (n : ℕ) (r : ℝ) (hn : 0 < n) : rf7_tentCoeff n r 0 = 0 := by
  simp [rf7_tentCoeff, zero_pow hn.ne']

/-- The principal root lift of the centred radial tent displacement.
Source: `b6a_movingRoot`, `rf4_rootMap`, and `b6t_plane`. -/
def rf7_tentRoot (n : ℕ) (r : ℝ) (ε u : ℂ) : ℂ :=
  u * (1 - (rf7_tentCoeff n r u : ℂ) * ε / u ^ n) ^ ((n : ℂ)⁻¹)

example (n : ℕ) (r : ℝ) (u : ℂ) : rf7_tentRoot n r 0 u = u := by
  simp [rf7_tentRoot]


theorem rf7_tentRoot_pow (n : ℕ) (hn : 0 < n) (r : ℝ) (ε u : ℂ) :
    rf7_tentRoot n r ε u ^ n = u ^ n - (rf7_tentCoeff n r u : ℂ) * ε := by
  by_cases hu : u = 0
  · subst u
    simp [rf7_tentRoot, rf7_tentCoeff, zero_pow hn.ne']
  · rw [rf7_tentRoot, mul_pow, Complex.cpow_nat_inv_pow _ hn.ne']
    field_simp


theorem rf7_tentRoot_perturbation_norm_lt_one (n : ℕ) (r : ℝ) (hr : 0 < r)
    (ε : ℂ) (hε : ‖ε‖ < r) (u : ℂ) (hu : u ≠ 0) :
    ‖(rf7_tentCoeff n r u : ℂ) * ε / u ^ n‖ < 1 := by
  have hA0 : 0 ≤ rf7_tentCoeff n r u :=
    le_min zero_le_one (div_nonneg (pow_nonneg (norm_nonneg u) n) hr.le)
  have hA : rf7_tentCoeff n r u ≤ ‖u‖ ^ n / r := min_le_right _ _
  have huN : 0 < ‖u‖ ^ n := pow_pos (norm_pos_iff.mpr hu) n
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA0, norm_pow]
  apply (div_lt_one huN).mpr
  apply (mul_le_mul_of_nonneg_right hA (norm_nonneg ε)).trans_lt
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hr).mpr
  nlinarith


theorem rf7_tentRoot_continuous (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    Continuous (fun p : {ε : ℂ // ‖ε‖ < r} × ℂ ↦ rf7_tentRoot n r p.1.val p.2) := by
  have hA : Continuous (fun p : {ε : ℂ // ‖ε‖ < r} × ℂ ↦ rf7_tentCoeff n r p.2) :=
    continuous_const.min ((continuous_snd.norm.pow n).div_const r)
  have hp : Continuous (fun p : {ε : ℂ // ‖ε‖ < r} × ℂ ↦
      rf7_tentRoot n r p.1.val p.2 ^ n) := by
    have heq : (fun p : {ε : ℂ // ‖ε‖ < r} × ℂ ↦ rf7_tentRoot n r p.1.val p.2 ^ n) =
        (fun p ↦ p.2 ^ n - (rf7_tentCoeff n r p.2 : ℂ) * p.1.val) := by
      funext p
      exact rf7_tentRoot_pow n hn r p.1.val p.2
    rw [heq]
    exact (continuous_snd.pow n).sub ((Complex.continuous_ofReal.comp hA).mul
      (continuous_subtype_val.comp continuous_fst))
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hu : p.2 = 0
  · apply rf7_continuousAt_zero_of_pow _ n hn p
    · simp [rf7_tentRoot, hu]
    · exact hp.continuousAt
  · have hfactor : ContinuousAt
        (fun p : {ε : ℂ // ‖ε‖ < r} × ℂ ↦ 1 - (rf7_tentCoeff n r p.2 : ℂ) * p.1.val / p.2 ^ n) p :=
      continuousAt_const.sub (((Complex.continuous_ofReal.comp hA).continuousAt.mul
        (continuous_subtype_val.comp continuous_fst).continuousAt).div
        (continuous_snd.pow n).continuousAt (pow_ne_zero n hu))
    have hs : 1 - (rf7_tentCoeff n r p.2 : ℂ) * p.1.val / p.2 ^ n ∈ Complex.slitPlane := by
      have hs := rf7_tentRoot_perturbation_norm_lt_one n r hr p.1.val p.1.2 p.2 hu
      have hs' : ‖-((rf7_tentCoeff n r p.2 : ℂ) * p.1.val / p.2 ^ n)‖ < 1 := by
        rwa [norm_neg]
      convert Complex.mem_slitPlane_of_norm_lt_one hs' using 1 <;> ring
    exact continuous_snd.continuousAt.mul (hfactor.cpow continuousAt_const hs)


theorem rf7_tentRoot_collar (n : ℕ) (r : ℝ) (hr : 0 < r) (ε u : ℂ)
    (hu : r ≤ ‖u‖ ^ n) : rf7_tentRoot n r ε u = rf4_rootMap n ε u := by
  have hA : rf7_tentCoeff n r u = 1 := min_eq_left ((le_div_iff₀ hr).mpr (by simpa using hu))
  simp only [rf7_tentRoot, hA, Complex.ofReal_one, one_mul, rf4_rootMap,
    zpow_neg, zpow_natCast, div_eq_mul_inv]


theorem rf7_tentRoot_mul (n : ℕ) (r : ℝ) (ε u ζ : ℂ) (hζ : ζ ^ n = 1) :
    rf7_tentRoot n r ε (ζ * u) = ζ * rf7_tentRoot n r ε u := by
  have hp : (ζ * u) ^ n = u ^ n := by rw [mul_pow, hζ, one_mul]
  have hA : rf7_tentCoeff n r (ζ * u) = rf7_tentCoeff n r u := by
    unfold rf7_tentCoeff
    rw [← norm_pow, hp, norm_pow]
  simp only [rf7_tentRoot, hA, hp]
  ring


theorem rf7_tentRoot_injective_on_power_fibre (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r)
    (ε : ℂ) (hε : ‖ε‖ < r) (u v : ℂ) (hp : u ^ n = v ^ n)
    (heq : rf7_tentRoot n r ε u = rf7_tentRoot n r ε v) : u = v := by
  by_cases hu : u = 0
  · subst u
    have hv : v = 0 := (pow_eq_zero_iff hn.ne').mp (by simpa [zero_pow hn.ne'] using hp.symm)
    exact hv.symm
  · have hA : rf7_tentCoeff n r v = rf7_tentCoeff n r u := by
      unfold rf7_tentCoeff
      rw [← norm_pow, ← hp, norm_pow]
    have hbase : 1 - (rf7_tentCoeff n r u : ℂ) * ε / u ^ n ≠ 0 := by
      intro h
      have he : (rf7_tentCoeff n r u : ℂ) * ε / u ^ n = 1 := (sub_eq_zero.mp h).symm
      have hs := rf7_tentRoot_perturbation_norm_lt_one n r hr ε hε u hu
      rw [he, norm_one] at hs
      exact lt_irrefl 1 hs
    have hfactor : (1 - (rf7_tentCoeff n r u : ℂ) * ε / u ^ n) ^ ((n : ℂ)⁻¹) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
    simp only [rf7_tentRoot, hA, ← hp] at heq
    exact mul_right_cancel₀ hfactor heq

end HodgeLean.Foundations.Program
