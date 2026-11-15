import HodgeLean.Foundations.Program.PrymParabolicIntersectionWedge

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

/-- Inverse coordinates for the centred finite wedge.
Source: solving the real and imaginary equations in `hga_wedgeDeformation`. -/
def hga_wedgeInverse (u v : ℝ) (z : ℂ) : ℂ :=
  (((z.re + (u + 11 / 2) * |z.im / 10|) / (v - u) : ℝ) : ℂ) +
    (((-z.im / 10 - (z.re + (u + 11 / 2) * |z.im / 10|) / (v - u)) / 2 : ℝ) : ℂ) *
      Complex.I

theorem hga_wedgeDeformation_inverse (u v : ℝ) (huv : u < v) (z : ℂ) :
    hga_wedgeDeformation u v 1 (hga_wedgeInverse u v z) = z := by
  have hv : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
  have hs : (hga_wedgeInverse u v z).re + 2 * (hga_wedgeInverse u v z).im =
      -z.im / 10 := by
    simp only [hga_wedgeInverse, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add]
    ring
  apply Complex.ext
  · simp only [hga_wedgeDeformation, sub_self, zero_add, one_mul, one_add_one_eq_two,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
    rw [hs]
    simp only [hga_wedgeInverse, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      neg_div, abs_neg]
    field_simp
    <;> ring
  · simp only [hga_wedgeDeformation, sub_self, zero_add, one_mul, one_add_one_eq_two,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
    rw [hs]
    ring

theorem hga_wedgeInverse_deformation (u v : ℝ) (huv : u < v) (z : ℂ) :
    hga_wedgeInverse u v (hga_wedgeDeformation u v 1 z) = z := by
  have hv : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
  have hr : (hga_wedgeDeformation u v 1 z).re =
      (v - u) * z.re - (u + 11 / 2) * |z.re + 2 * z.im| := by
    norm_num [hga_wedgeDeformation]
  have hi : (hga_wedgeDeformation u v 1 z).im / 10 = -(z.re + 2 * z.im) := by
    norm_num [hga_wedgeDeformation]
    ring
  apply Complex.ext <;>
    simp only [hga_wedgeInverse, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, neg_div, hr, hi, abs_neg]
  · field_simp
    <;> ring
  · field_simp
    <;> ring

/-- The centred wedge coordinates as a homeomorphism of the complex plane.
Source: `hga_wedgeDeformation_inverse`, `hga_wedgeInverse_deformation`. -/
def hga_wedgeHomeomorph (u v : ℝ) (huv : u < v) : ℂ ≃ₜ ℂ where
  toFun := hga_wedgeDeformation u v 1
  invFun := hga_wedgeInverse u v
  left_inv := hga_wedgeInverse_deformation u v huv
  right_inv := hga_wedgeDeformation_inverse u v huv
  continuous_toFun := (hga_continuous_wedgeDeformation u v).comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := by unfold hga_wedgeInverse; fun_prop

open scoped Topology in
theorem hga_wedgeInverse_local_parametrization (u v : ℝ) (huv : u < v) :
    ∀ᶠ z : ℂ in 𝓝 0, hg5_wedge u v (hga_triangleRetraction (hga_wedgeInverse u v z)) =
      z + hg5_wedge u v (hga_triangleRetraction 0) := by
  have hzero : hga_wedgeInverse u v 0 = 0 := by simp [hga_wedgeInverse]
  have ht : Filter.Tendsto (hga_wedgeInverse u v) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (hga_wedgeInverse u v) :=
      (hga_wedgeHomeomorph u v huv).continuous_invFun
    simpa only [hzero] using hc.tendsto 0
  filter_upwards [ht.eventually (hga_wedgeExtension_eventually u v)] with z hz
  change hg5_wedge u v (hga_triangleRetraction (hga_wedgeInverse u v z)) =
    hga_wedgeDeformation u v 1 (hga_wedgeInverse u v z) +
      hg5_wedge u v (hga_triangleRetraction 0) at hz
  rwa [hga_wedgeDeformation_inverse u v huv] at hz

#print axioms hga_wedgeInverse_local_parametrization

#print axioms hga_wedgeHomeomorph

#print axioms hga_wedgeInverse_deformation

#print axioms hga_wedgeInverse
#print axioms hga_wedgeDeformation_inverse
end HodgeLean.Foundations.Program
