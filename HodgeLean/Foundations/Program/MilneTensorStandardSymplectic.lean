import HodgeLean.Foundations.Program.MilneTensorCoordinateGeneration
import HodgeLean.Foundations.Program.MilneTensorSymplecticPolynomial
import HodgeLean.Foundations.Program.MilneTensorMatrixSign

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_standard_symplectic_generation (d r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries (m1b_J d).toBilin') n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries (m1b_J d).toBilin') 2) n := by
  apply m1b_coordinate_generation_of_orbit_polynomials (-1) (by norm_num) _
    (m1b_standard_symplectic_nondegenerate d)
  · intro x y
    simpa only [neg_one_mul] using
      (LinearMap.BilinForm.IsAlt.neg_eq (m1b_standard_symplectic_alternating d) x y).symm
  · intro Q hQ hs
    apply m1b_alternating_forms_same_orbit _ _ (m1b_standard_symplectic_nondegenerate d)
      (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hQ)
      (m1b_standard_symplectic_alternating d)
    intro x
    have h := m1b_matrixForm_transpose_sign (-1) Q hs x x
    linear_combination (1 / 2 : ℂ) * h
  · intro m f hf
    exact m1b_standard_symplectic_orbit_polynomial d 1 m f hf

end HodgeLean.Foundations.Program
