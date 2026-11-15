import HodgeLean.Foundations.Program.MilneTensorCoordinateGeneration
import HodgeLean.Foundations.Program.MilneTensorSymmetricPolynomial
import HodgeLean.Foundations.Program.MilneTensorMatrixSign

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_standard_orthogonal_generation (d r n : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin') n =
      m1b_products (m1b_fixed
        (m1b_copies r '' m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin') 2) n := by
  have hB : (1 : Matrix (Fin d) (Fin d) ℂ).toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by simp)
  apply m1b_coordinate_generation_of_orbit_polynomials 1 (by norm_num) _ hB
  · exact m1b_matrixForm_transpose_sign 1 1 (by simp)
  · intro Q hQ hs
    apply m1b_symmetric_forms_same_orbit _ _ hB
      (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hQ)
    · exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr (by simp)).eq
    · have hsym : Q.IsSymm := by
        change Q.transpose = Q
        simpa only [one_smul] using hs
      exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr hsym).eq
  · intro m f hf
    exact m1b_standard_symmetric_orbit_polynomial d 1 m f hf

end HodgeLean.Foundations.Program
