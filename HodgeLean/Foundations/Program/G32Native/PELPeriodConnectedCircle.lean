import HodgeLean.Foundations.Program.G32Native.PELIsometryCircle
import HodgeLean.Foundations.Program.G32Native.PELPeriodScalarChecks

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- A period complex structure belongs to the identity component by its
explicit circle, independently of any general-member identification.
Source: `pel_complex_structure_mem_component`. -/
theorem pelPeriodMatrix_mem_component (R : PELSplitReference) (z : PELSplitDomain R) :
    pelPeriodMatrix R z ∈ g1_identityComponent
      (pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
        (Set.range fun i : Fin 4 =>
          (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
            (algebraMap ℚ ℂ))) := by
  let J := z.J.map (algebraMap ℝ ℂ)
  have hJ : J * J = -1 := by
    rw [← Matrix.map_mul, z.square, Matrix.map_neg, Matrix.map_one] <;> simp
  have hmap (M : Matrix (Fin 12) (Fin 12) ℚ) :
      (M.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) = M.map (algebraMap ℚ ℂ) := by
    ext i j
    simp only [Matrix.map_apply, ← IsScalarTower.algebraMap_apply ℚ ℝ ℂ]
  have hΩ : J.transpose * R.form.map (algebraMap ℚ ℂ) * J =
      R.form.map (algebraMap ℚ ℂ) := by
    have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℝ =>
      M.map (algebraMap ℝ ℂ)) z.isometry
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmap, J] using h
  have hc : ∀ T ∈ (Set.range fun i : Fin 4 =>
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
        (algebraMap ℚ ℂ)), J * T = T * J := by
    rintro T ⟨i, rfl⟩
    have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) ℝ =>
      M.map (algebraMap ℝ ℂ))
        (z.commute (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))
    simpa only [Matrix.map_mul, hmap] using h
  have h := pel_complex_structure_mem_component J _ _ hJ hΩ hc
  have he : pelCircleUnit J hJ (Real.pi / 2) = pelPeriodMatrix R z := by
    apply Units.ext
    simp only [pelCircleUnit, pelCircleMatrix, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul, zero_add]
    rfl
  rwa [he] at h

#print axioms pelPeriodMatrix_mem_component
end HodgeLean.Foundations.Program.GeneralTypeIII
