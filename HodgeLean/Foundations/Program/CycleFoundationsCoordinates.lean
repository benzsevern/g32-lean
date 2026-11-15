import HodgeLean.Foundations.Program.CycleFoundationsDefs

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Two rational coordinates on one vector space differ by a nonzero scalar. -/
theorem cfd_top_coordinate_rescale {V : Type*} [AddCommGroup V] [Module ℚ V]
    (I J : V ≃ₗ[ℚ] ℚ) :
    ∃ r : ℚ, r ≠ 0 ∧ I.toLinearMap = r • J.toLinearMap := by
  refine ⟨I (J.symm 1), ?_, ?_⟩
  · intro h
    have hz : J.symm 1 = 0 := I.injective (h.trans I.map_zero.symm)
    have he := J.apply_symm_apply (1 : ℚ)
    rw [hz, map_zero] at he
    exact one_ne_zero he.symm
  · ext v
    have hv : v = J v • J.symm 1 := by
      apply J.injective
      rw [map_smul, J.apply_symm_apply, smul_eq_mul, mul_one]
    change I v = I (J.symm 1) • J v
    rw [hv, map_smul]
    change J v * I (J.symm 1) = I (J.symm 1) * J (J v • J.symm 1)
    rw [map_smul, J.apply_symm_apply, smul_eq_mul, mul_one, mul_comm]

/-- Changing the top coordinate rescales the Künneth projection. -/
theorem cfd_projection_coordinate_rescale
    (A B : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d n : ℕ) (I J : HQ B (2 * d) ≃ₗ[ℚ] ℚ) :
    ∃ r : ℚ, r ≠ 0 ∧ cfd_projection A B d I n = r • cfd_projection A B d J n := by
  obtain ⟨r, hr, hIJ⟩ := cfd_top_coordinate_rescale I J
  refine ⟨r, hr, ?_⟩
  unfold cfd_projection
  rw [hIJ, TensorProduct.map_smul_right]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

end HodgeLean.Foundations.Program
