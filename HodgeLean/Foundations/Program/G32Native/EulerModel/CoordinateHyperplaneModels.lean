import HodgeLean.Foundations.Program.G32Native.EulerModel.Hyperplane

/-! # The actual projective models of every specified residue-coordinate hyperplane -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Every specified residue-coordinate hyperplane retains the actual projective model of dimension one less. -/
theorem residue_hyperplane_projective_model (k : ℕ) (hk : 0 < k) (j : Fin (k + 1)) :
    Nonempty (s2c_subscheme
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_s2b_residueIdeal k j) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))) := by
  classical
  have hI : s2e_s2b_residueIdeal k j = s2e_s2b_intersectionIdeal k {j} := by
    simp only [s2e_s2b_intersectionIdeal, Finset.mem_singleton, iSup_iSup_eq_left]
  rw [hI]
  have E := s2e_coordinate_intersection_over k {j}
    (by simp only [Finset.card_singleton]; omega)
  have hcard : ({j} : Finset (Fin (k + 1))).card = 1 := Finset.card_singleton _
  rw [hcard] at E
  exact E

#print axioms residue_hyperplane_projective_model
end HodgeLean.Foundations.Program.G32Native.EulerModel
