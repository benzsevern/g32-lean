import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCoordinatePrime

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every coordinate other than the inserted one remains dominant on the coordinate fibre. -/
theorem s2v_l1b_divisor_coordinate_fibre_projection_dominant
    (Z : Over (Spec ↧ℂ)) [LocallyOfFiniteType Z.hom]
    (n : ℕ) (b : ComplexPoint Z) (i j : Fin (n + 1)) (hji : j ≠ i) :
    IsDominant ((s2c_branchInsertion Z n b ≫
      s2_permute Z (n + 1) (Equiv.swap 0 i) ≫ g3_proj Z (n + 1) j).left) := by
  classical
  have h0 : (Equiv.swap 0 i) j ≠ 0 := by
    intro H
    exact hji ((Equiv.swap 0 i).injective (H.trans (Equiv.swap_apply_right 0 i).symm))
  obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr h0
  have he : s2c_branchInsertion Z n b ≫
      s2_permute Z (n + 1) (Equiv.swap 0 i) ≫ g3_proj Z (n + 1) j =
        g3_proj Z n k := by
    simp only [s2_permute, s2_check_lift_proj, Equiv.symm_swap, ← hk]
    change s2c_branchInsertion Z n b ≫ g3_proj Z (n + 1) k.succ = _
    simp only [s2c_branchInsertion, s2_check_lift_proj]
    rfl
  rw [he]
  exact s2v_l1b_divisor_projection_dominant Z n k

end HodgeLean.Foundations.Program
