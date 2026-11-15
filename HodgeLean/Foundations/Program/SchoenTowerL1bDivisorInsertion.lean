import HodgeLean.Foundations.Program.SchoenTowerL1aBranchInsertionKernel
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Marked insertion is a closed immersion for every separated complex curve model. -/
theorem s2v_l1b_divisor_insertion_closedImmersion
    (Z : Over (Spec ↧ℂ)) [IsSeparated Z.hom] (n : ℕ) (b : ComplexPoint Z) :
    IsClosedImmersion (s2c_branchInsertion Z n b).left := by
  let d := pullback.snd Z.hom (g3_power Z n).hom
  letI : IsSeparated d := inferInstanceAs (IsSeparated (pullback.snd Z.hom (g3_power Z n).hom))
  haveI : IsClosedImmersion ((s2c_branchInsertion Z n b).left ≫ d) := by
    rw [s2v_l1a_branchInsertion_snd]
    infer_instance
  exact IsClosedImmersion.of_comp (s2c_branchInsertion Z n b).left d

/-- Moving the inserted coordinate identifies every coordinate fibre with the shorter ordered power. -/
theorem s2v_l1b_divisor_coordinate_insertion_isPullback
    (Z : Over (Spec ↧ℂ)) (n : ℕ) (b : ComplexPoint Z) (i : Fin (n + 1)) :
    IsPullback (s2c_branchInsertion Z n b ≫ s2_permute Z (n + 1) (Equiv.swap 0 i)).left
      (g3_power Z n).hom (g3_proj Z (n + 1) i).left b.left := by
  classical
  let e := (Over.forget (Spec ↧ℂ)).mapIso (s2_permuteIso Z (n + 1) (Equiv.swap 0 i))
  apply (s2v_l1a_branchInsertion_isPullback Z n b).of_iso
    (Iso.refl _) e (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp
  · simp only [Iso.refl_hom, Category.comp_id]
    change (g3_proj Z (n + 1) 0).left =
      (s2_permute Z (n + 1) (Equiv.swap 0 i) ≫ g3_proj Z (n + 1) i).left
    simp only [s2_permute, s2_check_lift_proj, Equiv.symm_swap, Equiv.swap_apply_right]
  · simp

/-- The kernel of a moved insertion is the full ideal of its specified coordinate point. -/
theorem s2v_l1b_divisor_coordinate_insertion_kernel
    (Z : Over (Spec ↧ℂ)) [IsSeparated Z.hom]
    (n : ℕ) (b : ComplexPoint Z) (i : Fin (n + 1)) :
    (s2c_branchInsertion Z n b ≫ s2_permute Z (n + 1) (Equiv.swap 0 i)).left.ker =
      b.left.ker.comap (g3_proj Z (n + 1) i).left := by
  letI : IsClosedImmersion (b.left ≫ Z.hom) := by
    rw [b.w]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion b.left := IsClosedImmersion.of_comp b.left Z.hom
  let H := s2v_l1b_divisor_coordinate_insertion_isPullback Z n b i
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion b.left
    (g3_proj Z (n + 1) i).left]
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end HodgeLean.Foundations.Program
