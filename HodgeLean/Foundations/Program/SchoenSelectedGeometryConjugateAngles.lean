import HodgeLean.Foundations.Program.SchoenSelectedGeometryRootConjugate

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- A nontrivial root and its conjugate have complementary normalized angles. -/
theorem s0_residue_conjugate_angle_sum (S : g32p_Supplier) (a : ZMod S.m) (ha : a ≠ 0) :
    g32h_angle (g32p_root S.m ^ a.val) +
      g32h_angle (star (g32p_root S.m ^ a.val)) = 1 := by
  letI : NeZero a := ⟨ha⟩
  have h₁ : g32h_angle (g32p_root S.m ^ a.val) = (a.val : ℝ) / S.m :=
    b4_angle_exp_power (NeZero.pos S.m) (ZMod.val_lt a)
  have h₂ : g32h_angle (g32p_root S.m ^ (-a).val) = ((-a).val : ℝ) / S.m :=
    b4_angle_exp_power (NeZero.pos S.m) (ZMod.val_lt (-a))
  rw [s0_root_residue_conjugate, h₁, h₂, ZMod.val_neg_of_ne_zero,
    Nat.cast_sub (Nat.le_of_lt (ZMod.val_lt a))]
  have hm : (S.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne S.m)
  field_simp
  ring

#print axioms s0_residue_conjugate_angle_sum
end HodgeLean.Foundations.Program
