import HodgeLean.Foundations.Program.G32SelectedRealizationResidueAge

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Complex conjugation negates the residue of the chosen cyclotomic root. -/
theorem s0_root_residue_conjugate (S : g32p_Supplier) (a : ZMod S.m) :
    star (g32p_root S.m ^ a.val) = g32p_root S.m ^ (-a).val := by
  have hr (a : ZMod S.m) : (ZMod.toCircle a : ℂ) = g32p_root S.m ^ a.val := by
    rw [ZMod.toCircle_apply, g32p_root, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [← hr a, ← hr (-a), AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

#print axioms s0_root_residue_conjugate
end HodgeLean.Foundations.Program
