import HodgeLean.Foundations.Program.G32PropFourSixDefs

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem g32c_supplier_simple (S : g32p_Supplier)
    (hrow : ∃ r ∈ g32WitnessTable, r.m = S.m ∧ r.orderH = Nat.card S.H ∧
      (g32p_exponents S).Perm (expandExps r.exps)) :
    IsSimpleExps S.m (g32p_exponents S) := by
  obtain ⟨r, hr, hm, _, he⟩ := hrow
  obtain ⟨L, hL, hp⟩ := papers_g32_table_simple r hr
  exact ⟨L, hL.trans he.symm, fun p hp' => hm ▸ hp p hp'⟩

end HodgeLean.Foundations.Program
