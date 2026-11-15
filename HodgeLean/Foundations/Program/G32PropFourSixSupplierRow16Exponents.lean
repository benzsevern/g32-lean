import HodgeLean.Foundations.Program.G32PropFourSixPacked0688
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 200000

theorem g32p_row16_trace_avoid : ∀ i : Fin 15, ∀ j : Fin 13,
    g32p_row16_traces i ≠ g32p_branchTrace j := by
  decide

theorem g32p_row16_branch_exps (j : Fin 13) :
    papersExps g32p_row16_finiteSupplier.H g32p_row16_finiteSupplier.χ
      (g32p_classDatum j) = 0 := by
  apply g32p_exps_of_character_avoid (p := if j.val < 12 then 3 else 2)
    (by split_ifs <;> decide) _ _ _ (g32p_branch_power j) g32p_rho
  intro h he
  let i := g32p_row16_groupEquiv.symm h
  have hi : g32p_row16_groupEquiv i = h := g32p_row16_groupEquiv.apply_symm_apply h
  rw [← hi, g32p_row16_character, g32p_branch_character] at he
  exact g32p_row16_trace_avoid i j (HurwitzPrymRex_ev_injective g32h_omega_sq_add he)

theorem g32p_row16_exponents : g32p_exponents g32p_row16_finiteSupplier = [] := by
  have hs : papersExpsTuple g32p_row16_finiteSupplier.H
      g32p_row16_finiteSupplier.χ g32p_classList = 0 := by
    unfold papersExpsTuple g32p_classList
    rw [List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_eq_zero (fun j _ => g32p_row16_branch_exps j)
  change ((papersExpsTuple _ _ _).map ZMod.val).toList = []
  rw [hs, Multiset.map_zero, Multiset.toList_zero]

theorem g32p_row16_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 16 ∧ r.m = g32p_row16_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row16_finiteSupplier.H ∧
      (g32p_exponents g32p_row16_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨16, 1, 15, 15, 33697, 0, 67392, none, [], .U⟩,
    ?_, rfl, rfl, g32p_row16_finiteSupplier_order.symm, ?_⟩
  · decide
  · rw [g32p_row16_exponents]
    exact List.Perm.refl _

end HodgeLean.Foundations.Program
