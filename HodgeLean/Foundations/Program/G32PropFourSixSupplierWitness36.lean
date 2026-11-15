import HodgeLean.Foundations.Program.G32PropFourSixPacked0928
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_exponents :
    (g32p_exponents g32p_row36_finiteSupplier).Perm (expandExps [(3, 36)]) := by
  have h0 : papersExps g32p_row36_finiteSupplier.H g32p_row36_finiteSupplier.χ (g32p_classDatum 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row36_finiteSupplier.H g32p_row36_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row36_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 135)).val.map
      (fun j => Multiplicative.toAdd (g32p_row36_cosetExponents0 j))).filter (· ≠ 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have h1 : papersExps g32p_row36_finiteSupplier.H g32p_row36_finiteSupplier.χ (g32p_classDatum 6) = (([] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row36_finiteSupplier.H g32p_row36_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row36_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 135)).val.map
      (fun j => Multiplicative.toAdd (g32p_row36_cosetExponents1 j))).filter (· ≠ 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have h2 : papersExps g32p_row36_finiteSupplier.H g32p_row36_finiteSupplier.χ (g32p_classDatum 12) = (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row36_finiteSupplier.H g32p_row36_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row36_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 225)).val.map
      (fun j => Multiplicative.toAdd (g32p_row36_cosetExponents2 j))).filter (· ≠ 0) = (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have hs : papersExpsTuple g32p_row36_finiteSupplier.H g32p_row36_finiteSupplier.χ g32p_classList =
      6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + 6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + 6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6))).map ZMod.val = ↑(expandExps [(3, 36)])
  decide +kernel

theorem g32p_row36_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 36 ∧ r.m = g32p_row36_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row36_finiteSupplier.H ∧
      (g32p_exponents g32p_row36_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨36, (-1), 384, 6, 1306, 36, 2646, some 3, [(3, 36)], .S⟩, ?_, rfl, rfl, g32p_row36_finiteSupplier_order.symm, g32p_row36_exponents⟩
  decide

def g32p_row36_complexWitness : g32p_row36_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row36_finiteSupplier

theorem g32p_row36_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 36 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row36_finiteSupplier, g32p_row36_complexWitness, g32p_complexCharacter_apply _,
    g32p_row36_finiteSupplier_table⟩

end HodgeLean.Foundations.Program
