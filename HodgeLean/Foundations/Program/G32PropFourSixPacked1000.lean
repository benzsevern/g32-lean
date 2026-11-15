import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow48
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0764
import HodgeLean.Foundations.Program.G32PropFourSixPacked0998
import HodgeLean.Foundations.Program.G32PropFourSixPacked0999
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row48_squareBlock19 : ∀ r : Fin 16,
    HurwitzPrymRex_mmul
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 19 r))
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 19 r)) = HurwitzPrymRex_mone →
    g32p_row48_characterValues (g32p_finBlockIndex 384 19 r) = 1 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row48_squareBlock20 : ∀ r : Fin 16,
    HurwitzPrymRex_mmul
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 20 r))
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 20 r)) = HurwitzPrymRex_mone →
    g32p_row48_characterValues (g32p_finBlockIndex 384 20 r) = 1 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row48_squareBlock21 : ∀ r : Fin 16,
    HurwitzPrymRex_mmul
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 21 r))
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 21 r)) = HurwitzPrymRex_mone →
    g32p_row48_characterValues (g32p_finBlockIndex 384 21 r) = 1 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row48_squareBlock22 : ∀ r : Fin 16,
    HurwitzPrymRex_mmul
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 22 r))
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 22 r)) = HurwitzPrymRex_mone →
    g32p_row48_characterValues (g32p_finBlockIndex 384 22 r) = 1 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row48_squareBlock23 : ∀ r : Fin 16,
    HurwitzPrymRex_mmul
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 23 r))
      (g32p_row36_groupNodes (g32p_finBlockIndex 384 23 r)) = HurwitzPrymRex_mone →
    g32p_row48_characterValues (g32p_finBlockIndex 384 23 r) = 1 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row48_traces : Fin 384 → HurwitzPrymRex_Zw :=
  ![⟨4, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, -4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 4⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, -4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

theorem g32p_row48_traceCertificate (i : Fin 384) :
    (⟨∑ j : Fin 4, (g32p_row36_groupNodes i j j).re,
      ∑ j : Fin 4, (g32p_row36_groupNodes i j j).om⟩ : HurwitzPrymRex_Zw) =
      g32p_row48_traces i := by
  revert i
  decide +kernel

theorem g32p_row48_character (i : Fin 384) :
    g32p_rho.character (g32p_row36_groupEquiv i : g32p_G) =
      HurwitzPrymRex_ev g32h_omega (g32p_row48_traces i) := by
  rw [g32p_rho_character, g32p_row36_groupEquiv_map, g32p_archive_trace,
    g32p_integral_trace, g32p_row48_traceCertificate]

theorem g32p_row48_trace_avoid : ∀ i : Fin 384, ∀ j : Fin 12,
    g32p_row48_traces i ≠ g32p_branchTrace ⟨j.val, by omega⟩ := by
  decide +kernel

theorem g32p_row48_squareCheck : ∀ i : Fin 384,
    HurwitzPrymRex_mmul (g32p_row36_groupNodes i) (g32p_row36_groupNodes i) =
      HurwitzPrymRex_mone → g32p_row48_characterValues i = 1 := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row48_squareBlock00
  · exact g32p_row48_squareBlock01
  · exact g32p_row48_squareBlock02
  · exact g32p_row48_squareBlock03
  · exact g32p_row48_squareBlock04
  · exact g32p_row48_squareBlock05
  · exact g32p_row48_squareBlock06
  · exact g32p_row48_squareBlock07
  · exact g32p_row48_squareBlock08
  · exact g32p_row48_squareBlock09
  · exact g32p_row48_squareBlock10
  · exact g32p_row48_squareBlock11
  · exact g32p_row48_squareBlock12
  · exact g32p_row48_squareBlock13
  · exact g32p_row48_squareBlock14
  · exact g32p_row48_squareBlock15
  · exact g32p_row48_squareBlock16
  · exact g32p_row48_squareBlock17
  · exact g32p_row48_squareBlock18
  · exact g32p_row48_squareBlock19
  · exact g32p_row48_squareBlock20
  · exact g32p_row48_squareBlock21
  · exact g32p_row48_squareBlock22
  · exact g32p_row48_squareBlock23

theorem g32p_row48_squareKernel : ∀ h : g32p_row48_finiteSupplier.H,
    h ^ 2 = 1 → g32p_row48_finiteSupplier.χ h = 1 :=
  g32p_supplier_square_kernel g32p_row48_finiteSupplier
    g32p_row36_groupEquiv g32p_row36_groupNodes g32p_row48_characterValues
    g32p_row48_finiteSupplier_value g32p_row36_groupEquiv_map g32p_row48_squareCheck

theorem g32p_row48_branch_exps (j : Fin 13) :
    papersExps g32p_row48_finiteSupplier.H g32p_row48_finiteSupplier.χ
      (g32p_classDatum j) = 0 := by
  by_cases hj : j.val < 12
  · apply g32p_exps_of_character_avoid (p := 3) (by decide) _ _ _
      (by simpa only [if_pos hj] using g32p_branch_power j) g32p_rho
    intro h he
    let i := g32p_row36_groupEquiv.symm h
    have hi : g32p_row36_groupEquiv i = h := g32p_row36_groupEquiv.apply_symm_apply h
    rw [← hi, g32p_row48_character, g32p_branch_character] at he
    exact g32p_row48_trace_avoid i ⟨j.val, hj⟩
      (HurwitzPrymRex_ev_injective g32h_omega_sq_add he)
  · have he : j = 12 := Fin.ext (by omega)
    subst j
    exact g32p_exps_of_power_kernel _ _ _ (g32p_branch_power 12) g32p_row48_squareKernel

theorem g32p_row48_exponents : g32p_exponents g32p_row48_finiteSupplier = [] := by
  have hs : papersExpsTuple g32p_row48_finiteSupplier.H
      g32p_row48_finiteSupplier.χ g32p_classList = 0 := by
    unfold papersExpsTuple g32p_classList
    rw [List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_eq_zero (fun j _ => g32p_row48_branch_exps j)
  change ((papersExpsTuple _ _ _).map ZMod.val).toList = []
  rw [hs, Multiset.map_zero, Multiset.toList_zero]

theorem g32p_row48_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 48 ∧ r.m = g32p_row48_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row48_finiteSupplier.H ∧
      (g32p_exponents g32p_row48_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨48, (-1), 384, 6, 1306, 0, 2610, none, [], .U⟩,
    ?_, rfl, rfl, g32p_row48_finiteSupplier_order.symm, ?_⟩
  · decide
  · rw [g32p_row48_exponents]
    exact List.Perm.refl _


def g32p_row48_complexWitness : g32p_row48_finiteSupplier.H →* ℂˣ :=
  g32p_complexCharacter g32p_row48_finiteSupplier

theorem g32p_row48_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 48 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row48_finiteSupplier, g32p_row48_complexWitness,
    g32p_complexCharacter_apply _, g32p_row48_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
