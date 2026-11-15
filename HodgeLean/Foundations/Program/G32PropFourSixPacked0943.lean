import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixPacked0932
import HodgeLean.Foundations.Program.G32PropFourSixPacked0937
import HodgeLean.Foundations.Program.G32PropFourSixPacked0942
import HodgeLean.Foundations.Program.G32PropFourSixPacked0938
import HodgeLean.Foundations.Program.G32PropFourSixPacked0939
import HodgeLean.Foundations.Program.G32PropFourSixPacked0940
import HodgeLean.Foundations.Program.G32PropFourSixPacked0941
import HodgeLean.Foundations.Program.G32PropFourSixCharacters
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow38
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0764

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row37_cosetBranchMatrix2 : g32p_row37_cosetBranchMatrices 2 = g32p_cosetIntegralBranches 2 := by
  decide +kernel

theorem g32p_row37_cosetRootLabels2 : ∀ j : Fin 552, g32p_row37_cosetLabels2 (g32p_row37_cosetRoots2 j) = j := by
  decide +kernel

theorem g32p_row37_cosetNextLabels2 : ∀ i : Fin 1080, g32p_row37_cosetLabels2 (g32p_row37_cosetBranchNext 2 i) = g32p_row37_cosetLabels2 i := by
  decide +kernel

theorem g32p_row37_cosetReach2 : ∀ i : Fin 1080, (g32p_row37_cosetBranchNext 2)^[g32p_row37_cosetDistances2 i] (g32p_row37_cosetRoots2 (g32p_row37_cosetLabels2 i)) = i := by
  decide +kernel

theorem g32p_row37_cosetPeriods2 : ∀ j : Fin 552, 0 < g32p_row37_cosetLengths2 j ∧ (g32p_row37_cosetBranchNext 2)^[g32p_row37_cosetLengths2 j] (g32p_row37_cosetRoots2 j) = g32p_row37_cosetRoots2 j ∧ ∀ t : Fin (g32p_row37_cosetLengths2 j), 0 < t.val → (g32p_row37_cosetBranchNext 2)^[t.val] (g32p_row37_cosetRoots2 j) ≠ g32p_row37_cosetRoots2 j := by
  decide +kernel

theorem g32p_row37_cosetCycleSteps2 : ∀ cycle ∈ g32p_row37_cosetCycles2,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row37_cosetBranchNext 2 ⟨i % 1080, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row37_cosetInverse2 : ∀ i : Fin 1080,
    ((g32p_row37_cosetBranchNext 2)^[1]) (g32p_row37_cosetBranchNext 2 i) = i ∧
    g32p_row37_cosetBranchNext 2 (((g32p_row37_cosetBranchNext 2)^[1]) i) = i := by
  decide +kernel

theorem g32p_row37_cosetPermutation2 : Function.Bijective (g32p_row37_cosetBranchNext 2) := by
  have hl : Function.LeftInverse ((g32p_row37_cosetBranchNext 2)^[1]) (g32p_row37_cosetBranchNext 2) :=
    fun i => (g32p_row37_cosetInverse2 i).1
  have hr : Function.RightInverse ((g32p_row37_cosetBranchNext 2)^[1]) (g32p_row37_cosetBranchNext 2) :=
    fun i => (g32p_row37_cosetInverse2 i).2
  exact ⟨hl.injective, hr.surjective⟩


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_cosetEquiv : Fin 1080 ≃ (g32p_G ⧸ g32p_row37_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row37_cosetEnumeration

theorem g32p_row37_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row37_cosetBranchMatrices b)) := by
  have he : g32p_row37_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    fin_cases b
    · exact g32p_row37_cosetBranchMatrix0
    · exact g32p_row37_cosetBranchMatrix1
    · exact g32p_row37_cosetBranchMatrix2
  rw [he]
  exact g32p_cosetBranches_map b

theorem g32p_row37_cosetBranchCheck (b : Fin 3) (i : Fin 1080) :
    HurwitzPrymRex_mmul (g32p_row37_cosetBranchMatrices b) (g32p_row37_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row37_cosetRepresentatives (g32p_row37_cosetBranchNext b i))
        (g32p_row37_groupNodes (g32p_row37_cosetBranchFactor b i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row37_cosetBranchBlock_0000 b
  · exact g32p_row37_cosetBranchBlock_0001 b
  · exact g32p_row37_cosetBranchBlock_0002 b
  · exact g32p_row37_cosetBranchBlock_0003 b
  · exact g32p_row37_cosetBranchBlock_0004 b
  · exact g32p_row37_cosetBranchBlock_0005 b
  · exact g32p_row37_cosetBranchBlock_0006 b
  · exact g32p_row37_cosetBranchBlock_0007 b
  · exact g32p_row37_cosetBranchBlock_0008 b
  · exact g32p_row37_cosetBranchBlock_0009 b
  · exact g32p_row37_cosetBranchBlock_0010 b
  · exact g32p_row37_cosetBranchBlock_0011 b
  · exact g32p_row37_cosetBranchBlock_0012 b
  · exact g32p_row37_cosetBranchBlock_0013 b
  · exact g32p_row37_cosetBranchBlock_0014 b
  · exact g32p_row37_cosetBranchBlock_0015 b
  · exact g32p_row37_cosetBranchBlock_0016 b
  · exact g32p_row37_cosetBranchBlock_0017 b
  · exact g32p_row37_cosetBranchBlock_0018 b
  · exact g32p_row37_cosetBranchBlock_0019 b
  · exact g32p_row37_cosetBranchBlock_0020 b
  · exact g32p_row37_cosetBranchBlock_0021 b
  · exact g32p_row37_cosetBranchBlock_0022 b
  · exact g32p_row37_cosetBranchBlock_0023 b
  · exact g32p_row37_cosetBranchBlock_0024 b
  · exact g32p_row37_cosetBranchBlock_0025 b
  · exact g32p_row37_cosetBranchBlock_0026 b
  · exact g32p_row37_cosetBranchBlock_0027 b
  · exact g32p_row37_cosetBranchBlock_0028 b
  · exact g32p_row37_cosetBranchBlock_0029 b
  · exact g32p_row37_cosetBranchBlock_0030 b
  · exact g32p_row37_cosetBranchBlock_0031 b
  · exact g32p_row37_cosetBranchBlock_0032 b
  · exact g32p_row37_cosetBranchBlock_0033 b
  · exact g32p_row37_cosetBranchBlock_0034 b
  · exact g32p_row37_cosetBranchBlock_0035 b
  · exact g32p_row37_cosetBranchBlock_0036 b
  · exact g32p_row37_cosetBranchBlock_0037 b
  · exact g32p_row37_cosetBranchBlock_0038 b
  · exact g32p_row37_cosetBranchBlock_0039 b
  · exact g32p_row37_cosetBranchBlock_0040 b
  · exact g32p_row37_cosetBranchBlock_0041 b
  · exact g32p_row37_cosetBranchBlock_0042 b
  · exact g32p_row37_cosetBranchBlock_0043 b
  · exact g32p_row37_cosetBranchBlock_0044 b
  · exact g32p_row37_cosetBranchBlock_0045 b
  · exact g32p_row37_cosetBranchBlock_0046 b
  · exact g32p_row37_cosetBranchBlock_0047 b
  · exact g32p_row37_cosetBranchBlock_0048 b
  · exact g32p_row37_cosetBranchBlock_0049 b
  · exact g32p_row37_cosetBranchBlock_0050 b
  · exact g32p_row37_cosetBranchBlock_0051 b
  · exact g32p_row37_cosetBranchBlock_0052 b
  · exact g32p_row37_cosetBranchBlock_0053 b
  · exact g32p_row37_cosetBranchBlock_0054 b
  · exact g32p_row37_cosetBranchBlock_0055 b
  · exact g32p_row37_cosetBranchBlock_0056 b
  · exact g32p_row37_cosetBranchBlock_0057 b
  · exact g32p_row37_cosetBranchBlock_0058 b
  · exact g32p_row37_cosetBranchBlock_0059 b
  · exact g32p_row37_cosetBranchBlock_0060 b
  · exact g32p_row37_cosetBranchBlock_0061 b
  · exact g32p_row37_cosetBranchBlock_0062 b
  · exact g32p_row37_cosetBranchBlock_0063 b
  · exact g32p_row37_cosetBranchBlock_0064 b
  · exact g32p_row37_cosetBranchBlock_0065 b
  · exact g32p_row37_cosetBranchBlock_0066 b
  · exact g32p_row37_cosetBranchBlock_0067 b


theorem g32p_row37_cosetActualBranchStep (b : Fin 3) (i : Fin 1080) :
    g32p_cosetBranches b * g32p_row37_cosetActualRepresentatives i =
      g32p_row37_cosetActualRepresentatives (g32p_row37_cosetBranchNext b i) *
        (g32p_row37_groupEquiv (g32p_row37_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row37_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row37_cosetActualRepresentatives (g32p_row37_cosetBranchNext b i) *
      (g32p_row37_groupEquiv (g32p_row37_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row37_cosetBranchMap, g32p_row37_cosetActualRepresentatives_map,
    g32p_row37_cosetActualRepresentatives_map, g32p_row37_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row37_cosetBranchCheck]

theorem g32p_row37_cosetQuotientStep (b : Fin 3) (i : Fin 1080) :
    g32p_row37_cosetEquiv (g32p_row37_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row37_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row37_cosetActualRepresentatives (g32p_row37_cosetBranchNext b i)) : g32p_G ⧸ g32p_row37_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row37_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row37_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row37_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row37_groupEquiv (g32p_row37_cosetBranchFactor b i)).property

def g32p_row37_cosetOrbitEquiv0 : Fin 432 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 0)) (g32p_G ⧸ g32p_row37_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 0) g32p_row37_cosetEquiv
    (g32p_row37_cosetBranchNext 0) (g32p_row37_cosetQuotientStep 0) g32p_row37_cosetLabels0 g32p_row37_cosetRoots0
    g32p_row37_cosetDistances0 g32p_row37_cosetRootLabels0 g32p_row37_cosetNextLabels0 g32p_row37_cosetReach0)

theorem g32p_row37_cosetPeriod0 (j : Fin 432) :
    Function.minimalPeriod ((g32p_cosetBranches 0) • ·) (g32p_row37_cosetEquiv (g32p_row37_cosetRoots0 j)) = g32p_row37_cosetLengths0 j := by
  apply g32p_period_of_cycle g32p_row37_cosetEquiv (g32p_row37_cosetBranchNext 0) ((g32p_cosetBranches 0) • ·)
    (g32p_row37_cosetQuotientStep 0) _ _ (g32p_row37_cosetPeriods0 j).1 (g32p_row37_cosetPeriods0 j).2.1
  intro t ht hlt
  exact (g32p_row37_cosetPeriods0 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row37_cosetMonodromyCheck0 (j : Fin 432) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row37_cosetBranchMatrices 0) (g32p_row37_cosetLengths0 j))
      (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots0 j)) =
      HurwitzPrymRex_mmul (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots0 j))
        (g32p_row37_groupNodes (g32p_row37_cosetMonodromies0 j)) ∧
    g32p_row37_characterValues (g32p_row37_cosetMonodromies0 j) = g32p_row37_cosetExponents0 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row37_cosetMonodromyBlock0_0000
  · exact g32p_row37_cosetMonodromyBlock0_0001
  · exact g32p_row37_cosetMonodromyBlock0_0002
  · exact g32p_row37_cosetMonodromyBlock0_0003
  · exact g32p_row37_cosetMonodromyBlock0_0004
  · exact g32p_row37_cosetMonodromyBlock0_0005
  · exact g32p_row37_cosetMonodromyBlock0_0006
  · exact g32p_row37_cosetMonodromyBlock0_0007
  · exact g32p_row37_cosetMonodromyBlock0_0008
  · exact g32p_row37_cosetMonodromyBlock0_0009
  · exact g32p_row37_cosetMonodromyBlock0_0010
  · exact g32p_row37_cosetMonodromyBlock0_0011
  · exact g32p_row37_cosetMonodromyBlock0_0012
  · exact g32p_row37_cosetMonodromyBlock0_0013
  · exact g32p_row37_cosetMonodromyBlock0_0014
  · exact g32p_row37_cosetMonodromyBlock0_0015
  · exact g32p_row37_cosetMonodromyBlock0_0016
  · exact g32p_row37_cosetMonodromyBlock0_0017
  · exact g32p_row37_cosetMonodromyBlock0_0018
  · exact g32p_row37_cosetMonodromyBlock0_0019
  · exact g32p_row37_cosetMonodromyBlock0_0020
  · exact g32p_row37_cosetMonodromyBlock0_0021
  · exact g32p_row37_cosetMonodromyBlock0_0022
  · exact g32p_row37_cosetMonodromyBlock0_0023
  · exact g32p_row37_cosetMonodromyBlock0_0024
  · exact g32p_row37_cosetMonodromyBlock0_0025
  · exact g32p_row37_cosetMonodromyBlock0_0026

theorem g32p_row37_cosetActualMonodromy0 (j : Fin 432) :
    (g32p_cosetBranches 0) ^ g32p_row37_cosetLengths0 j * g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots0 j) =
      g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots0 j) *
        (g32p_row37_groupEquiv (g32p_row37_cosetMonodromies0 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row37_cosetBranchMatrices 0)
    (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots0 j))
    (g32p_row37_groupNodes (g32p_row37_cosetMonodromies0 j))
    (g32p_row37_cosetLengths0 j) (g32p_row37_cosetBranchMap 0)
    (g32p_row37_cosetActualRepresentatives_map _) (g32p_row37_groupEquiv_map _)
  exact (g32p_row37_cosetMonodromyCheck0 j).1

theorem g32p_row37_cosetCharacter0 (j : Fin 432) :
    g32p_row37_finiteSupplier.χ (g32p_row37_groupEquiv (g32p_row37_cosetMonodromies0 j)) = g32p_row37_cosetExponents0 j := by
  rw [g32p_row37_finiteSupplier_value]
  exact (g32p_row37_cosetMonodromyCheck0 j).2

theorem g32p_row37_cosetBranchExponents0 :
    papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_cosetBranches 0) =
      (Finset.univ.val.map (fun j : Fin 432 => Multiplicative.toAdd (g32p_row37_cosetExponents0 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row37_cosetOrbitEquiv0
    (fun j => g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots0 j)) (fun _ => rfl) g32p_row37_cosetLengths0 g32p_row37_cosetPeriod0
    (fun j => g32p_row37_groupEquiv (g32p_row37_cosetMonodromies0 j)) g32p_row37_cosetActualMonodromy0]
  simp only [g32p_row37_cosetCharacter0]
  rfl

def g32p_row37_cosetOrbitEquiv1 : Fin 432 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 1)) (g32p_G ⧸ g32p_row37_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 1) g32p_row37_cosetEquiv
    (g32p_row37_cosetBranchNext 1) (g32p_row37_cosetQuotientStep 1) g32p_row37_cosetLabels1 g32p_row37_cosetRoots1
    g32p_row37_cosetDistances1 g32p_row37_cosetRootLabels1 g32p_row37_cosetNextLabels1 g32p_row37_cosetReach1)

theorem g32p_row37_cosetPeriod1 (j : Fin 432) :
    Function.minimalPeriod ((g32p_cosetBranches 1) • ·) (g32p_row37_cosetEquiv (g32p_row37_cosetRoots1 j)) = g32p_row37_cosetLengths1 j := by
  apply g32p_period_of_cycle g32p_row37_cosetEquiv (g32p_row37_cosetBranchNext 1) ((g32p_cosetBranches 1) • ·)
    (g32p_row37_cosetQuotientStep 1) _ _ (g32p_row37_cosetPeriods1 j).1 (g32p_row37_cosetPeriods1 j).2.1
  intro t ht hlt
  exact (g32p_row37_cosetPeriods1 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row37_cosetMonodromyCheck1 (j : Fin 432) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row37_cosetBranchMatrices 1) (g32p_row37_cosetLengths1 j))
      (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots1 j)) =
      HurwitzPrymRex_mmul (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots1 j))
        (g32p_row37_groupNodes (g32p_row37_cosetMonodromies1 j)) ∧
    g32p_row37_characterValues (g32p_row37_cosetMonodromies1 j) = g32p_row37_cosetExponents1 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row37_cosetMonodromyBlock1_0000
  · exact g32p_row37_cosetMonodromyBlock1_0001
  · exact g32p_row37_cosetMonodromyBlock1_0002
  · exact g32p_row37_cosetMonodromyBlock1_0003
  · exact g32p_row37_cosetMonodromyBlock1_0004
  · exact g32p_row37_cosetMonodromyBlock1_0005
  · exact g32p_row37_cosetMonodromyBlock1_0006
  · exact g32p_row37_cosetMonodromyBlock1_0007
  · exact g32p_row37_cosetMonodromyBlock1_0008
  · exact g32p_row37_cosetMonodromyBlock1_0009
  · exact g32p_row37_cosetMonodromyBlock1_0010
  · exact g32p_row37_cosetMonodromyBlock1_0011
  · exact g32p_row37_cosetMonodromyBlock1_0012
  · exact g32p_row37_cosetMonodromyBlock1_0013
  · exact g32p_row37_cosetMonodromyBlock1_0014
  · exact g32p_row37_cosetMonodromyBlock1_0015
  · exact g32p_row37_cosetMonodromyBlock1_0016
  · exact g32p_row37_cosetMonodromyBlock1_0017
  · exact g32p_row37_cosetMonodromyBlock1_0018
  · exact g32p_row37_cosetMonodromyBlock1_0019
  · exact g32p_row37_cosetMonodromyBlock1_0020
  · exact g32p_row37_cosetMonodromyBlock1_0021
  · exact g32p_row37_cosetMonodromyBlock1_0022
  · exact g32p_row37_cosetMonodromyBlock1_0023
  · exact g32p_row37_cosetMonodromyBlock1_0024
  · exact g32p_row37_cosetMonodromyBlock1_0025
  · exact g32p_row37_cosetMonodromyBlock1_0026

theorem g32p_row37_cosetActualMonodromy1 (j : Fin 432) :
    (g32p_cosetBranches 1) ^ g32p_row37_cosetLengths1 j * g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots1 j) =
      g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots1 j) *
        (g32p_row37_groupEquiv (g32p_row37_cosetMonodromies1 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row37_cosetBranchMatrices 1)
    (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots1 j))
    (g32p_row37_groupNodes (g32p_row37_cosetMonodromies1 j))
    (g32p_row37_cosetLengths1 j) (g32p_row37_cosetBranchMap 1)
    (g32p_row37_cosetActualRepresentatives_map _) (g32p_row37_groupEquiv_map _)
  exact (g32p_row37_cosetMonodromyCheck1 j).1

theorem g32p_row37_cosetCharacter1 (j : Fin 432) :
    g32p_row37_finiteSupplier.χ (g32p_row37_groupEquiv (g32p_row37_cosetMonodromies1 j)) = g32p_row37_cosetExponents1 j := by
  rw [g32p_row37_finiteSupplier_value]
  exact (g32p_row37_cosetMonodromyCheck1 j).2

theorem g32p_row37_cosetBranchExponents1 :
    papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_cosetBranches 1) =
      (Finset.univ.val.map (fun j : Fin 432 => Multiplicative.toAdd (g32p_row37_cosetExponents1 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row37_cosetOrbitEquiv1
    (fun j => g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots1 j)) (fun _ => rfl) g32p_row37_cosetLengths1 g32p_row37_cosetPeriod1
    (fun j => g32p_row37_groupEquiv (g32p_row37_cosetMonodromies1 j)) g32p_row37_cosetActualMonodromy1]
  simp only [g32p_row37_cosetCharacter1]
  rfl

def g32p_row37_cosetOrbitEquiv2 : Fin 552 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row37_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row37_cosetEquiv
    (g32p_row37_cosetBranchNext 2) (g32p_row37_cosetQuotientStep 2) g32p_row37_cosetLabels2 g32p_row37_cosetRoots2
    g32p_row37_cosetDistances2 g32p_row37_cosetRootLabels2 g32p_row37_cosetNextLabels2 g32p_row37_cosetReach2)

theorem g32p_row37_cosetPeriod2 (j : Fin 552) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row37_cosetEquiv (g32p_row37_cosetRoots2 j)) = g32p_row37_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row37_cosetEquiv (g32p_row37_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row37_cosetQuotientStep 2) _ _ (g32p_row37_cosetPeriods2 j).1 (g32p_row37_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row37_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row37_cosetMonodromyCheck2 (j : Fin 552) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row37_cosetBranchMatrices 2) (g32p_row37_cosetLengths2 j))
      (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots2 j)) =
      HurwitzPrymRex_mmul (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots2 j))
        (g32p_row37_groupNodes (g32p_row37_cosetMonodromies2 j)) ∧
    g32p_row37_characterValues (g32p_row37_cosetMonodromies2 j) = g32p_row37_cosetExponents2 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row37_cosetMonodromyBlock2_0000
  · exact g32p_row37_cosetMonodromyBlock2_0001
  · exact g32p_row37_cosetMonodromyBlock2_0002
  · exact g32p_row37_cosetMonodromyBlock2_0003
  · exact g32p_row37_cosetMonodromyBlock2_0004
  · exact g32p_row37_cosetMonodromyBlock2_0005
  · exact g32p_row37_cosetMonodromyBlock2_0006
  · exact g32p_row37_cosetMonodromyBlock2_0007
  · exact g32p_row37_cosetMonodromyBlock2_0008
  · exact g32p_row37_cosetMonodromyBlock2_0009
  · exact g32p_row37_cosetMonodromyBlock2_0010
  · exact g32p_row37_cosetMonodromyBlock2_0011
  · exact g32p_row37_cosetMonodromyBlock2_0012
  · exact g32p_row37_cosetMonodromyBlock2_0013
  · exact g32p_row37_cosetMonodromyBlock2_0014
  · exact g32p_row37_cosetMonodromyBlock2_0015
  · exact g32p_row37_cosetMonodromyBlock2_0016
  · exact g32p_row37_cosetMonodromyBlock2_0017
  · exact g32p_row37_cosetMonodromyBlock2_0018
  · exact g32p_row37_cosetMonodromyBlock2_0019
  · exact g32p_row37_cosetMonodromyBlock2_0020
  · exact g32p_row37_cosetMonodromyBlock2_0021
  · exact g32p_row37_cosetMonodromyBlock2_0022
  · exact g32p_row37_cosetMonodromyBlock2_0023
  · exact g32p_row37_cosetMonodromyBlock2_0024
  · exact g32p_row37_cosetMonodromyBlock2_0025
  · exact g32p_row37_cosetMonodromyBlock2_0026
  · exact g32p_row37_cosetMonodromyBlock2_0027
  · exact g32p_row37_cosetMonodromyBlock2_0028
  · exact g32p_row37_cosetMonodromyBlock2_0029
  · exact g32p_row37_cosetMonodromyBlock2_0030
  · exact g32p_row37_cosetMonodromyBlock2_0031
  · exact g32p_row37_cosetMonodromyBlock2_0032
  · exact g32p_row37_cosetMonodromyBlock2_0033
  · exact g32p_row37_cosetMonodromyBlock2_0034

theorem g32p_row37_cosetActualMonodromy2 (j : Fin 552) :
    (g32p_cosetBranches 2) ^ g32p_row37_cosetLengths2 j * g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots2 j) =
      g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots2 j) *
        (g32p_row37_groupEquiv (g32p_row37_cosetMonodromies2 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row37_cosetBranchMatrices 2)
    (g32p_row37_cosetRepresentatives (g32p_row37_cosetRoots2 j))
    (g32p_row37_groupNodes (g32p_row37_cosetMonodromies2 j))
    (g32p_row37_cosetLengths2 j) (g32p_row37_cosetBranchMap 2)
    (g32p_row37_cosetActualRepresentatives_map _) (g32p_row37_groupEquiv_map _)
  exact (g32p_row37_cosetMonodromyCheck2 j).1

theorem g32p_row37_cosetCharacter2 (j : Fin 552) :
    g32p_row37_finiteSupplier.χ (g32p_row37_groupEquiv (g32p_row37_cosetMonodromies2 j)) = g32p_row37_cosetExponents2 j := by
  rw [g32p_row37_finiteSupplier_value]
  exact (g32p_row37_cosetMonodromyCheck2 j).2

theorem g32p_row37_cosetBranchExponents2 :
    papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 552 => Multiplicative.toAdd (g32p_row37_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row37_cosetOrbitEquiv2
    (fun j => g32p_row37_cosetActualRepresentatives (g32p_row37_cosetRoots2 j)) (fun _ => rfl) g32p_row37_cosetLengths2 g32p_row37_cosetPeriod2
    (fun j => g32p_row37_groupEquiv (g32p_row37_cosetMonodromies2 j)) g32p_row37_cosetActualMonodromy2]
  simp only [g32p_row37_cosetCharacter2]
  rfl

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row37_exponents :
    (g32p_exponents g32p_row37_finiteSupplier).Perm (expandExps [(3, 12)]) := by
  have h0 : papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_classDatum 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row37_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 432)).val.map
      (fun j => Multiplicative.toAdd (g32p_row37_cosetExponents0 j))).filter (· ≠ 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have h1 : papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_classDatum 6) = (([] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row37_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 432)).val.map
      (fun j => Multiplicative.toAdd (g32p_row37_cosetExponents1 j))).filter (· ≠ 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have h2 : papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_classDatum 12) = (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row37_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 552)).val.map
      (fun j => Multiplicative.toAdd (g32p_row37_cosetExponents2 j))).filter (· ≠ 0) = (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have hs : papersExpsTuple g32p_row37_finiteSupplier.H g32p_row37_finiteSupplier.χ g32p_classList =
      6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + 6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + 6 • (([] : List (ZMod 6)) : Multiset (ZMod 6)) + (([3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] : List (ZMod 6)) : Multiset (ZMod 6))).map ZMod.val = ↑(expandExps [(3, 12)])
  decide +kernel

theorem g32p_row37_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 37 ∧ r.m = g32p_row37_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row37_finiteSupplier.H ∧
      (g32p_exponents g32p_row37_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨37, (-1), 144, 6, 3073, 12, 6156, some 3, [(3, 12)], .S⟩, ?_, rfl, rfl, g32p_row37_finiteSupplier_order.symm, g32p_row37_exponents⟩
  decide

def g32p_row37_complexWitness : g32p_row37_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row37_finiteSupplier

theorem g32p_row37_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 37 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row37_finiteSupplier, g32p_row37_complexWitness, g32p_complexCharacter_apply _,
    g32p_row37_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row38_traces : Fin 144 → HurwitzPrymRex_Zw :=
  ![⟨4, 0⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨-1, 2⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, -3⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, 2⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨1, -2⟩, ⟨2, 0⟩, ⟨1, 2⟩, ⟨1, -2⟩, ⟨-3, -2⟩, ⟨-1, -2⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨1, 2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨2, 0⟩, ⟨1, 2⟩, ⟨1, -2⟩, ⟨-3, -2⟩, ⟨-2, -2⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨1, -2⟩, ⟨2, 0⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-3, -2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨-3, -2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-2, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-2, -3⟩, ⟨2, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 3⟩, ⟨1, -1⟩, ⟨-2, -2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨2, 1⟩, ⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩, ⟨-1, 2⟩, ⟨0, -2⟩, ⟨-1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, 2⟩, ⟨3, 2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨3, 2⟩, ⟨-2, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -2⟩, ⟨2, 1⟩, ⟨0, 1⟩, ⟨2, 3⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]

theorem g32p_row38_traceCertificate (i : Fin 144) :
    (⟨∑ j : Fin 4, (g32p_row38_groupNodes i j j).re,
      ∑ j : Fin 4, (g32p_row38_groupNodes i j j).om⟩ : HurwitzPrymRex_Zw) =
      g32p_row38_traces i := by
  revert i
  decide +kernel

theorem g32p_row38_character (i : Fin 144) :
    g32p_rho.character (g32p_row38_groupEquiv i : g32p_G) =
      HurwitzPrymRex_ev g32h_omega (g32p_row38_traces i) := by
  rw [g32p_rho_character, g32p_row38_groupEquiv_map, g32p_archive_trace,
    g32p_integral_trace, g32p_row38_traceCertificate]

theorem g32p_row38_trace_avoid : ∀ i : Fin 144, ∀ j : Fin 12,
    g32p_row38_traces i ≠ g32p_branchTrace ⟨j.val, by omega⟩ := by
  decide +kernel

theorem g32p_row38_branch_exps (j : Fin 13) :
    papersExps g32p_row38_finiteSupplier.H g32p_row38_finiteSupplier.χ
      (g32p_classDatum j) = 0 := by
  by_cases hj : j.val < 12
  · apply g32p_exps_of_character_avoid (p := 3) (by decide) _ _ _
      (by simpa only [if_pos hj] using g32p_branch_power j) g32p_rho
    intro h he
    let i := g32p_row38_groupEquiv.symm h
    have hi : g32p_row38_groupEquiv i = h := g32p_row38_groupEquiv.apply_symm_apply h
    rw [← hi, g32p_row38_character, g32p_branch_character] at he
    exact g32p_row38_trace_avoid i ⟨j.val, hj⟩
      (HurwitzPrymRex_ev_injective g32h_omega_sq_add he)
  · have he : j = 12 := Fin.ext (by omega)
    subst j
    exact g32p_exps_of_coprime_order _ _ _ (g32p_branch_power 12) (by decide)

theorem g32p_row38_exponents : g32p_exponents g32p_row38_finiteSupplier = [] := by
  have hs : papersExpsTuple g32p_row38_finiteSupplier.H
      g32p_row38_finiteSupplier.χ g32p_classList = 0 := by
    unfold papersExpsTuple g32p_classList
    rw [List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_eq_zero (fun j _ => g32p_row38_branch_exps j)
  change ((papersExpsTuple _ _ _).map ZMod.val).toList = []
  rw [hs, Multiset.map_zero, Multiset.toList_zero]

theorem g32p_row38_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 38 ∧ r.m = g32p_row38_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row38_finiteSupplier.H ∧
      (g32p_exponents g32p_row38_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨38, (-1), 144, 3, 3505, 0, 7008, none, [], .U⟩,
    ?_, rfl, rfl, g32p_row38_finiteSupplier_order.symm, ?_⟩
  · decide
  · rw [g32p_row38_exponents]
    exact List.Perm.refl _


def g32p_row38_complexWitness : g32p_row38_finiteSupplier.H →* ℂˣ :=
  g32p_complexCharacter g32p_row38_finiteSupplier

theorem g32p_row38_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 38 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row38_finiteSupplier, g32p_row38_complexWitness,
    g32p_complexCharacter_apply _, g32p_row38_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
