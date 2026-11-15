import HodgeLean.Foundations.Program.G32PropFourSixPacked1010
import HodgeLean.Foundations.Program.G32PropFourSixPacked1013
import HodgeLean.Foundations.Program.G32PropFourSixPacked1011
import HodgeLean.Foundations.Program.G32PropFourSixPacked1012
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row50_cosetEquiv : Fin 640 ≃ (g32p_G ⧸ g32p_row50_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row50_cosetEnumeration

theorem g32p_row50_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row50_cosetBranchMatrices b)) := by
  have he : g32p_row50_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    fin_cases b
    · exact g32p_row50_cosetBranchMatrix0
    · exact g32p_row50_cosetBranchMatrix1
    · exact g32p_row50_cosetBranchMatrix2
  rw [he]
  exact g32p_cosetBranches_map b

theorem g32p_row50_cosetBranchCheck (b : Fin 3) (i : Fin 640) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices b) (g32p_row50_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext b i))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor b i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row50_cosetBranchBlock_0000 b
  · exact g32p_row50_cosetBranchBlock_0001 b
  · exact g32p_row50_cosetBranchBlock_0002 b
  · exact g32p_row50_cosetBranchBlock_0003 b
  · exact g32p_row50_cosetBranchBlock_0004 b
  · exact g32p_row50_cosetBranchBlock_0005 b
  · exact g32p_row50_cosetBranchBlock_0006 b
  · exact g32p_row50_cosetBranchBlock_0007 b
  · exact g32p_row50_cosetBranchBlock_0008 b
  · exact g32p_row50_cosetBranchBlock_0009 b
  · exact g32p_row50_cosetBranchBlock_0010 b
  · exact g32p_row50_cosetBranchBlock_0011 b
  · exact g32p_row50_cosetBranchBlock_0012 b
  · exact g32p_row50_cosetBranchBlock_0013 b
  · exact g32p_row50_cosetBranchBlock_0014 b
  · exact g32p_row50_cosetBranchBlock_0015 b
  · exact g32p_row50_cosetBranchBlock_0016 b
  · exact g32p_row50_cosetBranchBlock_0017 b
  · exact g32p_row50_cosetBranchBlock_0018 b
  · exact g32p_row50_cosetBranchBlock_0019 b
  · exact g32p_row50_cosetBranchBlock_0020 b
  · exact g32p_row50_cosetBranchBlock_0021 b
  · exact g32p_row50_cosetBranchBlock_0022 b
  · exact g32p_row50_cosetBranchBlock_0023 b
  · exact g32p_row50_cosetBranchBlock_0024 b
  · exact g32p_row50_cosetBranchBlock_0025 b
  · exact g32p_row50_cosetBranchBlock_0026 b
  · exact g32p_row50_cosetBranchBlock_0027 b
  · exact g32p_row50_cosetBranchBlock_0028 b
  · exact g32p_row50_cosetBranchBlock_0029 b
  · exact g32p_row50_cosetBranchBlock_0030 b
  · exact g32p_row50_cosetBranchBlock_0031 b
  · exact g32p_row50_cosetBranchBlock_0032 b
  · exact g32p_row50_cosetBranchBlock_0033 b
  · exact g32p_row50_cosetBranchBlock_0034 b
  · exact g32p_row50_cosetBranchBlock_0035 b
  · exact g32p_row50_cosetBranchBlock_0036 b
  · exact g32p_row50_cosetBranchBlock_0037 b
  · exact g32p_row50_cosetBranchBlock_0038 b
  · exact g32p_row50_cosetBranchBlock_0039 b


theorem g32p_row50_cosetActualBranchStep (b : Fin 3) (i : Fin 640) :
    g32p_cosetBranches b * g32p_row50_cosetActualRepresentatives i =
      g32p_row50_cosetActualRepresentatives (g32p_row50_cosetBranchNext b i) *
        (g32p_row50_groupEquiv (g32p_row50_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row50_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row50_cosetActualRepresentatives (g32p_row50_cosetBranchNext b i) *
      (g32p_row50_groupEquiv (g32p_row50_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row50_cosetBranchMap, g32p_row50_cosetActualRepresentatives_map,
    g32p_row50_cosetActualRepresentatives_map, g32p_row50_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row50_cosetBranchCheck]

theorem g32p_row50_cosetQuotientStep (b : Fin 3) (i : Fin 640) :
    g32p_row50_cosetEquiv (g32p_row50_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row50_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row50_cosetActualRepresentatives (g32p_row50_cosetBranchNext b i)) : g32p_G ⧸ g32p_row50_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row50_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row50_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row50_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row50_groupEquiv (g32p_row50_cosetBranchFactor b i)).property

def g32p_row50_cosetOrbitEquiv0 : Fin 256 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 0)) (g32p_G ⧸ g32p_row50_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 0) g32p_row50_cosetEquiv
    (g32p_row50_cosetBranchNext 0) (g32p_row50_cosetQuotientStep 0) g32p_row50_cosetLabels0 g32p_row50_cosetRoots0
    g32p_row50_cosetDistances0 g32p_row50_cosetRootLabels0 g32p_row50_cosetNextLabels0 g32p_row50_cosetReach0)

theorem g32p_row50_cosetPeriod0 (j : Fin 256) :
    Function.minimalPeriod ((g32p_cosetBranches 0) • ·) (g32p_row50_cosetEquiv (g32p_row50_cosetRoots0 j)) = g32p_row50_cosetLengths0 j := by
  apply g32p_period_of_cycle g32p_row50_cosetEquiv (g32p_row50_cosetBranchNext 0) ((g32p_cosetBranches 0) • ·)
    (g32p_row50_cosetQuotientStep 0) _ _ (g32p_row50_cosetPeriods0 j).1 (g32p_row50_cosetPeriods0 j).2.1
  intro t ht hlt
  exact (g32p_row50_cosetPeriods0 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row50_cosetMonodromyCheck0 (j : Fin 256) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 0) (g32p_row50_cosetLengths0 j))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 j)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 j))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 j)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 j) = g32p_row50_cosetExponents0 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row50_cosetMonodromyBlock0_0000
  · exact g32p_row50_cosetMonodromyBlock0_0001
  · exact g32p_row50_cosetMonodromyBlock0_0002
  · exact g32p_row50_cosetMonodromyBlock0_0003
  · exact g32p_row50_cosetMonodromyBlock0_0004
  · exact g32p_row50_cosetMonodromyBlock0_0005
  · exact g32p_row50_cosetMonodromyBlock0_0006
  · exact g32p_row50_cosetMonodromyBlock0_0007
  · exact g32p_row50_cosetMonodromyBlock0_0008
  · exact g32p_row50_cosetMonodromyBlock0_0009
  · exact g32p_row50_cosetMonodromyBlock0_0010
  · exact g32p_row50_cosetMonodromyBlock0_0011
  · exact g32p_row50_cosetMonodromyBlock0_0012
  · exact g32p_row50_cosetMonodromyBlock0_0013
  · exact g32p_row50_cosetMonodromyBlock0_0014
  · exact g32p_row50_cosetMonodromyBlock0_0015

theorem g32p_row50_cosetActualMonodromy0 (j : Fin 256) :
    (g32p_cosetBranches 0) ^ g32p_row50_cosetLengths0 j * g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots0 j) =
      g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots0 j) *
        (g32p_row50_groupEquiv (g32p_row50_cosetMonodromies0 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row50_cosetBranchMatrices 0)
    (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 j))
    (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 j))
    (g32p_row50_cosetLengths0 j) (g32p_row50_cosetBranchMap 0)
    (g32p_row50_cosetActualRepresentatives_map _) (g32p_row50_groupEquiv_map _)
  exact (g32p_row50_cosetMonodromyCheck0 j).1

theorem g32p_row50_cosetCharacter0 (j : Fin 256) :
    g32p_row50_finiteSupplier.χ (g32p_row50_groupEquiv (g32p_row50_cosetMonodromies0 j)) = g32p_row50_cosetExponents0 j := by
  rw [g32p_row50_finiteSupplier_value]
  exact (g32p_row50_cosetMonodromyCheck0 j).2

theorem g32p_row50_cosetBranchExponents0 :
    papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_cosetBranches 0) =
      (Finset.univ.val.map (fun j : Fin 256 => Multiplicative.toAdd (g32p_row50_cosetExponents0 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row50_cosetOrbitEquiv0
    (fun j => g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots0 j)) (fun _ => rfl) g32p_row50_cosetLengths0 g32p_row50_cosetPeriod0
    (fun j => g32p_row50_groupEquiv (g32p_row50_cosetMonodromies0 j)) g32p_row50_cosetActualMonodromy0]
  simp only [g32p_row50_cosetCharacter0]
  rfl

def g32p_row50_cosetOrbitEquiv1 : Fin 256 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 1)) (g32p_G ⧸ g32p_row50_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 1) g32p_row50_cosetEquiv
    (g32p_row50_cosetBranchNext 1) (g32p_row50_cosetQuotientStep 1) g32p_row50_cosetLabels1 g32p_row50_cosetRoots1
    g32p_row50_cosetDistances1 g32p_row50_cosetRootLabels1 g32p_row50_cosetNextLabels1 g32p_row50_cosetReach1)

theorem g32p_row50_cosetPeriod1 (j : Fin 256) :
    Function.minimalPeriod ((g32p_cosetBranches 1) • ·) (g32p_row50_cosetEquiv (g32p_row50_cosetRoots1 j)) = g32p_row50_cosetLengths1 j := by
  apply g32p_period_of_cycle g32p_row50_cosetEquiv (g32p_row50_cosetBranchNext 1) ((g32p_cosetBranches 1) • ·)
    (g32p_row50_cosetQuotientStep 1) _ _ (g32p_row50_cosetPeriods1 j).1 (g32p_row50_cosetPeriods1 j).2.1
  intro t ht hlt
  exact (g32p_row50_cosetPeriods1 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row50_cosetMonodromyCheck1 (j : Fin 256) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 1) (g32p_row50_cosetLengths1 j))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots1 j)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots1 j))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies1 j)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies1 j) = g32p_row50_cosetExponents1 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row50_cosetMonodromyBlock1_0000
  · exact g32p_row50_cosetMonodromyBlock1_0001
  · exact g32p_row50_cosetMonodromyBlock1_0002
  · exact g32p_row50_cosetMonodromyBlock1_0003
  · exact g32p_row50_cosetMonodromyBlock1_0004
  · exact g32p_row50_cosetMonodromyBlock1_0005
  · exact g32p_row50_cosetMonodromyBlock1_0006
  · exact g32p_row50_cosetMonodromyBlock1_0007
  · exact g32p_row50_cosetMonodromyBlock1_0008
  · exact g32p_row50_cosetMonodromyBlock1_0009
  · exact g32p_row50_cosetMonodromyBlock1_0010
  · exact g32p_row50_cosetMonodromyBlock1_0011
  · exact g32p_row50_cosetMonodromyBlock1_0012
  · exact g32p_row50_cosetMonodromyBlock1_0013
  · exact g32p_row50_cosetMonodromyBlock1_0014
  · exact g32p_row50_cosetMonodromyBlock1_0015

theorem g32p_row50_cosetActualMonodromy1 (j : Fin 256) :
    (g32p_cosetBranches 1) ^ g32p_row50_cosetLengths1 j * g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots1 j) =
      g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots1 j) *
        (g32p_row50_groupEquiv (g32p_row50_cosetMonodromies1 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row50_cosetBranchMatrices 1)
    (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots1 j))
    (g32p_row50_groupNodes (g32p_row50_cosetMonodromies1 j))
    (g32p_row50_cosetLengths1 j) (g32p_row50_cosetBranchMap 1)
    (g32p_row50_cosetActualRepresentatives_map _) (g32p_row50_groupEquiv_map _)
  exact (g32p_row50_cosetMonodromyCheck1 j).1

theorem g32p_row50_cosetCharacter1 (j : Fin 256) :
    g32p_row50_finiteSupplier.χ (g32p_row50_groupEquiv (g32p_row50_cosetMonodromies1 j)) = g32p_row50_cosetExponents1 j := by
  rw [g32p_row50_finiteSupplier_value]
  exact (g32p_row50_cosetMonodromyCheck1 j).2

theorem g32p_row50_cosetBranchExponents1 :
    papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_cosetBranches 1) =
      (Finset.univ.val.map (fun j : Fin 256 => Multiplicative.toAdd (g32p_row50_cosetExponents1 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row50_cosetOrbitEquiv1
    (fun j => g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots1 j)) (fun _ => rfl) g32p_row50_cosetLengths1 g32p_row50_cosetPeriod1
    (fun j => g32p_row50_groupEquiv (g32p_row50_cosetMonodromies1 j)) g32p_row50_cosetActualMonodromy1]
  simp only [g32p_row50_cosetCharacter1]
  rfl

def g32p_row50_cosetOrbitEquiv2 : Fin 320 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row50_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row50_cosetEquiv
    (g32p_row50_cosetBranchNext 2) (g32p_row50_cosetQuotientStep 2) g32p_row50_cosetLabels2 g32p_row50_cosetRoots2
    g32p_row50_cosetDistances2 g32p_row50_cosetRootLabels2 g32p_row50_cosetNextLabels2 g32p_row50_cosetReach2)

theorem g32p_row50_cosetPeriod2 (j : Fin 320) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row50_cosetEquiv (g32p_row50_cosetRoots2 j)) = g32p_row50_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row50_cosetEquiv (g32p_row50_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row50_cosetQuotientStep 2) _ _ (g32p_row50_cosetPeriods2 j).1 (g32p_row50_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row50_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row50_cosetMonodromyCheck2 (j : Fin 320) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 2) (g32p_row50_cosetLengths2 j))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots2 j)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots2 j))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies2 j)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies2 j) = g32p_row50_cosetExponents2 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row50_cosetMonodromyBlock2_0000
  · exact g32p_row50_cosetMonodromyBlock2_0001
  · exact g32p_row50_cosetMonodromyBlock2_0002
  · exact g32p_row50_cosetMonodromyBlock2_0003
  · exact g32p_row50_cosetMonodromyBlock2_0004
  · exact g32p_row50_cosetMonodromyBlock2_0005
  · exact g32p_row50_cosetMonodromyBlock2_0006
  · exact g32p_row50_cosetMonodromyBlock2_0007
  · exact g32p_row50_cosetMonodromyBlock2_0008
  · exact g32p_row50_cosetMonodromyBlock2_0009
  · exact g32p_row50_cosetMonodromyBlock2_0010
  · exact g32p_row50_cosetMonodromyBlock2_0011
  · exact g32p_row50_cosetMonodromyBlock2_0012
  · exact g32p_row50_cosetMonodromyBlock2_0013
  · exact g32p_row50_cosetMonodromyBlock2_0014
  · exact g32p_row50_cosetMonodromyBlock2_0015
  · exact g32p_row50_cosetMonodromyBlock2_0016
  · exact g32p_row50_cosetMonodromyBlock2_0017
  · exact g32p_row50_cosetMonodromyBlock2_0018
  · exact g32p_row50_cosetMonodromyBlock2_0019

theorem g32p_row50_cosetActualMonodromy2 (j : Fin 320) :
    (g32p_cosetBranches 2) ^ g32p_row50_cosetLengths2 j * g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots2 j) =
      g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots2 j) *
        (g32p_row50_groupEquiv (g32p_row50_cosetMonodromies2 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row50_cosetBranchMatrices 2)
    (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots2 j))
    (g32p_row50_groupNodes (g32p_row50_cosetMonodromies2 j))
    (g32p_row50_cosetLengths2 j) (g32p_row50_cosetBranchMap 2)
    (g32p_row50_cosetActualRepresentatives_map _) (g32p_row50_groupEquiv_map _)
  exact (g32p_row50_cosetMonodromyCheck2 j).1

theorem g32p_row50_cosetCharacter2 (j : Fin 320) :
    g32p_row50_finiteSupplier.χ (g32p_row50_groupEquiv (g32p_row50_cosetMonodromies2 j)) = g32p_row50_cosetExponents2 j := by
  rw [g32p_row50_finiteSupplier_value]
  exact (g32p_row50_cosetMonodromyCheck2 j).2

theorem g32p_row50_cosetBranchExponents2 :
    papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 320 => Multiplicative.toAdd (g32p_row50_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row50_cosetOrbitEquiv2
    (fun j => g32p_row50_cosetActualRepresentatives (g32p_row50_cosetRoots2 j)) (fun _ => rfl) g32p_row50_cosetLengths2 g32p_row50_cosetPeriod2
    (fun j => g32p_row50_groupEquiv (g32p_row50_cosetMonodromies2 j)) g32p_row50_cosetActualMonodromy2]
  simp only [g32p_row50_cosetCharacter2]
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

theorem g32p_row50_exponents :
    (g32p_exponents g32p_row50_finiteSupplier).Perm (expandExps [(1, 288), (2, 288)]) := by
  have h0 : papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_classDatum 0) = (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row50_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 256)).val.map
      (fun j => Multiplicative.toAdd (g32p_row50_cosetExponents0 j))).filter (· ≠ 0) = (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have h1 : papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_classDatum 6) = (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row50_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 256)).val.map
      (fun j => Multiplicative.toAdd (g32p_row50_cosetExponents1 j))).filter (· ≠ 0) = (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have h2 : papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_classDatum 12) = (([] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row50_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 320)).val.map
      (fun j => Multiplicative.toAdd (g32p_row50_cosetExponents2 j))).filter (· ≠ 0) = (([] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have hs : papersExpsTuple g32p_row50_finiteSupplier.H g32p_row50_finiteSupplier.χ g32p_classList =
      6 • (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) + 6 • (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) + (([] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (6 • (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) + 6 • (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) + (([] : List (ZMod 3)) : Multiset (ZMod 3))).map ZMod.val = ↑(expandExps [(1, 288), (2, 288)])
  decide +kernel

theorem g32p_row50_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 50 ∧ r.m = g32p_row50_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row50_finiteSupplier.H ∧
      (g32p_exponents g32p_row50_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨50, 1, 243, 3, 1825, 576, 4224, some 1, [(1, 288), (2, 288)], .S⟩, ?_, rfl, rfl, g32p_row50_finiteSupplier_order.symm, g32p_row50_exponents⟩
  decide

def g32p_row50_complexWitness : g32p_row50_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row50_finiteSupplier

theorem g32p_row50_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 50 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row50_finiteSupplier, g32p_row50_complexWitness, g32p_complexCharacter_apply _,
    g32p_row50_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
