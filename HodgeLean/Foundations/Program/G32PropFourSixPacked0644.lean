import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness04CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0643
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetBranchMatrix0 : g32p_row04_cosetBranchMatrices 0 = g32p_cosetIntegralBranches 0 := by
  decide +kernel

theorem g32p_row04_cosetPartition0 : (g32p_row04_cosetCycles0).flatten.Perm (List.range 90) := by
  decide +kernel

theorem g32p_row04_cosetRootLabels0 : ∀ j : Fin 42, g32p_row04_cosetLabels0 (g32p_row04_cosetRoots0 j) = j := by
  decide +kernel

theorem g32p_row04_cosetNextLabels0 : ∀ i : Fin 90, g32p_row04_cosetLabels0 (g32p_row04_cosetBranchNext 0 i) = g32p_row04_cosetLabels0 i := by
  decide +kernel

theorem g32p_row04_cosetReach0 : ∀ i : Fin 90, (g32p_row04_cosetBranchNext 0)^[g32p_row04_cosetDistances0 i] (g32p_row04_cosetRoots0 (g32p_row04_cosetLabels0 i)) = i := by
  decide +kernel

theorem g32p_row04_cosetPeriods0 : ∀ j : Fin 42, 0 < g32p_row04_cosetLengths0 j ∧ (g32p_row04_cosetBranchNext 0)^[g32p_row04_cosetLengths0 j] (g32p_row04_cosetRoots0 j) = g32p_row04_cosetRoots0 j ∧ ∀ t : Fin (g32p_row04_cosetLengths0 j), 0 < t.val → (g32p_row04_cosetBranchNext 0)^[t.val] (g32p_row04_cosetRoots0 j) ≠ g32p_row04_cosetRoots0 j := by
  decide +kernel

theorem g32p_row04_cosetCycleSteps0 : ∀ cycle ∈ g32p_row04_cosetCycles0,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row04_cosetBranchNext 0 ⟨i % 90, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row04_cosetPermutation0 : Function.Bijective (g32p_row04_cosetBranchNext 0) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetBranchMatrix1 : g32p_row04_cosetBranchMatrices 1 = g32p_cosetIntegralBranches 1 := by
  decide +kernel

theorem g32p_row04_cosetPartition1 : (g32p_row04_cosetCycles1).flatten.Perm (List.range 90) := by
  decide +kernel

theorem g32p_row04_cosetRootLabels1 : ∀ j : Fin 42, g32p_row04_cosetLabels1 (g32p_row04_cosetRoots1 j) = j := by
  decide +kernel

theorem g32p_row04_cosetNextLabels1 : ∀ i : Fin 90, g32p_row04_cosetLabels1 (g32p_row04_cosetBranchNext 1 i) = g32p_row04_cosetLabels1 i := by
  decide +kernel

theorem g32p_row04_cosetReach1 : ∀ i : Fin 90, (g32p_row04_cosetBranchNext 1)^[g32p_row04_cosetDistances1 i] (g32p_row04_cosetRoots1 (g32p_row04_cosetLabels1 i)) = i := by
  decide +kernel

theorem g32p_row04_cosetPeriods1 : ∀ j : Fin 42, 0 < g32p_row04_cosetLengths1 j ∧ (g32p_row04_cosetBranchNext 1)^[g32p_row04_cosetLengths1 j] (g32p_row04_cosetRoots1 j) = g32p_row04_cosetRoots1 j ∧ ∀ t : Fin (g32p_row04_cosetLengths1 j), 0 < t.val → (g32p_row04_cosetBranchNext 1)^[t.val] (g32p_row04_cosetRoots1 j) ≠ g32p_row04_cosetRoots1 j := by
  decide +kernel

theorem g32p_row04_cosetCycleSteps1 : ∀ cycle ∈ g32p_row04_cosetCycles1,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row04_cosetBranchNext 1 ⟨i % 90, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row04_cosetPermutation1 : Function.Bijective (g32p_row04_cosetBranchNext 1) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetBranchMatrix2 : g32p_row04_cosetBranchMatrices 2 = g32p_cosetIntegralBranches 2 := by
  decide +kernel

theorem g32p_row04_cosetPartition2 : (g32p_row04_cosetCycles2).flatten.Perm (List.range 90) := by
  decide +kernel

theorem g32p_row04_cosetRootLabels2 : ∀ j : Fin 46, g32p_row04_cosetLabels2 (g32p_row04_cosetRoots2 j) = j := by
  decide +kernel

theorem g32p_row04_cosetNextLabels2 : ∀ i : Fin 90, g32p_row04_cosetLabels2 (g32p_row04_cosetBranchNext 2 i) = g32p_row04_cosetLabels2 i := by
  decide +kernel

theorem g32p_row04_cosetReach2 : ∀ i : Fin 90, (g32p_row04_cosetBranchNext 2)^[g32p_row04_cosetDistances2 i] (g32p_row04_cosetRoots2 (g32p_row04_cosetLabels2 i)) = i := by
  decide +kernel

theorem g32p_row04_cosetPeriods2 : ∀ j : Fin 46, 0 < g32p_row04_cosetLengths2 j ∧ (g32p_row04_cosetBranchNext 2)^[g32p_row04_cosetLengths2 j] (g32p_row04_cosetRoots2 j) = g32p_row04_cosetRoots2 j ∧ ∀ t : Fin (g32p_row04_cosetLengths2 j), 0 < t.val → (g32p_row04_cosetBranchNext 2)^[t.val] (g32p_row04_cosetRoots2 j) ≠ g32p_row04_cosetRoots2 j := by
  decide +kernel

theorem g32p_row04_cosetCycleSteps2 : ∀ cycle ∈ g32p_row04_cosetCycles2,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row04_cosetBranchNext 2 ⟨i % 90, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row04_cosetPermutation2 : Function.Bijective (g32p_row04_cosetBranchNext 2) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 400000

def g32p_row04_cosetEquiv : Fin 90 ≃ (g32p_G ⧸ g32p_row04_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row04_cosetEnumeration

theorem g32p_row04_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row04_cosetBranchMatrices b)) := by
  have he : g32p_row04_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    fin_cases b
    · exact g32p_row04_cosetBranchMatrix0
    · exact g32p_row04_cosetBranchMatrix1
    · exact g32p_row04_cosetBranchMatrix2
  rw [he]
  exact g32p_cosetBranches_map b

theorem g32p_row04_cosetBranchCheck (b : Fin 3) (i : Fin 90) :
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices b) (g32p_row04_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext b i))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor b i)) := by
  fin_cases i
  · exact g32p_row04_cosetBranchStep_0000 b
  · exact g32p_row04_cosetBranchStep_0001 b
  · exact g32p_row04_cosetBranchStep_0002 b
  · exact g32p_row04_cosetBranchStep_0003 b
  · exact g32p_row04_cosetBranchStep_0004 b
  · exact g32p_row04_cosetBranchStep_0005 b
  · exact g32p_row04_cosetBranchStep_0006 b
  · exact g32p_row04_cosetBranchStep_0007 b
  · exact g32p_row04_cosetBranchStep_0008 b
  · exact g32p_row04_cosetBranchStep_0009 b
  · exact g32p_row04_cosetBranchStep_0010 b
  · exact g32p_row04_cosetBranchStep_0011 b
  · exact g32p_row04_cosetBranchStep_0012 b
  · exact g32p_row04_cosetBranchStep_0013 b
  · exact g32p_row04_cosetBranchStep_0014 b
  · exact g32p_row04_cosetBranchStep_0015 b
  · exact g32p_row04_cosetBranchStep_0016 b
  · exact g32p_row04_cosetBranchStep_0017 b
  · exact g32p_row04_cosetBranchStep_0018 b
  · exact g32p_row04_cosetBranchStep_0019 b
  · exact g32p_row04_cosetBranchStep_0020 b
  · exact g32p_row04_cosetBranchStep_0021 b
  · exact g32p_row04_cosetBranchStep_0022 b
  · exact g32p_row04_cosetBranchStep_0023 b
  · exact g32p_row04_cosetBranchStep_0024 b
  · exact g32p_row04_cosetBranchStep_0025 b
  · exact g32p_row04_cosetBranchStep_0026 b
  · exact g32p_row04_cosetBranchStep_0027 b
  · exact g32p_row04_cosetBranchStep_0028 b
  · exact g32p_row04_cosetBranchStep_0029 b
  · exact g32p_row04_cosetBranchStep_0030 b
  · exact g32p_row04_cosetBranchStep_0031 b
  · exact g32p_row04_cosetBranchStep_0032 b
  · exact g32p_row04_cosetBranchStep_0033 b
  · exact g32p_row04_cosetBranchStep_0034 b
  · exact g32p_row04_cosetBranchStep_0035 b
  · exact g32p_row04_cosetBranchStep_0036 b
  · exact g32p_row04_cosetBranchStep_0037 b
  · exact g32p_row04_cosetBranchStep_0038 b
  · exact g32p_row04_cosetBranchStep_0039 b
  · exact g32p_row04_cosetBranchStep_0040 b
  · exact g32p_row04_cosetBranchStep_0041 b
  · exact g32p_row04_cosetBranchStep_0042 b
  · exact g32p_row04_cosetBranchStep_0043 b
  · exact g32p_row04_cosetBranchStep_0044 b
  · exact g32p_row04_cosetBranchStep_0045 b
  · exact g32p_row04_cosetBranchStep_0046 b
  · exact g32p_row04_cosetBranchStep_0047 b
  · exact g32p_row04_cosetBranchStep_0048 b
  · exact g32p_row04_cosetBranchStep_0049 b
  · exact g32p_row04_cosetBranchStep_0050 b
  · exact g32p_row04_cosetBranchStep_0051 b
  · exact g32p_row04_cosetBranchStep_0052 b
  · exact g32p_row04_cosetBranchStep_0053 b
  · exact g32p_row04_cosetBranchStep_0054 b
  · exact g32p_row04_cosetBranchStep_0055 b
  · exact g32p_row04_cosetBranchStep_0056 b
  · exact g32p_row04_cosetBranchStep_0057 b
  · exact g32p_row04_cosetBranchStep_0058 b
  · exact g32p_row04_cosetBranchStep_0059 b
  · exact g32p_row04_cosetBranchStep_0060 b
  · exact g32p_row04_cosetBranchStep_0061 b
  · exact g32p_row04_cosetBranchStep_0062 b
  · exact g32p_row04_cosetBranchStep_0063 b
  · exact g32p_row04_cosetBranchStep_0064 b
  · exact g32p_row04_cosetBranchStep_0065 b
  · exact g32p_row04_cosetBranchStep_0066 b
  · exact g32p_row04_cosetBranchStep_0067 b
  · exact g32p_row04_cosetBranchStep_0068 b
  · exact g32p_row04_cosetBranchStep_0069 b
  · exact g32p_row04_cosetBranchStep_0070 b
  · exact g32p_row04_cosetBranchStep_0071 b
  · exact g32p_row04_cosetBranchStep_0072 b
  · exact g32p_row04_cosetBranchStep_0073 b
  · exact g32p_row04_cosetBranchStep_0074 b
  · exact g32p_row04_cosetBranchStep_0075 b
  · exact g32p_row04_cosetBranchStep_0076 b
  · exact g32p_row04_cosetBranchStep_0077 b
  · exact g32p_row04_cosetBranchStep_0078 b
  · exact g32p_row04_cosetBranchStep_0079 b
  · exact g32p_row04_cosetBranchStep_0080 b
  · exact g32p_row04_cosetBranchStep_0081 b
  · exact g32p_row04_cosetBranchStep_0082 b
  · exact g32p_row04_cosetBranchStep_0083 b
  · exact g32p_row04_cosetBranchStep_0084 b
  · exact g32p_row04_cosetBranchStep_0085 b
  · exact g32p_row04_cosetBranchStep_0086 b
  · exact g32p_row04_cosetBranchStep_0087 b
  · exact g32p_row04_cosetBranchStep_0088 b
  · exact g32p_row04_cosetBranchStep_0089 b

theorem g32p_row04_cosetActualBranchStep (b : Fin 3) (i : Fin 90) :
    g32p_cosetBranches b * g32p_row04_cosetActualRepresentatives i =
      g32p_row04_cosetActualRepresentatives (g32p_row04_cosetBranchNext b i) *
        (g32p_row04_groupEquiv (g32p_row04_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row04_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row04_cosetActualRepresentatives (g32p_row04_cosetBranchNext b i) *
      (g32p_row04_groupEquiv (g32p_row04_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row04_cosetBranchMap, g32p_row04_cosetActualRepresentatives_map,
    g32p_row04_cosetActualRepresentatives_map, g32p_row04_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row04_cosetBranchCheck]

theorem g32p_row04_cosetQuotientStep (b : Fin 3) (i : Fin 90) :
    g32p_row04_cosetEquiv (g32p_row04_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row04_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row04_cosetActualRepresentatives (g32p_row04_cosetBranchNext b i)) : g32p_G ⧸ g32p_row04_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row04_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row04_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row04_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row04_groupEquiv (g32p_row04_cosetBranchFactor b i)).property

def g32p_row04_cosetOrbitEquiv0 : Fin 42 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 0)) (g32p_G ⧸ g32p_row04_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 0) g32p_row04_cosetEquiv
    (g32p_row04_cosetBranchNext 0) (g32p_row04_cosetQuotientStep 0) g32p_row04_cosetLabels0 g32p_row04_cosetRoots0
    g32p_row04_cosetDistances0 g32p_row04_cosetRootLabels0 g32p_row04_cosetNextLabels0 g32p_row04_cosetReach0)

theorem g32p_row04_cosetPeriod0 (j : Fin 42) :
    Function.minimalPeriod ((g32p_cosetBranches 0) • ·) (g32p_row04_cosetEquiv (g32p_row04_cosetRoots0 j)) = g32p_row04_cosetLengths0 j := by
  apply g32p_period_of_cycle g32p_row04_cosetEquiv (g32p_row04_cosetBranchNext 0) ((g32p_cosetBranches 0) • ·)
    (g32p_row04_cosetQuotientStep 0) _ _ (g32p_row04_cosetPeriods0 j).1 (g32p_row04_cosetPeriods0 j).2.1
  intro t ht hlt
  exact (g32p_row04_cosetPeriods0 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row04_cosetActualMonodromy0 (j : Fin 42) :
    (g32p_cosetBranches 0) ^ g32p_row04_cosetLengths0 j * g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots0 j) =
      g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots0 j) *
        (g32p_row04_groupEquiv (g32p_row04_cosetMonodromies0 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row04_cosetBranchMatrices 0)
    (g32p_row04_cosetRepresentatives (g32p_row04_cosetRoots0 j))
    (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 j))
    (g32p_row04_cosetLengths0 j) (g32p_row04_cosetBranchMap 0)
    (g32p_row04_cosetActualRepresentatives_map _) (g32p_row04_groupEquiv_map _)
  fin_cases j
  · exact g32p_row04_cosetMonodromy_0_0000.1
  · exact g32p_row04_cosetMonodromy_0_0001.1
  · exact g32p_row04_cosetMonodromy_0_0002.1
  · exact g32p_row04_cosetMonodromy_0_0003.1
  · exact g32p_row04_cosetMonodromy_0_0004.1
  · exact g32p_row04_cosetMonodromy_0_0005.1
  · exact g32p_row04_cosetMonodromy_0_0006.1
  · exact g32p_row04_cosetMonodromy_0_0007.1
  · exact g32p_row04_cosetMonodromy_0_0008.1
  · exact g32p_row04_cosetMonodromy_0_0009.1
  · exact g32p_row04_cosetMonodromy_0_0010.1
  · exact g32p_row04_cosetMonodromy_0_0011.1
  · exact g32p_row04_cosetMonodromy_0_0012.1
  · exact g32p_row04_cosetMonodromy_0_0013.1
  · exact g32p_row04_cosetMonodromy_0_0014.1
  · exact g32p_row04_cosetMonodromy_0_0015.1
  · exact g32p_row04_cosetMonodromy_0_0016.1
  · exact g32p_row04_cosetMonodromy_0_0017.1
  · exact g32p_row04_cosetMonodromy_0_0018.1
  · exact g32p_row04_cosetMonodromy_0_0019.1
  · exact g32p_row04_cosetMonodromy_0_0020.1
  · exact g32p_row04_cosetMonodromy_0_0021.1
  · exact g32p_row04_cosetMonodromy_0_0022.1
  · exact g32p_row04_cosetMonodromy_0_0023.1
  · exact g32p_row04_cosetMonodromy_0_0024.1
  · exact g32p_row04_cosetMonodromy_0_0025.1
  · exact g32p_row04_cosetMonodromy_0_0026.1
  · exact g32p_row04_cosetMonodromy_0_0027.1
  · exact g32p_row04_cosetMonodromy_0_0028.1
  · exact g32p_row04_cosetMonodromy_0_0029.1
  · exact g32p_row04_cosetMonodromy_0_0030.1
  · exact g32p_row04_cosetMonodromy_0_0031.1
  · exact g32p_row04_cosetMonodromy_0_0032.1
  · exact g32p_row04_cosetMonodromy_0_0033.1
  · exact g32p_row04_cosetMonodromy_0_0034.1
  · exact g32p_row04_cosetMonodromy_0_0035.1
  · exact g32p_row04_cosetMonodromy_0_0036.1
  · exact g32p_row04_cosetMonodromy_0_0037.1
  · exact g32p_row04_cosetMonodromy_0_0038.1
  · exact g32p_row04_cosetMonodromy_0_0039.1
  · exact g32p_row04_cosetMonodromy_0_0040.1
  · exact g32p_row04_cosetMonodromy_0_0041.1

theorem g32p_row04_cosetCharacter0 (j : Fin 42) :
    g32p_row04_finiteSupplier.χ (g32p_row04_groupEquiv (g32p_row04_cosetMonodromies0 j)) = g32p_row04_cosetExponents0 j := by
  rw [g32p_row04_finiteSupplier_value]
  fin_cases j
  · exact g32p_row04_cosetMonodromy_0_0000.2
  · exact g32p_row04_cosetMonodromy_0_0001.2
  · exact g32p_row04_cosetMonodromy_0_0002.2
  · exact g32p_row04_cosetMonodromy_0_0003.2
  · exact g32p_row04_cosetMonodromy_0_0004.2
  · exact g32p_row04_cosetMonodromy_0_0005.2
  · exact g32p_row04_cosetMonodromy_0_0006.2
  · exact g32p_row04_cosetMonodromy_0_0007.2
  · exact g32p_row04_cosetMonodromy_0_0008.2
  · exact g32p_row04_cosetMonodromy_0_0009.2
  · exact g32p_row04_cosetMonodromy_0_0010.2
  · exact g32p_row04_cosetMonodromy_0_0011.2
  · exact g32p_row04_cosetMonodromy_0_0012.2
  · exact g32p_row04_cosetMonodromy_0_0013.2
  · exact g32p_row04_cosetMonodromy_0_0014.2
  · exact g32p_row04_cosetMonodromy_0_0015.2
  · exact g32p_row04_cosetMonodromy_0_0016.2
  · exact g32p_row04_cosetMonodromy_0_0017.2
  · exact g32p_row04_cosetMonodromy_0_0018.2
  · exact g32p_row04_cosetMonodromy_0_0019.2
  · exact g32p_row04_cosetMonodromy_0_0020.2
  · exact g32p_row04_cosetMonodromy_0_0021.2
  · exact g32p_row04_cosetMonodromy_0_0022.2
  · exact g32p_row04_cosetMonodromy_0_0023.2
  · exact g32p_row04_cosetMonodromy_0_0024.2
  · exact g32p_row04_cosetMonodromy_0_0025.2
  · exact g32p_row04_cosetMonodromy_0_0026.2
  · exact g32p_row04_cosetMonodromy_0_0027.2
  · exact g32p_row04_cosetMonodromy_0_0028.2
  · exact g32p_row04_cosetMonodromy_0_0029.2
  · exact g32p_row04_cosetMonodromy_0_0030.2
  · exact g32p_row04_cosetMonodromy_0_0031.2
  · exact g32p_row04_cosetMonodromy_0_0032.2
  · exact g32p_row04_cosetMonodromy_0_0033.2
  · exact g32p_row04_cosetMonodromy_0_0034.2
  · exact g32p_row04_cosetMonodromy_0_0035.2
  · exact g32p_row04_cosetMonodromy_0_0036.2
  · exact g32p_row04_cosetMonodromy_0_0037.2
  · exact g32p_row04_cosetMonodromy_0_0038.2
  · exact g32p_row04_cosetMonodromy_0_0039.2
  · exact g32p_row04_cosetMonodromy_0_0040.2
  · exact g32p_row04_cosetMonodromy_0_0041.2

theorem g32p_row04_cosetBranchExponents0 :
    papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_cosetBranches 0) =
      (Finset.univ.val.map (fun j : Fin 42 => Multiplicative.toAdd (g32p_row04_cosetExponents0 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row04_cosetOrbitEquiv0
    (fun j => g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots0 j)) (fun _ => rfl) g32p_row04_cosetLengths0 g32p_row04_cosetPeriod0
    (fun j => g32p_row04_groupEquiv (g32p_row04_cosetMonodromies0 j)) g32p_row04_cosetActualMonodromy0]
  simp only [g32p_row04_cosetCharacter0]
  rfl

def g32p_row04_cosetOrbitEquiv1 : Fin 42 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 1)) (g32p_G ⧸ g32p_row04_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 1) g32p_row04_cosetEquiv
    (g32p_row04_cosetBranchNext 1) (g32p_row04_cosetQuotientStep 1) g32p_row04_cosetLabels1 g32p_row04_cosetRoots1
    g32p_row04_cosetDistances1 g32p_row04_cosetRootLabels1 g32p_row04_cosetNextLabels1 g32p_row04_cosetReach1)

theorem g32p_row04_cosetPeriod1 (j : Fin 42) :
    Function.minimalPeriod ((g32p_cosetBranches 1) • ·) (g32p_row04_cosetEquiv (g32p_row04_cosetRoots1 j)) = g32p_row04_cosetLengths1 j := by
  apply g32p_period_of_cycle g32p_row04_cosetEquiv (g32p_row04_cosetBranchNext 1) ((g32p_cosetBranches 1) • ·)
    (g32p_row04_cosetQuotientStep 1) _ _ (g32p_row04_cosetPeriods1 j).1 (g32p_row04_cosetPeriods1 j).2.1
  intro t ht hlt
  exact (g32p_row04_cosetPeriods1 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row04_cosetActualMonodromy1 (j : Fin 42) :
    (g32p_cosetBranches 1) ^ g32p_row04_cosetLengths1 j * g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots1 j) =
      g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots1 j) *
        (g32p_row04_groupEquiv (g32p_row04_cosetMonodromies1 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row04_cosetBranchMatrices 1)
    (g32p_row04_cosetRepresentatives (g32p_row04_cosetRoots1 j))
    (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 j))
    (g32p_row04_cosetLengths1 j) (g32p_row04_cosetBranchMap 1)
    (g32p_row04_cosetActualRepresentatives_map _) (g32p_row04_groupEquiv_map _)
  fin_cases j
  · exact g32p_row04_cosetMonodromy_1_0000.1
  · exact g32p_row04_cosetMonodromy_1_0001.1
  · exact g32p_row04_cosetMonodromy_1_0002.1
  · exact g32p_row04_cosetMonodromy_1_0003.1
  · exact g32p_row04_cosetMonodromy_1_0004.1
  · exact g32p_row04_cosetMonodromy_1_0005.1
  · exact g32p_row04_cosetMonodromy_1_0006.1
  · exact g32p_row04_cosetMonodromy_1_0007.1
  · exact g32p_row04_cosetMonodromy_1_0008.1
  · exact g32p_row04_cosetMonodromy_1_0009.1
  · exact g32p_row04_cosetMonodromy_1_0010.1
  · exact g32p_row04_cosetMonodromy_1_0011.1
  · exact g32p_row04_cosetMonodromy_1_0012.1
  · exact g32p_row04_cosetMonodromy_1_0013.1
  · exact g32p_row04_cosetMonodromy_1_0014.1
  · exact g32p_row04_cosetMonodromy_1_0015.1
  · exact g32p_row04_cosetMonodromy_1_0016.1
  · exact g32p_row04_cosetMonodromy_1_0017.1
  · exact g32p_row04_cosetMonodromy_1_0018.1
  · exact g32p_row04_cosetMonodromy_1_0019.1
  · exact g32p_row04_cosetMonodromy_1_0020.1
  · exact g32p_row04_cosetMonodromy_1_0021.1
  · exact g32p_row04_cosetMonodromy_1_0022.1
  · exact g32p_row04_cosetMonodromy_1_0023.1
  · exact g32p_row04_cosetMonodromy_1_0024.1
  · exact g32p_row04_cosetMonodromy_1_0025.1
  · exact g32p_row04_cosetMonodromy_1_0026.1
  · exact g32p_row04_cosetMonodromy_1_0027.1
  · exact g32p_row04_cosetMonodromy_1_0028.1
  · exact g32p_row04_cosetMonodromy_1_0029.1
  · exact g32p_row04_cosetMonodromy_1_0030.1
  · exact g32p_row04_cosetMonodromy_1_0031.1
  · exact g32p_row04_cosetMonodromy_1_0032.1
  · exact g32p_row04_cosetMonodromy_1_0033.1
  · exact g32p_row04_cosetMonodromy_1_0034.1
  · exact g32p_row04_cosetMonodromy_1_0035.1
  · exact g32p_row04_cosetMonodromy_1_0036.1
  · exact g32p_row04_cosetMonodromy_1_0037.1
  · exact g32p_row04_cosetMonodromy_1_0038.1
  · exact g32p_row04_cosetMonodromy_1_0039.1
  · exact g32p_row04_cosetMonodromy_1_0040.1
  · exact g32p_row04_cosetMonodromy_1_0041.1

theorem g32p_row04_cosetCharacter1 (j : Fin 42) :
    g32p_row04_finiteSupplier.χ (g32p_row04_groupEquiv (g32p_row04_cosetMonodromies1 j)) = g32p_row04_cosetExponents1 j := by
  rw [g32p_row04_finiteSupplier_value]
  fin_cases j
  · exact g32p_row04_cosetMonodromy_1_0000.2
  · exact g32p_row04_cosetMonodromy_1_0001.2
  · exact g32p_row04_cosetMonodromy_1_0002.2
  · exact g32p_row04_cosetMonodromy_1_0003.2
  · exact g32p_row04_cosetMonodromy_1_0004.2
  · exact g32p_row04_cosetMonodromy_1_0005.2
  · exact g32p_row04_cosetMonodromy_1_0006.2
  · exact g32p_row04_cosetMonodromy_1_0007.2
  · exact g32p_row04_cosetMonodromy_1_0008.2
  · exact g32p_row04_cosetMonodromy_1_0009.2
  · exact g32p_row04_cosetMonodromy_1_0010.2
  · exact g32p_row04_cosetMonodromy_1_0011.2
  · exact g32p_row04_cosetMonodromy_1_0012.2
  · exact g32p_row04_cosetMonodromy_1_0013.2
  · exact g32p_row04_cosetMonodromy_1_0014.2
  · exact g32p_row04_cosetMonodromy_1_0015.2
  · exact g32p_row04_cosetMonodromy_1_0016.2
  · exact g32p_row04_cosetMonodromy_1_0017.2
  · exact g32p_row04_cosetMonodromy_1_0018.2
  · exact g32p_row04_cosetMonodromy_1_0019.2
  · exact g32p_row04_cosetMonodromy_1_0020.2
  · exact g32p_row04_cosetMonodromy_1_0021.2
  · exact g32p_row04_cosetMonodromy_1_0022.2
  · exact g32p_row04_cosetMonodromy_1_0023.2
  · exact g32p_row04_cosetMonodromy_1_0024.2
  · exact g32p_row04_cosetMonodromy_1_0025.2
  · exact g32p_row04_cosetMonodromy_1_0026.2
  · exact g32p_row04_cosetMonodromy_1_0027.2
  · exact g32p_row04_cosetMonodromy_1_0028.2
  · exact g32p_row04_cosetMonodromy_1_0029.2
  · exact g32p_row04_cosetMonodromy_1_0030.2
  · exact g32p_row04_cosetMonodromy_1_0031.2
  · exact g32p_row04_cosetMonodromy_1_0032.2
  · exact g32p_row04_cosetMonodromy_1_0033.2
  · exact g32p_row04_cosetMonodromy_1_0034.2
  · exact g32p_row04_cosetMonodromy_1_0035.2
  · exact g32p_row04_cosetMonodromy_1_0036.2
  · exact g32p_row04_cosetMonodromy_1_0037.2
  · exact g32p_row04_cosetMonodromy_1_0038.2
  · exact g32p_row04_cosetMonodromy_1_0039.2
  · exact g32p_row04_cosetMonodromy_1_0040.2
  · exact g32p_row04_cosetMonodromy_1_0041.2

theorem g32p_row04_cosetBranchExponents1 :
    papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_cosetBranches 1) =
      (Finset.univ.val.map (fun j : Fin 42 => Multiplicative.toAdd (g32p_row04_cosetExponents1 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row04_cosetOrbitEquiv1
    (fun j => g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots1 j)) (fun _ => rfl) g32p_row04_cosetLengths1 g32p_row04_cosetPeriod1
    (fun j => g32p_row04_groupEquiv (g32p_row04_cosetMonodromies1 j)) g32p_row04_cosetActualMonodromy1]
  simp only [g32p_row04_cosetCharacter1]
  rfl

def g32p_row04_cosetOrbitEquiv2 : Fin 46 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row04_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row04_cosetEquiv
    (g32p_row04_cosetBranchNext 2) (g32p_row04_cosetQuotientStep 2) g32p_row04_cosetLabels2 g32p_row04_cosetRoots2
    g32p_row04_cosetDistances2 g32p_row04_cosetRootLabels2 g32p_row04_cosetNextLabels2 g32p_row04_cosetReach2)

theorem g32p_row04_cosetPeriod2 (j : Fin 46) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row04_cosetEquiv (g32p_row04_cosetRoots2 j)) = g32p_row04_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row04_cosetEquiv (g32p_row04_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row04_cosetQuotientStep 2) _ _ (g32p_row04_cosetPeriods2 j).1 (g32p_row04_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row04_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row04_cosetActualMonodromy2 (j : Fin 46) :
    (g32p_cosetBranches 2) ^ g32p_row04_cosetLengths2 j * g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots2 j) =
      g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots2 j) *
        (g32p_row04_groupEquiv (g32p_row04_cosetMonodromies2 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row04_cosetBranchMatrices 2)
    (g32p_row04_cosetRepresentatives (g32p_row04_cosetRoots2 j))
    (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 j))
    (g32p_row04_cosetLengths2 j) (g32p_row04_cosetBranchMap 2)
    (g32p_row04_cosetActualRepresentatives_map _) (g32p_row04_groupEquiv_map _)
  fin_cases j
  · exact g32p_row04_cosetMonodromy_2_0000.1
  · exact g32p_row04_cosetMonodromy_2_0001.1
  · exact g32p_row04_cosetMonodromy_2_0002.1
  · exact g32p_row04_cosetMonodromy_2_0003.1
  · exact g32p_row04_cosetMonodromy_2_0004.1
  · exact g32p_row04_cosetMonodromy_2_0005.1
  · exact g32p_row04_cosetMonodromy_2_0006.1
  · exact g32p_row04_cosetMonodromy_2_0007.1
  · exact g32p_row04_cosetMonodromy_2_0008.1
  · exact g32p_row04_cosetMonodromy_2_0009.1
  · exact g32p_row04_cosetMonodromy_2_0010.1
  · exact g32p_row04_cosetMonodromy_2_0011.1
  · exact g32p_row04_cosetMonodromy_2_0012.1
  · exact g32p_row04_cosetMonodromy_2_0013.1
  · exact g32p_row04_cosetMonodromy_2_0014.1
  · exact g32p_row04_cosetMonodromy_2_0015.1
  · exact g32p_row04_cosetMonodromy_2_0016.1
  · exact g32p_row04_cosetMonodromy_2_0017.1
  · exact g32p_row04_cosetMonodromy_2_0018.1
  · exact g32p_row04_cosetMonodromy_2_0019.1
  · exact g32p_row04_cosetMonodromy_2_0020.1
  · exact g32p_row04_cosetMonodromy_2_0021.1
  · exact g32p_row04_cosetMonodromy_2_0022.1
  · exact g32p_row04_cosetMonodromy_2_0023.1
  · exact g32p_row04_cosetMonodromy_2_0024.1
  · exact g32p_row04_cosetMonodromy_2_0025.1
  · exact g32p_row04_cosetMonodromy_2_0026.1
  · exact g32p_row04_cosetMonodromy_2_0027.1
  · exact g32p_row04_cosetMonodromy_2_0028.1
  · exact g32p_row04_cosetMonodromy_2_0029.1
  · exact g32p_row04_cosetMonodromy_2_0030.1
  · exact g32p_row04_cosetMonodromy_2_0031.1
  · exact g32p_row04_cosetMonodromy_2_0032.1
  · exact g32p_row04_cosetMonodromy_2_0033.1
  · exact g32p_row04_cosetMonodromy_2_0034.1
  · exact g32p_row04_cosetMonodromy_2_0035.1
  · exact g32p_row04_cosetMonodromy_2_0036.1
  · exact g32p_row04_cosetMonodromy_2_0037.1
  · exact g32p_row04_cosetMonodromy_2_0038.1
  · exact g32p_row04_cosetMonodromy_2_0039.1
  · exact g32p_row04_cosetMonodromy_2_0040.1
  · exact g32p_row04_cosetMonodromy_2_0041.1
  · exact g32p_row04_cosetMonodromy_2_0042.1
  · exact g32p_row04_cosetMonodromy_2_0043.1
  · exact g32p_row04_cosetMonodromy_2_0044.1
  · exact g32p_row04_cosetMonodromy_2_0045.1

theorem g32p_row04_cosetCharacter2 (j : Fin 46) :
    g32p_row04_finiteSupplier.χ (g32p_row04_groupEquiv (g32p_row04_cosetMonodromies2 j)) = g32p_row04_cosetExponents2 j := by
  rw [g32p_row04_finiteSupplier_value]
  fin_cases j
  · exact g32p_row04_cosetMonodromy_2_0000.2
  · exact g32p_row04_cosetMonodromy_2_0001.2
  · exact g32p_row04_cosetMonodromy_2_0002.2
  · exact g32p_row04_cosetMonodromy_2_0003.2
  · exact g32p_row04_cosetMonodromy_2_0004.2
  · exact g32p_row04_cosetMonodromy_2_0005.2
  · exact g32p_row04_cosetMonodromy_2_0006.2
  · exact g32p_row04_cosetMonodromy_2_0007.2
  · exact g32p_row04_cosetMonodromy_2_0008.2
  · exact g32p_row04_cosetMonodromy_2_0009.2
  · exact g32p_row04_cosetMonodromy_2_0010.2
  · exact g32p_row04_cosetMonodromy_2_0011.2
  · exact g32p_row04_cosetMonodromy_2_0012.2
  · exact g32p_row04_cosetMonodromy_2_0013.2
  · exact g32p_row04_cosetMonodromy_2_0014.2
  · exact g32p_row04_cosetMonodromy_2_0015.2
  · exact g32p_row04_cosetMonodromy_2_0016.2
  · exact g32p_row04_cosetMonodromy_2_0017.2
  · exact g32p_row04_cosetMonodromy_2_0018.2
  · exact g32p_row04_cosetMonodromy_2_0019.2
  · exact g32p_row04_cosetMonodromy_2_0020.2
  · exact g32p_row04_cosetMonodromy_2_0021.2
  · exact g32p_row04_cosetMonodromy_2_0022.2
  · exact g32p_row04_cosetMonodromy_2_0023.2
  · exact g32p_row04_cosetMonodromy_2_0024.2
  · exact g32p_row04_cosetMonodromy_2_0025.2
  · exact g32p_row04_cosetMonodromy_2_0026.2
  · exact g32p_row04_cosetMonodromy_2_0027.2
  · exact g32p_row04_cosetMonodromy_2_0028.2
  · exact g32p_row04_cosetMonodromy_2_0029.2
  · exact g32p_row04_cosetMonodromy_2_0030.2
  · exact g32p_row04_cosetMonodromy_2_0031.2
  · exact g32p_row04_cosetMonodromy_2_0032.2
  · exact g32p_row04_cosetMonodromy_2_0033.2
  · exact g32p_row04_cosetMonodromy_2_0034.2
  · exact g32p_row04_cosetMonodromy_2_0035.2
  · exact g32p_row04_cosetMonodromy_2_0036.2
  · exact g32p_row04_cosetMonodromy_2_0037.2
  · exact g32p_row04_cosetMonodromy_2_0038.2
  · exact g32p_row04_cosetMonodromy_2_0039.2
  · exact g32p_row04_cosetMonodromy_2_0040.2
  · exact g32p_row04_cosetMonodromy_2_0041.2
  · exact g32p_row04_cosetMonodromy_2_0042.2
  · exact g32p_row04_cosetMonodromy_2_0043.2
  · exact g32p_row04_cosetMonodromy_2_0044.2
  · exact g32p_row04_cosetMonodromy_2_0045.2

theorem g32p_row04_cosetBranchExponents2 :
    papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 46 => Multiplicative.toAdd (g32p_row04_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row04_cosetOrbitEquiv2
    (fun j => g32p_row04_cosetActualRepresentatives (g32p_row04_cosetRoots2 j)) (fun _ => rfl) g32p_row04_cosetLengths2 g32p_row04_cosetPeriod2
    (fun j => g32p_row04_groupEquiv (g32p_row04_cosetMonodromies2 j)) g32p_row04_cosetActualMonodromy2]
  simp only [g32p_row04_cosetCharacter2]
  rfl

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row04_exponents :
    (g32p_exponents g32p_row04_finiteSupplier).Perm (expandExps [(1, 54), (2, 54)]) := by
  have h0 : papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_classDatum 0) = (([1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row04_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 42)).val.map
      (fun j => Multiplicative.toAdd (g32p_row04_cosetExponents0 j))).filter (· ≠ 0) = (([1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have h1 : papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_classDatum 6) = (([2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row04_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 42)).val.map
      (fun j => Multiplicative.toAdd (g32p_row04_cosetExponents1 j))).filter (· ≠ 0) = (([2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have h2 : papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_classDatum 12) = (([] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    change papersExps g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row04_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 46)).val.map
      (fun j => Multiplicative.toAdd (g32p_row04_cosetExponents2 j))).filter (· ≠ 0) = (([] : List (ZMod 3)) : Multiset (ZMod 3))
    decide +kernel
  have hs : papersExpsTuple g32p_row04_finiteSupplier.H g32p_row04_finiteSupplier.χ g32p_classList =
      6 • (([1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) + 6 • (([2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) + (([] : List (ZMod 3)) : Multiset (ZMod 3)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (6 • (([1, 1, 1, 1, 1, 1, 1, 1, 1] : List (ZMod 3)) : Multiset (ZMod 3)) + 6 • (([2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 3)) : Multiset (ZMod 3)) + (([] : List (ZMod 3)) : Multiset (ZMod 3))).map ZMod.val = ↑(expandExps [(1, 54), (2, 54)])
  decide +kernel

theorem g32p_row04_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 4 ∧ r.m = g32p_row04_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row04_finiteSupplier.H ∧
      (g32p_exponents g32p_row04_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨4, 1, 1728, 3, 221, 108, 548, some 1, [(1, 54), (2, 54)], .S⟩, ?_, rfl, rfl, g32p_row04_finiteSupplier_order.symm, g32p_row04_exponents⟩
  decide

def g32p_row04_complexWitness : g32p_row04_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row04_finiteSupplier

theorem g32p_row04_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 4 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row04_finiteSupplier, g32p_row04_complexWitness, g32p_complexCharacter_apply _,
    g32p_row04_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
