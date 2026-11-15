import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness03CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixPacked0638
import HodgeLean.Foundations.Program.G32PropFourSixPacked0639
import HodgeLean.Foundations.Program.G32PropFourSixPacked0640
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_2_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 2) (HurwitzPrymRex_mone)) (g32p_row03_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 24)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies2 19)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies2 19) = g32p_row03_cosetExponents2 19 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_2_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row03_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 26)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies2 20)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies2 20) = g32p_row03_cosetExponents2 20 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_2_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row03_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 27)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies2 21)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies2 21) = g32p_row03_cosetExponents2 21 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_2_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row03_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 29)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies2 22)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies2 22) = g32p_row03_cosetExponents2 22 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_2_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 2) (HurwitzPrymRex_mone)) (g32p_row03_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 34)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies2 23)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies2 23) = g32p_row03_cosetExponents2 23 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetBranchMatrix0 : g32p_row03_cosetBranchMatrices 0 = g32p_cosetIntegralBranches 0 := by
  decide +kernel

theorem g32p_row03_cosetPartition0 : (g32p_row03_cosetCycles0).flatten.Perm (List.range 36) := by
  decide +kernel

theorem g32p_row03_cosetRootLabels0 : ∀ j : Fin 12, g32p_row03_cosetLabels0 (g32p_row03_cosetRoots0 j) = j := by
  decide +kernel

theorem g32p_row03_cosetNextLabels0 : ∀ i : Fin 36, g32p_row03_cosetLabels0 (g32p_row03_cosetBranchNext 0 i) = g32p_row03_cosetLabels0 i := by
  decide +kernel

theorem g32p_row03_cosetReach0 : ∀ i : Fin 36, (g32p_row03_cosetBranchNext 0)^[g32p_row03_cosetDistances0 i] (g32p_row03_cosetRoots0 (g32p_row03_cosetLabels0 i)) = i := by
  decide +kernel

theorem g32p_row03_cosetPeriods0 : ∀ j : Fin 12, 0 < g32p_row03_cosetLengths0 j ∧ (g32p_row03_cosetBranchNext 0)^[g32p_row03_cosetLengths0 j] (g32p_row03_cosetRoots0 j) = g32p_row03_cosetRoots0 j ∧ ∀ t : Fin (g32p_row03_cosetLengths0 j), 0 < t.val → (g32p_row03_cosetBranchNext 0)^[t.val] (g32p_row03_cosetRoots0 j) ≠ g32p_row03_cosetRoots0 j := by
  decide +kernel

theorem g32p_row03_cosetCycleSteps0 : ∀ cycle ∈ g32p_row03_cosetCycles0,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row03_cosetBranchNext 0 ⟨i % 36, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row03_cosetPermutation0 : Function.Bijective (g32p_row03_cosetBranchNext 0) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetBranchMatrix1 : g32p_row03_cosetBranchMatrices 1 = g32p_cosetIntegralBranches 1 := by
  decide +kernel

theorem g32p_row03_cosetPartition1 : (g32p_row03_cosetCycles1).flatten.Perm (List.range 36) := by
  decide +kernel

theorem g32p_row03_cosetRootLabels1 : ∀ j : Fin 12, g32p_row03_cosetLabels1 (g32p_row03_cosetRoots1 j) = j := by
  decide +kernel

theorem g32p_row03_cosetNextLabels1 : ∀ i : Fin 36, g32p_row03_cosetLabels1 (g32p_row03_cosetBranchNext 1 i) = g32p_row03_cosetLabels1 i := by
  decide +kernel

theorem g32p_row03_cosetReach1 : ∀ i : Fin 36, (g32p_row03_cosetBranchNext 1)^[g32p_row03_cosetDistances1 i] (g32p_row03_cosetRoots1 (g32p_row03_cosetLabels1 i)) = i := by
  decide +kernel

theorem g32p_row03_cosetPeriods1 : ∀ j : Fin 12, 0 < g32p_row03_cosetLengths1 j ∧ (g32p_row03_cosetBranchNext 1)^[g32p_row03_cosetLengths1 j] (g32p_row03_cosetRoots1 j) = g32p_row03_cosetRoots1 j ∧ ∀ t : Fin (g32p_row03_cosetLengths1 j), 0 < t.val → (g32p_row03_cosetBranchNext 1)^[t.val] (g32p_row03_cosetRoots1 j) ≠ g32p_row03_cosetRoots1 j := by
  decide +kernel

theorem g32p_row03_cosetCycleSteps1 : ∀ cycle ∈ g32p_row03_cosetCycles1,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row03_cosetBranchNext 1 ⟨i % 36, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row03_cosetPermutation1 : Function.Bijective (g32p_row03_cosetBranchNext 1) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetBranchMatrix2 : g32p_row03_cosetBranchMatrices 2 = g32p_cosetIntegralBranches 2 := by
  decide +kernel

theorem g32p_row03_cosetPartition2 : (g32p_row03_cosetCycles2).flatten.Perm (List.range 36) := by
  decide +kernel

theorem g32p_row03_cosetRootLabels2 : ∀ j : Fin 24, g32p_row03_cosetLabels2 (g32p_row03_cosetRoots2 j) = j := by
  decide +kernel

theorem g32p_row03_cosetNextLabels2 : ∀ i : Fin 36, g32p_row03_cosetLabels2 (g32p_row03_cosetBranchNext 2 i) = g32p_row03_cosetLabels2 i := by
  decide +kernel

theorem g32p_row03_cosetReach2 : ∀ i : Fin 36, (g32p_row03_cosetBranchNext 2)^[g32p_row03_cosetDistances2 i] (g32p_row03_cosetRoots2 (g32p_row03_cosetLabels2 i)) = i := by
  decide +kernel

theorem g32p_row03_cosetPeriods2 : ∀ j : Fin 24, 0 < g32p_row03_cosetLengths2 j ∧ (g32p_row03_cosetBranchNext 2)^[g32p_row03_cosetLengths2 j] (g32p_row03_cosetRoots2 j) = g32p_row03_cosetRoots2 j ∧ ∀ t : Fin (g32p_row03_cosetLengths2 j), 0 < t.val → (g32p_row03_cosetBranchNext 2)^[t.val] (g32p_row03_cosetRoots2 j) ≠ g32p_row03_cosetRoots2 j := by
  decide +kernel

theorem g32p_row03_cosetCycleSteps2 : ∀ cycle ∈ g32p_row03_cosetCycles2,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row03_cosetBranchNext 2 ⟨i % 36, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row03_cosetPermutation2 : Function.Bijective (g32p_row03_cosetBranchNext 2) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 400000

def g32p_row03_cosetEquiv : Fin 36 ≃ (g32p_G ⧸ g32p_row03_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row03_cosetEnumeration

theorem g32p_row03_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row03_cosetBranchMatrices b)) := by
  have he : g32p_row03_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    fin_cases b
    · exact g32p_row03_cosetBranchMatrix0
    · exact g32p_row03_cosetBranchMatrix1
    · exact g32p_row03_cosetBranchMatrix2
  rw [he]
  exact g32p_cosetBranches_map b

theorem g32p_row03_cosetBranchCheck (b : Fin 3) (i : Fin 36) :
    HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices b) (g32p_row03_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetBranchNext b i))
        (g32p_row03_groupNodes (g32p_row03_cosetBranchFactor b i)) := by
  fin_cases i
  · exact g32p_row03_cosetBranchStep_0000 b
  · exact g32p_row03_cosetBranchStep_0001 b
  · exact g32p_row03_cosetBranchStep_0002 b
  · exact g32p_row03_cosetBranchStep_0003 b
  · exact g32p_row03_cosetBranchStep_0004 b
  · exact g32p_row03_cosetBranchStep_0005 b
  · exact g32p_row03_cosetBranchStep_0006 b
  · exact g32p_row03_cosetBranchStep_0007 b
  · exact g32p_row03_cosetBranchStep_0008 b
  · exact g32p_row03_cosetBranchStep_0009 b
  · exact g32p_row03_cosetBranchStep_0010 b
  · exact g32p_row03_cosetBranchStep_0011 b
  · exact g32p_row03_cosetBranchStep_0012 b
  · exact g32p_row03_cosetBranchStep_0013 b
  · exact g32p_row03_cosetBranchStep_0014 b
  · exact g32p_row03_cosetBranchStep_0015 b
  · exact g32p_row03_cosetBranchStep_0016 b
  · exact g32p_row03_cosetBranchStep_0017 b
  · exact g32p_row03_cosetBranchStep_0018 b
  · exact g32p_row03_cosetBranchStep_0019 b
  · exact g32p_row03_cosetBranchStep_0020 b
  · exact g32p_row03_cosetBranchStep_0021 b
  · exact g32p_row03_cosetBranchStep_0022 b
  · exact g32p_row03_cosetBranchStep_0023 b
  · exact g32p_row03_cosetBranchStep_0024 b
  · exact g32p_row03_cosetBranchStep_0025 b
  · exact g32p_row03_cosetBranchStep_0026 b
  · exact g32p_row03_cosetBranchStep_0027 b
  · exact g32p_row03_cosetBranchStep_0028 b
  · exact g32p_row03_cosetBranchStep_0029 b
  · exact g32p_row03_cosetBranchStep_0030 b
  · exact g32p_row03_cosetBranchStep_0031 b
  · exact g32p_row03_cosetBranchStep_0032 b
  · exact g32p_row03_cosetBranchStep_0033 b
  · exact g32p_row03_cosetBranchStep_0034 b
  · exact g32p_row03_cosetBranchStep_0035 b

theorem g32p_row03_cosetActualBranchStep (b : Fin 3) (i : Fin 36) :
    g32p_cosetBranches b * g32p_row03_cosetActualRepresentatives i =
      g32p_row03_cosetActualRepresentatives (g32p_row03_cosetBranchNext b i) *
        (g32p_row03_groupEquiv (g32p_row03_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row03_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row03_cosetActualRepresentatives (g32p_row03_cosetBranchNext b i) *
      (g32p_row03_groupEquiv (g32p_row03_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row03_cosetBranchMap, g32p_row03_cosetActualRepresentatives_map,
    g32p_row03_cosetActualRepresentatives_map, g32p_row03_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row03_cosetBranchCheck]

theorem g32p_row03_cosetQuotientStep (b : Fin 3) (i : Fin 36) :
    g32p_row03_cosetEquiv (g32p_row03_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row03_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row03_cosetActualRepresentatives (g32p_row03_cosetBranchNext b i)) : g32p_G ⧸ g32p_row03_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row03_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row03_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row03_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row03_groupEquiv (g32p_row03_cosetBranchFactor b i)).property

def g32p_row03_cosetOrbitEquiv0 : Fin 12 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 0)) (g32p_G ⧸ g32p_row03_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 0) g32p_row03_cosetEquiv
    (g32p_row03_cosetBranchNext 0) (g32p_row03_cosetQuotientStep 0) g32p_row03_cosetLabels0 g32p_row03_cosetRoots0
    g32p_row03_cosetDistances0 g32p_row03_cosetRootLabels0 g32p_row03_cosetNextLabels0 g32p_row03_cosetReach0)

theorem g32p_row03_cosetPeriod0 (j : Fin 12) :
    Function.minimalPeriod ((g32p_cosetBranches 0) • ·) (g32p_row03_cosetEquiv (g32p_row03_cosetRoots0 j)) = g32p_row03_cosetLengths0 j := by
  apply g32p_period_of_cycle g32p_row03_cosetEquiv (g32p_row03_cosetBranchNext 0) ((g32p_cosetBranches 0) • ·)
    (g32p_row03_cosetQuotientStep 0) _ _ (g32p_row03_cosetPeriods0 j).1 (g32p_row03_cosetPeriods0 j).2.1
  intro t ht hlt
  exact (g32p_row03_cosetPeriods0 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row03_cosetActualMonodromy0 (j : Fin 12) :
    (g32p_cosetBranches 0) ^ g32p_row03_cosetLengths0 j * g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots0 j) =
      g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots0 j) *
        (g32p_row03_groupEquiv (g32p_row03_cosetMonodromies0 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row03_cosetBranchMatrices 0)
    (g32p_row03_cosetRepresentatives (g32p_row03_cosetRoots0 j))
    (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 j))
    (g32p_row03_cosetLengths0 j) (g32p_row03_cosetBranchMap 0)
    (g32p_row03_cosetActualRepresentatives_map _) (g32p_row03_groupEquiv_map _)
  fin_cases j
  · exact g32p_row03_cosetMonodromy_0_0000.1
  · exact g32p_row03_cosetMonodromy_0_0001.1
  · exact g32p_row03_cosetMonodromy_0_0002.1
  · exact g32p_row03_cosetMonodromy_0_0003.1
  · exact g32p_row03_cosetMonodromy_0_0004.1
  · exact g32p_row03_cosetMonodromy_0_0005.1
  · exact g32p_row03_cosetMonodromy_0_0006.1
  · exact g32p_row03_cosetMonodromy_0_0007.1
  · exact g32p_row03_cosetMonodromy_0_0008.1
  · exact g32p_row03_cosetMonodromy_0_0009.1
  · exact g32p_row03_cosetMonodromy_0_0010.1
  · exact g32p_row03_cosetMonodromy_0_0011.1

theorem g32p_row03_cosetCharacter0 (j : Fin 12) :
    g32p_row03_finiteSupplier.χ (g32p_row03_groupEquiv (g32p_row03_cosetMonodromies0 j)) = g32p_row03_cosetExponents0 j := by
  rw [g32p_row03_finiteSupplier_value]
  fin_cases j
  · exact g32p_row03_cosetMonodromy_0_0000.2
  · exact g32p_row03_cosetMonodromy_0_0001.2
  · exact g32p_row03_cosetMonodromy_0_0002.2
  · exact g32p_row03_cosetMonodromy_0_0003.2
  · exact g32p_row03_cosetMonodromy_0_0004.2
  · exact g32p_row03_cosetMonodromy_0_0005.2
  · exact g32p_row03_cosetMonodromy_0_0006.2
  · exact g32p_row03_cosetMonodromy_0_0007.2
  · exact g32p_row03_cosetMonodromy_0_0008.2
  · exact g32p_row03_cosetMonodromy_0_0009.2
  · exact g32p_row03_cosetMonodromy_0_0010.2
  · exact g32p_row03_cosetMonodromy_0_0011.2

theorem g32p_row03_cosetBranchExponents0 :
    papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_cosetBranches 0) =
      (Finset.univ.val.map (fun j : Fin 12 => Multiplicative.toAdd (g32p_row03_cosetExponents0 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row03_cosetOrbitEquiv0
    (fun j => g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots0 j)) (fun _ => rfl) g32p_row03_cosetLengths0 g32p_row03_cosetPeriod0
    (fun j => g32p_row03_groupEquiv (g32p_row03_cosetMonodromies0 j)) g32p_row03_cosetActualMonodromy0]
  simp only [g32p_row03_cosetCharacter0]
  rfl

def g32p_row03_cosetOrbitEquiv1 : Fin 12 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 1)) (g32p_G ⧸ g32p_row03_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 1) g32p_row03_cosetEquiv
    (g32p_row03_cosetBranchNext 1) (g32p_row03_cosetQuotientStep 1) g32p_row03_cosetLabels1 g32p_row03_cosetRoots1
    g32p_row03_cosetDistances1 g32p_row03_cosetRootLabels1 g32p_row03_cosetNextLabels1 g32p_row03_cosetReach1)

theorem g32p_row03_cosetPeriod1 (j : Fin 12) :
    Function.minimalPeriod ((g32p_cosetBranches 1) • ·) (g32p_row03_cosetEquiv (g32p_row03_cosetRoots1 j)) = g32p_row03_cosetLengths1 j := by
  apply g32p_period_of_cycle g32p_row03_cosetEquiv (g32p_row03_cosetBranchNext 1) ((g32p_cosetBranches 1) • ·)
    (g32p_row03_cosetQuotientStep 1) _ _ (g32p_row03_cosetPeriods1 j).1 (g32p_row03_cosetPeriods1 j).2.1
  intro t ht hlt
  exact (g32p_row03_cosetPeriods1 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row03_cosetActualMonodromy1 (j : Fin 12) :
    (g32p_cosetBranches 1) ^ g32p_row03_cosetLengths1 j * g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots1 j) =
      g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots1 j) *
        (g32p_row03_groupEquiv (g32p_row03_cosetMonodromies1 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row03_cosetBranchMatrices 1)
    (g32p_row03_cosetRepresentatives (g32p_row03_cosetRoots1 j))
    (g32p_row03_groupNodes (g32p_row03_cosetMonodromies1 j))
    (g32p_row03_cosetLengths1 j) (g32p_row03_cosetBranchMap 1)
    (g32p_row03_cosetActualRepresentatives_map _) (g32p_row03_groupEquiv_map _)
  fin_cases j
  · exact g32p_row03_cosetMonodromy_1_0000.1
  · exact g32p_row03_cosetMonodromy_1_0001.1
  · exact g32p_row03_cosetMonodromy_1_0002.1
  · exact g32p_row03_cosetMonodromy_1_0003.1
  · exact g32p_row03_cosetMonodromy_1_0004.1
  · exact g32p_row03_cosetMonodromy_1_0005.1
  · exact g32p_row03_cosetMonodromy_1_0006.1
  · exact g32p_row03_cosetMonodromy_1_0007.1
  · exact g32p_row03_cosetMonodromy_1_0008.1
  · exact g32p_row03_cosetMonodromy_1_0009.1
  · exact g32p_row03_cosetMonodromy_1_0010.1
  · exact g32p_row03_cosetMonodromy_1_0011.1

theorem g32p_row03_cosetCharacter1 (j : Fin 12) :
    g32p_row03_finiteSupplier.χ (g32p_row03_groupEquiv (g32p_row03_cosetMonodromies1 j)) = g32p_row03_cosetExponents1 j := by
  rw [g32p_row03_finiteSupplier_value]
  fin_cases j
  · exact g32p_row03_cosetMonodromy_1_0000.2
  · exact g32p_row03_cosetMonodromy_1_0001.2
  · exact g32p_row03_cosetMonodromy_1_0002.2
  · exact g32p_row03_cosetMonodromy_1_0003.2
  · exact g32p_row03_cosetMonodromy_1_0004.2
  · exact g32p_row03_cosetMonodromy_1_0005.2
  · exact g32p_row03_cosetMonodromy_1_0006.2
  · exact g32p_row03_cosetMonodromy_1_0007.2
  · exact g32p_row03_cosetMonodromy_1_0008.2
  · exact g32p_row03_cosetMonodromy_1_0009.2
  · exact g32p_row03_cosetMonodromy_1_0010.2
  · exact g32p_row03_cosetMonodromy_1_0011.2

theorem g32p_row03_cosetBranchExponents1 :
    papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_cosetBranches 1) =
      (Finset.univ.val.map (fun j : Fin 12 => Multiplicative.toAdd (g32p_row03_cosetExponents1 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row03_cosetOrbitEquiv1
    (fun j => g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots1 j)) (fun _ => rfl) g32p_row03_cosetLengths1 g32p_row03_cosetPeriod1
    (fun j => g32p_row03_groupEquiv (g32p_row03_cosetMonodromies1 j)) g32p_row03_cosetActualMonodromy1]
  simp only [g32p_row03_cosetCharacter1]
  rfl

def g32p_row03_cosetOrbitEquiv2 : Fin 24 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row03_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row03_cosetEquiv
    (g32p_row03_cosetBranchNext 2) (g32p_row03_cosetQuotientStep 2) g32p_row03_cosetLabels2 g32p_row03_cosetRoots2
    g32p_row03_cosetDistances2 g32p_row03_cosetRootLabels2 g32p_row03_cosetNextLabels2 g32p_row03_cosetReach2)

theorem g32p_row03_cosetPeriod2 (j : Fin 24) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row03_cosetEquiv (g32p_row03_cosetRoots2 j)) = g32p_row03_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row03_cosetEquiv (g32p_row03_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row03_cosetQuotientStep 2) _ _ (g32p_row03_cosetPeriods2 j).1 (g32p_row03_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row03_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row03_cosetActualMonodromy2 (j : Fin 24) :
    (g32p_cosetBranches 2) ^ g32p_row03_cosetLengths2 j * g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots2 j) =
      g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots2 j) *
        (g32p_row03_groupEquiv (g32p_row03_cosetMonodromies2 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row03_cosetBranchMatrices 2)
    (g32p_row03_cosetRepresentatives (g32p_row03_cosetRoots2 j))
    (g32p_row03_groupNodes (g32p_row03_cosetMonodromies2 j))
    (g32p_row03_cosetLengths2 j) (g32p_row03_cosetBranchMap 2)
    (g32p_row03_cosetActualRepresentatives_map _) (g32p_row03_groupEquiv_map _)
  fin_cases j
  · exact g32p_row03_cosetMonodromy_2_0000.1
  · exact g32p_row03_cosetMonodromy_2_0001.1
  · exact g32p_row03_cosetMonodromy_2_0002.1
  · exact g32p_row03_cosetMonodromy_2_0003.1
  · exact g32p_row03_cosetMonodromy_2_0004.1
  · exact g32p_row03_cosetMonodromy_2_0005.1
  · exact g32p_row03_cosetMonodromy_2_0006.1
  · exact g32p_row03_cosetMonodromy_2_0007.1
  · exact g32p_row03_cosetMonodromy_2_0008.1
  · exact g32p_row03_cosetMonodromy_2_0009.1
  · exact g32p_row03_cosetMonodromy_2_0010.1
  · exact g32p_row03_cosetMonodromy_2_0011.1
  · exact g32p_row03_cosetMonodromy_2_0012.1
  · exact g32p_row03_cosetMonodromy_2_0013.1
  · exact g32p_row03_cosetMonodromy_2_0014.1
  · exact g32p_row03_cosetMonodromy_2_0015.1
  · exact g32p_row03_cosetMonodromy_2_0016.1
  · exact g32p_row03_cosetMonodromy_2_0017.1
  · exact g32p_row03_cosetMonodromy_2_0018.1
  · exact g32p_row03_cosetMonodromy_2_0019.1
  · exact g32p_row03_cosetMonodromy_2_0020.1
  · exact g32p_row03_cosetMonodromy_2_0021.1
  · exact g32p_row03_cosetMonodromy_2_0022.1
  · exact g32p_row03_cosetMonodromy_2_0023.1

theorem g32p_row03_cosetCharacter2 (j : Fin 24) :
    g32p_row03_finiteSupplier.χ (g32p_row03_groupEquiv (g32p_row03_cosetMonodromies2 j)) = g32p_row03_cosetExponents2 j := by
  rw [g32p_row03_finiteSupplier_value]
  fin_cases j
  · exact g32p_row03_cosetMonodromy_2_0000.2
  · exact g32p_row03_cosetMonodromy_2_0001.2
  · exact g32p_row03_cosetMonodromy_2_0002.2
  · exact g32p_row03_cosetMonodromy_2_0003.2
  · exact g32p_row03_cosetMonodromy_2_0004.2
  · exact g32p_row03_cosetMonodromy_2_0005.2
  · exact g32p_row03_cosetMonodromy_2_0006.2
  · exact g32p_row03_cosetMonodromy_2_0007.2
  · exact g32p_row03_cosetMonodromy_2_0008.2
  · exact g32p_row03_cosetMonodromy_2_0009.2
  · exact g32p_row03_cosetMonodromy_2_0010.2
  · exact g32p_row03_cosetMonodromy_2_0011.2
  · exact g32p_row03_cosetMonodromy_2_0012.2
  · exact g32p_row03_cosetMonodromy_2_0013.2
  · exact g32p_row03_cosetMonodromy_2_0014.2
  · exact g32p_row03_cosetMonodromy_2_0015.2
  · exact g32p_row03_cosetMonodromy_2_0016.2
  · exact g32p_row03_cosetMonodromy_2_0017.2
  · exact g32p_row03_cosetMonodromy_2_0018.2
  · exact g32p_row03_cosetMonodromy_2_0019.2
  · exact g32p_row03_cosetMonodromy_2_0020.2
  · exact g32p_row03_cosetMonodromy_2_0021.2
  · exact g32p_row03_cosetMonodromy_2_0022.2
  · exact g32p_row03_cosetMonodromy_2_0023.2

theorem g32p_row03_cosetBranchExponents2 :
    papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 24 => Multiplicative.toAdd (g32p_row03_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row03_cosetOrbitEquiv2
    (fun j => g32p_row03_cosetActualRepresentatives (g32p_row03_cosetRoots2 j)) (fun _ => rfl) g32p_row03_cosetLengths2 g32p_row03_cosetPeriod2
    (fun j => g32p_row03_groupEquiv (g32p_row03_cosetMonodromies2 j)) g32p_row03_cosetActualMonodromy2]
  simp only [g32p_row03_cosetCharacter2]
  rfl

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row03_exponents :
    (g32p_exponents g32p_row03_finiteSupplier).Perm (expandExps [(3, 12)]) := by
  have h0 : papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_classDatum 0) = 0 := by
    change papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row03_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 12)).val.map
      (fun j => Multiplicative.toAdd (g32p_row03_cosetExponents0 j))).filter (· ≠ 0) = 0
    decide +kernel
  have h1 : papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_classDatum 6) = 0 := by
    change papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row03_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 12)).val.map
      (fun j => Multiplicative.toAdd (g32p_row03_cosetExponents1 j))).filter (· ≠ 0) = 0
    decide +kernel
  have h2 : papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_classDatum 12) = Multiset.replicate 12 (3 : ZMod 6) := by
    change papersExps g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row03_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 24)).val.map
      (fun j => Multiplicative.toAdd (g32p_row03_cosetExponents2 j))).filter (· ≠ 0) = Multiset.replicate 12 (3 : ZMod 6)
    decide +kernel
  have hs : papersExpsTuple g32p_row03_finiteSupplier.H g32p_row03_finiteSupplier.χ g32p_classList =
      Multiset.replicate 12 (3 : ZMod 6) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, nsmul_zero, zero_add, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (Multiset.replicate 12 (3 : ZMod 6)).map ZMod.val = ↑(expandExps [(3, 12)])
  decide +kernel

theorem g32p_row03_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 3 ∧ r.m = g32p_row03_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row03_finiteSupplier.H ∧
      (g32p_exponents g32p_row03_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨3, (1), 4320, 6, 115, 12, 240, some 3, [(3, 12)], .S⟩,
    ?_, rfl, rfl, g32p_row03_finiteSupplier_order.symm, g32p_row03_exponents⟩
  decide

def g32p_row03_complexWitness : g32p_row03_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row03_finiteSupplier

theorem g32p_row03_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 3 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row03_finiteSupplier, g32p_row03_complexWitness, g32p_complexCharacter_apply _,
    g32p_row03_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
