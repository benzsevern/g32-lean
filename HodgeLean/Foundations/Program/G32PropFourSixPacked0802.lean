import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness28CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0800
import HodgeLean.Foundations.Program.G32PropFourSixPacked0801
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetBranchMatrix1 : g32p_row28_cosetBranchMatrices 1 = g32p_cosetIntegralBranches 1 := by
  decide +kernel

theorem g32p_row28_cosetPartition1 : (g32p_row28_cosetCycles1).flatten.Perm (List.range 320) := by
  decide +kernel

theorem g32p_row28_cosetRootLabels1 : ∀ j : Fin 128, g32p_row28_cosetLabels1 (g32p_row28_cosetRoots1 j) = j := by
  decide +kernel

theorem g32p_row28_cosetNextLabels1 : ∀ i : Fin 320, g32p_row28_cosetLabels1 (g32p_row28_cosetBranchNext 1 i) = g32p_row28_cosetLabels1 i := by
  decide +kernel

theorem g32p_row28_cosetReach1 : ∀ i : Fin 320, (g32p_row28_cosetBranchNext 1)^[g32p_row28_cosetDistances1 i] (g32p_row28_cosetRoots1 (g32p_row28_cosetLabels1 i)) = i := by
  decide +kernel

theorem g32p_row28_cosetPeriods1 : ∀ j : Fin 128, 0 < g32p_row28_cosetLengths1 j ∧ (g32p_row28_cosetBranchNext 1)^[g32p_row28_cosetLengths1 j] (g32p_row28_cosetRoots1 j) = g32p_row28_cosetRoots1 j ∧ ∀ t : Fin (g32p_row28_cosetLengths1 j), 0 < t.val → (g32p_row28_cosetBranchNext 1)^[t.val] (g32p_row28_cosetRoots1 j) ≠ g32p_row28_cosetRoots1 j := by
  decide +kernel

theorem g32p_row28_cosetCycleSteps1 : ∀ cycle ∈ g32p_row28_cosetCycles1,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row28_cosetBranchNext 1 ⟨i % 320, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row28_cosetInverse1 : ∀ i : Fin 320,
    ((g32p_row28_cosetBranchNext 1)^[2]) (g32p_row28_cosetBranchNext 1 i) = i ∧
    g32p_row28_cosetBranchNext 1 (((g32p_row28_cosetBranchNext 1)^[2]) i) = i := by
  decide +kernel

theorem g32p_row28_cosetPermutation1 : Function.Bijective (g32p_row28_cosetBranchNext 1) := by
  have hl : Function.LeftInverse ((g32p_row28_cosetBranchNext 1)^[2]) (g32p_row28_cosetBranchNext 1) :=
    fun i => (g32p_row28_cosetInverse1 i).1
  have hr : Function.RightInverse ((g32p_row28_cosetBranchNext 1)^[2]) (g32p_row28_cosetBranchNext 1) :=
    fun i => (g32p_row28_cosetInverse1 i).2
  exact ⟨hl.injective, hr.surjective⟩


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetBranchMatrix2 : g32p_row28_cosetBranchMatrices 2 = g32p_cosetIntegralBranches 2 := by
  decide +kernel

theorem g32p_row28_cosetPartition2 : (g32p_row28_cosetCycles2).flatten.Perm (List.range 320) := by
  decide +kernel

theorem g32p_row28_cosetRootLabels2 : ∀ j : Fin 160, g32p_row28_cosetLabels2 (g32p_row28_cosetRoots2 j) = j := by
  decide +kernel

theorem g32p_row28_cosetNextLabels2 : ∀ i : Fin 320, g32p_row28_cosetLabels2 (g32p_row28_cosetBranchNext 2 i) = g32p_row28_cosetLabels2 i := by
  decide +kernel

theorem g32p_row28_cosetReach2 : ∀ i : Fin 320, (g32p_row28_cosetBranchNext 2)^[g32p_row28_cosetDistances2 i] (g32p_row28_cosetRoots2 (g32p_row28_cosetLabels2 i)) = i := by
  decide +kernel

theorem g32p_row28_cosetPeriods2 : ∀ j : Fin 160, 0 < g32p_row28_cosetLengths2 j ∧ (g32p_row28_cosetBranchNext 2)^[g32p_row28_cosetLengths2 j] (g32p_row28_cosetRoots2 j) = g32p_row28_cosetRoots2 j ∧ ∀ t : Fin (g32p_row28_cosetLengths2 j), 0 < t.val → (g32p_row28_cosetBranchNext 2)^[t.val] (g32p_row28_cosetRoots2 j) ≠ g32p_row28_cosetRoots2 j := by
  decide +kernel

theorem g32p_row28_cosetCycleSteps2 : ∀ cycle ∈ g32p_row28_cosetCycles2,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row28_cosetBranchNext 2 ⟨i % 320, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row28_cosetInverse2 : ∀ i : Fin 320,
    ((g32p_row28_cosetBranchNext 2)^[1]) (g32p_row28_cosetBranchNext 2 i) = i ∧
    g32p_row28_cosetBranchNext 2 (((g32p_row28_cosetBranchNext 2)^[1]) i) = i := by
  decide +kernel

theorem g32p_row28_cosetPermutation2 : Function.Bijective (g32p_row28_cosetBranchNext 2) := by
  have hl : Function.LeftInverse ((g32p_row28_cosetBranchNext 2)^[1]) (g32p_row28_cosetBranchNext 2) :=
    fun i => (g32p_row28_cosetInverse2 i).1
  have hr : Function.RightInverse ((g32p_row28_cosetBranchNext 2)^[1]) (g32p_row28_cosetBranchNext 2) :=
    fun i => (g32p_row28_cosetInverse2 i).2
  exact ⟨hl.injective, hr.surjective⟩


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row28_cosetEquiv : Fin 320 ≃ (g32p_G ⧸ g32p_row28_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row28_cosetEnumeration

theorem g32p_row28_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row28_cosetBranchMatrices b)) := by
  have he : g32p_row28_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    fin_cases b
    · exact g32p_row28_cosetBranchMatrix0
    · exact g32p_row28_cosetBranchMatrix1
    · exact g32p_row28_cosetBranchMatrix2
  rw [he]
  exact g32p_cosetBranches_map b

theorem g32p_row28_cosetBranchCheck (b : Fin 3) (i : Fin 320) :
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices b) (g32p_row28_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext b i))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor b i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row28_cosetBranchBlock_0000 b
  · exact g32p_row28_cosetBranchBlock_0001 b
  · exact g32p_row28_cosetBranchBlock_0002 b
  · exact g32p_row28_cosetBranchBlock_0003 b
  · exact g32p_row28_cosetBranchBlock_0004 b
  · exact g32p_row28_cosetBranchBlock_0005 b
  · exact g32p_row28_cosetBranchBlock_0006 b
  · exact g32p_row28_cosetBranchBlock_0007 b
  · exact g32p_row28_cosetBranchBlock_0008 b
  · exact g32p_row28_cosetBranchBlock_0009 b
  · exact g32p_row28_cosetBranchBlock_0010 b
  · exact g32p_row28_cosetBranchBlock_0011 b
  · exact g32p_row28_cosetBranchBlock_0012 b
  · exact g32p_row28_cosetBranchBlock_0013 b
  · exact g32p_row28_cosetBranchBlock_0014 b
  · exact g32p_row28_cosetBranchBlock_0015 b
  · exact g32p_row28_cosetBranchBlock_0016 b
  · exact g32p_row28_cosetBranchBlock_0017 b
  · exact g32p_row28_cosetBranchBlock_0018 b
  · exact g32p_row28_cosetBranchBlock_0019 b


theorem g32p_row28_cosetActualBranchStep (b : Fin 3) (i : Fin 320) :
    g32p_cosetBranches b * g32p_row28_cosetActualRepresentatives i =
      g32p_row28_cosetActualRepresentatives (g32p_row28_cosetBranchNext b i) *
        (g32p_row09_groupEquiv (g32p_row28_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row28_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row28_cosetActualRepresentatives (g32p_row28_cosetBranchNext b i) *
      (g32p_row09_groupEquiv (g32p_row28_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row28_cosetBranchMap, g32p_row28_cosetActualRepresentatives_map,
    g32p_row28_cosetActualRepresentatives_map, g32p_row09_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row28_cosetBranchCheck]

theorem g32p_row28_cosetQuotientStep (b : Fin 3) (i : Fin 320) :
    g32p_row28_cosetEquiv (g32p_row28_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row28_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row28_cosetActualRepresentatives (g32p_row28_cosetBranchNext b i)) : g32p_G ⧸ g32p_row28_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row28_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row28_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row28_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row09_groupEquiv (g32p_row28_cosetBranchFactor b i)).property

def g32p_row28_cosetOrbitEquiv0 : Fin 128 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 0)) (g32p_G ⧸ g32p_row28_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 0) g32p_row28_cosetEquiv
    (g32p_row28_cosetBranchNext 0) (g32p_row28_cosetQuotientStep 0) g32p_row28_cosetLabels0 g32p_row28_cosetRoots0
    g32p_row28_cosetDistances0 g32p_row28_cosetRootLabels0 g32p_row28_cosetNextLabels0 g32p_row28_cosetReach0)

theorem g32p_row28_cosetPeriod0 (j : Fin 128) :
    Function.minimalPeriod ((g32p_cosetBranches 0) • ·) (g32p_row28_cosetEquiv (g32p_row28_cosetRoots0 j)) = g32p_row28_cosetLengths0 j := by
  apply g32p_period_of_cycle g32p_row28_cosetEquiv (g32p_row28_cosetBranchNext 0) ((g32p_cosetBranches 0) • ·)
    (g32p_row28_cosetQuotientStep 0) _ _ (g32p_row28_cosetPeriods0 j).1 (g32p_row28_cosetPeriods0 j).2.1
  intro t ht hlt
  exact (g32p_row28_cosetPeriods0 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row28_cosetMonodromyCheck0 (j : Fin 128) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 j))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 j)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 j))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 j)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 j) = g32p_row28_cosetExponents0 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row28_cosetMonodromyBlock0_0000
  · exact g32p_row28_cosetMonodromyBlock0_0001
  · exact g32p_row28_cosetMonodromyBlock0_0002
  · exact g32p_row28_cosetMonodromyBlock0_0003
  · exact g32p_row28_cosetMonodromyBlock0_0004
  · exact g32p_row28_cosetMonodromyBlock0_0005
  · exact g32p_row28_cosetMonodromyBlock0_0006
  · exact g32p_row28_cosetMonodromyBlock0_0007

theorem g32p_row28_cosetActualMonodromy0 (j : Fin 128) :
    (g32p_cosetBranches 0) ^ g32p_row28_cosetLengths0 j * g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots0 j) =
      g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots0 j) *
        (g32p_row09_groupEquiv (g32p_row28_cosetMonodromies0 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row28_cosetBranchMatrices 0)
    (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 j))
    (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 j))
    (g32p_row28_cosetLengths0 j) (g32p_row28_cosetBranchMap 0)
    (g32p_row28_cosetActualRepresentatives_map _) (g32p_row09_groupEquiv_map _)
  exact (g32p_row28_cosetMonodromyCheck0 j).1

theorem g32p_row28_cosetCharacter0 (j : Fin 128) :
    g32p_row28_finiteSupplier.χ (g32p_row09_groupEquiv (g32p_row28_cosetMonodromies0 j)) = g32p_row28_cosetExponents0 j := by
  rw [g32p_row28_finiteSupplier_value]
  exact (g32p_row28_cosetMonodromyCheck0 j).2

theorem g32p_row28_cosetBranchExponents0 :
    papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_cosetBranches 0) =
      (Finset.univ.val.map (fun j : Fin 128 => Multiplicative.toAdd (g32p_row28_cosetExponents0 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row28_cosetOrbitEquiv0
    (fun j => g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots0 j)) (fun _ => rfl) g32p_row28_cosetLengths0 g32p_row28_cosetPeriod0
    (fun j => g32p_row09_groupEquiv (g32p_row28_cosetMonodromies0 j)) g32p_row28_cosetActualMonodromy0]
  simp only [g32p_row28_cosetCharacter0]
  rfl

def g32p_row28_cosetOrbitEquiv1 : Fin 128 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 1)) (g32p_G ⧸ g32p_row28_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 1) g32p_row28_cosetEquiv
    (g32p_row28_cosetBranchNext 1) (g32p_row28_cosetQuotientStep 1) g32p_row28_cosetLabels1 g32p_row28_cosetRoots1
    g32p_row28_cosetDistances1 g32p_row28_cosetRootLabels1 g32p_row28_cosetNextLabels1 g32p_row28_cosetReach1)

theorem g32p_row28_cosetPeriod1 (j : Fin 128) :
    Function.minimalPeriod ((g32p_cosetBranches 1) • ·) (g32p_row28_cosetEquiv (g32p_row28_cosetRoots1 j)) = g32p_row28_cosetLengths1 j := by
  apply g32p_period_of_cycle g32p_row28_cosetEquiv (g32p_row28_cosetBranchNext 1) ((g32p_cosetBranches 1) • ·)
    (g32p_row28_cosetQuotientStep 1) _ _ (g32p_row28_cosetPeriods1 j).1 (g32p_row28_cosetPeriods1 j).2.1
  intro t ht hlt
  exact (g32p_row28_cosetPeriods1 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row28_cosetMonodromyCheck1 (j : Fin 128) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 1) (g32p_row28_cosetLengths1 j))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 j)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 j))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 j)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 j) = g32p_row28_cosetExponents1 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row28_cosetMonodromyBlock1_0000
  · exact g32p_row28_cosetMonodromyBlock1_0001
  · exact g32p_row28_cosetMonodromyBlock1_0002
  · exact g32p_row28_cosetMonodromyBlock1_0003
  · exact g32p_row28_cosetMonodromyBlock1_0004
  · exact g32p_row28_cosetMonodromyBlock1_0005
  · exact g32p_row28_cosetMonodromyBlock1_0006
  · exact g32p_row28_cosetMonodromyBlock1_0007

theorem g32p_row28_cosetActualMonodromy1 (j : Fin 128) :
    (g32p_cosetBranches 1) ^ g32p_row28_cosetLengths1 j * g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots1 j) =
      g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots1 j) *
        (g32p_row09_groupEquiv (g32p_row28_cosetMonodromies1 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row28_cosetBranchMatrices 1)
    (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 j))
    (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 j))
    (g32p_row28_cosetLengths1 j) (g32p_row28_cosetBranchMap 1)
    (g32p_row28_cosetActualRepresentatives_map _) (g32p_row09_groupEquiv_map _)
  exact (g32p_row28_cosetMonodromyCheck1 j).1

theorem g32p_row28_cosetCharacter1 (j : Fin 128) :
    g32p_row28_finiteSupplier.χ (g32p_row09_groupEquiv (g32p_row28_cosetMonodromies1 j)) = g32p_row28_cosetExponents1 j := by
  rw [g32p_row28_finiteSupplier_value]
  exact (g32p_row28_cosetMonodromyCheck1 j).2

theorem g32p_row28_cosetBranchExponents1 :
    papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_cosetBranches 1) =
      (Finset.univ.val.map (fun j : Fin 128 => Multiplicative.toAdd (g32p_row28_cosetExponents1 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row28_cosetOrbitEquiv1
    (fun j => g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots1 j)) (fun _ => rfl) g32p_row28_cosetLengths1 g32p_row28_cosetPeriod1
    (fun j => g32p_row09_groupEquiv (g32p_row28_cosetMonodromies1 j)) g32p_row28_cosetActualMonodromy1]
  simp only [g32p_row28_cosetCharacter1]
  rfl

def g32p_row28_cosetOrbitEquiv2 : Fin 160 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row28_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row28_cosetEquiv
    (g32p_row28_cosetBranchNext 2) (g32p_row28_cosetQuotientStep 2) g32p_row28_cosetLabels2 g32p_row28_cosetRoots2
    g32p_row28_cosetDistances2 g32p_row28_cosetRootLabels2 g32p_row28_cosetNextLabels2 g32p_row28_cosetReach2)

theorem g32p_row28_cosetPeriod2 (j : Fin 160) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row28_cosetEquiv (g32p_row28_cosetRoots2 j)) = g32p_row28_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row28_cosetEquiv (g32p_row28_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row28_cosetQuotientStep 2) _ _ (g32p_row28_cosetPeriods2 j).1 (g32p_row28_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row28_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row28_cosetMonodromyCheck2 (j : Fin 160) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 2) (g32p_row28_cosetLengths2 j))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots2 j)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots2 j))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies2 j)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies2 j) = g32p_row28_cosetExponents2 j := by
  revert j
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row28_cosetMonodromyBlock2_0000
  · exact g32p_row28_cosetMonodromyBlock2_0001
  · exact g32p_row28_cosetMonodromyBlock2_0002
  · exact g32p_row28_cosetMonodromyBlock2_0003
  · exact g32p_row28_cosetMonodromyBlock2_0004
  · exact g32p_row28_cosetMonodromyBlock2_0005
  · exact g32p_row28_cosetMonodromyBlock2_0006
  · exact g32p_row28_cosetMonodromyBlock2_0007
  · exact g32p_row28_cosetMonodromyBlock2_0008
  · exact g32p_row28_cosetMonodromyBlock2_0009

theorem g32p_row28_cosetActualMonodromy2 (j : Fin 160) :
    (g32p_cosetBranches 2) ^ g32p_row28_cosetLengths2 j * g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots2 j) =
      g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots2 j) *
        (g32p_row09_groupEquiv (g32p_row28_cosetMonodromies2 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row28_cosetBranchMatrices 2)
    (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots2 j))
    (g32p_row09_groupNodes (g32p_row28_cosetMonodromies2 j))
    (g32p_row28_cosetLengths2 j) (g32p_row28_cosetBranchMap 2)
    (g32p_row28_cosetActualRepresentatives_map _) (g32p_row09_groupEquiv_map _)
  exact (g32p_row28_cosetMonodromyCheck2 j).1

theorem g32p_row28_cosetCharacter2 (j : Fin 160) :
    g32p_row28_finiteSupplier.χ (g32p_row09_groupEquiv (g32p_row28_cosetMonodromies2 j)) = g32p_row28_cosetExponents2 j := by
  rw [g32p_row28_finiteSupplier_value]
  exact (g32p_row28_cosetMonodromyCheck2 j).2

theorem g32p_row28_cosetBranchExponents2 :
    papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 160 => Multiplicative.toAdd (g32p_row28_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row28_cosetOrbitEquiv2
    (fun j => g32p_row28_cosetActualRepresentatives (g32p_row28_cosetRoots2 j)) (fun _ => rfl) g32p_row28_cosetLengths2 g32p_row28_cosetPeriod2
    (fun j => g32p_row09_groupEquiv (g32p_row28_cosetMonodromies2 j)) g32p_row28_cosetActualMonodromy2]
  simp only [g32p_row28_cosetCharacter2]
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

theorem g32p_row28_exponents :
    (g32p_exponents g32p_row28_finiteSupplier).Perm (expandExps [(2, 144), (4, 144)]) := by
  have h0 : papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_classDatum 0) = (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row28_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 128)).val.map
      (fun j => Multiplicative.toAdd (g32p_row28_cosetExponents0 j))).filter (· ≠ 0) = (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have h1 : papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_classDatum 6) = (([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row28_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 128)).val.map
      (fun j => Multiplicative.toAdd (g32p_row28_cosetExponents1 j))).filter (· ≠ 0) = (([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have h2 : papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_classDatum 12) = (([] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    change papersExps g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row28_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 160)).val.map
      (fun j => Multiplicative.toAdd (g32p_row28_cosetExponents2 j))).filter (· ≠ 0) = (([] : List (ZMod 6)) : Multiset (ZMod 6))
    decide +kernel
  have hs : papersExpsTuple g32p_row28_finiteSupplier.H g32p_row28_finiteSupplier.χ g32p_classList =
      6 • (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 6)) : Multiset (ZMod 6)) + 6 • (([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List (ZMod 6)) : Multiset (ZMod 6)) + (([] : List (ZMod 6)) : Multiset (ZMod 6)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (6 • (([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : List (ZMod 6)) : Multiset (ZMod 6)) + 6 • (([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List (ZMod 6)) : Multiset (ZMod 6)) + (([] : List (ZMod 6)) : Multiset (ZMod 6))).map ZMod.val = ↑(expandExps [(2, 144), (4, 144)])
  decide +kernel

theorem g32p_row28_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 28 ∧ r.m = g32p_row28_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row28_finiteSupplier.H ∧
      (g32p_exponents g32p_row28_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨28, (-1), 486, 6, 913, 288, 2112, some 2, [(2, 144), (4, 144)], .S⟩, ?_, rfl, rfl, g32p_row28_finiteSupplier_order.symm, g32p_row28_exponents⟩
  decide

def g32p_row28_complexWitness : g32p_row28_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row28_finiteSupplier

theorem g32p_row28_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 28 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row28_finiteSupplier, g32p_row28_complexWitness, g32p_complexCharacter_apply _,
    g32p_row28_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
