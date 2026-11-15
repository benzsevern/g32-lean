import HodgeLean.Foundations.Program.G32PropFourSixPacked1070
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness13CosetOrbitEquiv
import HodgeLean.Foundations.Program.G32PropFourSixPacked1044

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetQuotientStep (b : Fin 3) (i : Fin 6480) :
    g32p_row13_cosetEquiv (g32p_row13_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row13_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row13_cosetActualRepresentatives (g32p_row13_cosetBranchNext b i)) : g32p_G ⧸ g32p_row13_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row13_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row13_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row13_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row13_groupEquiv (g32p_row13_cosetBranchFactor b i)).property

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetBranchMatrix2 : g32p_row13_cosetBranchMatrices 2 = g32p_cosetIntegralBranches 2 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetCycleSteps2 : ∀ cycle ∈ g32p_row13_cosetCycles2,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row13_cosetBranchNext 2 ⟨i % 6480, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetInverse2 : ∀ i : Fin 6480,
    ((g32p_row13_cosetBranchNext 2)^[1]) (g32p_row13_cosetBranchNext 2 i) = i ∧
    g32p_row13_cosetBranchNext 2 (((g32p_row13_cosetBranchNext 2)^[1]) i) = i := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetNextLabels2 : ∀ i : Fin 6480, g32p_row13_cosetLabels2 (g32p_row13_cosetBranchNext 2 i) = g32p_row13_cosetLabels2 i := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetPeriods2 : ∀ j : Fin 3312, 0 < g32p_row13_cosetLengths2 j ∧ (g32p_row13_cosetBranchNext 2)^[g32p_row13_cosetLengths2 j] (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧ ∀ t : Fin (g32p_row13_cosetLengths2 j), 0 < t.val → (g32p_row13_cosetBranchNext 2)^[t.val] (g32p_row13_cosetRoots2 j) ≠ g32p_row13_cosetRoots2 j := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetPermutation2 : Function.Bijective (g32p_row13_cosetBranchNext 2) := by
  have hl : Function.LeftInverse ((g32p_row13_cosetBranchNext 2)^[1]) (g32p_row13_cosetBranchNext 2) :=
    fun i => (g32p_row13_cosetInverse2 i).1
  have hr : Function.RightInverse ((g32p_row13_cosetBranchNext 2)^[1]) (g32p_row13_cosetBranchNext 2) :=
    fun i => (g32p_row13_cosetInverse2 i).2
  exact ⟨hl.injective, hr.surjective⟩


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetReach2 : ∀ i : Fin 6480, (g32p_row13_cosetBranchNext 2)^[g32p_row13_cosetDistances2 i] (g32p_row13_cosetRoots2 (g32p_row13_cosetLabels2 i)) = i := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetRootLabels2 : ∀ j : Fin 3312, g32p_row13_cosetLabels2 (g32p_row13_cosetRoots2 j) = j := by
  decide +kernel

end HodgeLean.Foundations.Program

end
