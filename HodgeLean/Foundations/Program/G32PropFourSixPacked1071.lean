import HodgeLean.Foundations.Program.G32PropFourSixPacked1044
import HodgeLean.Foundations.Program.G32PropFourSixPacked1070
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_involutionPart0006 (r : Fin 512) :
    let j := g32p_finWideBlockIndex 3312 6 r
    ((g32p_row13_cosetLengths2 j = 1 ∧
      g32p_row13_cosetBranchNext 2 (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧
      g32p_row13_cosetMonodromies2 j = g32p_row13_cosetBranchFactor 2 (g32p_row13_cosetRoots2 j)) ∨
    (g32p_row13_cosetLengths2 j = 2 ∧ g32p_row13_cosetMonodromies2 j = 0)) ∧
    g32p_row13_characterValues (g32p_row13_cosetMonodromies2 j) = g32p_row13_cosetExponents2 j := by
  revert r
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetInvolutionCases2 (j : Fin 3312) :
    ((g32p_row13_cosetLengths2 j = 1 ∧
      g32p_row13_cosetBranchNext 2 (g32p_row13_cosetRoots2 j) = g32p_row13_cosetRoots2 j ∧
      g32p_row13_cosetMonodromies2 j = g32p_row13_cosetBranchFactor 2 (g32p_row13_cosetRoots2 j)) ∨
    (g32p_row13_cosetLengths2 j = 2 ∧ g32p_row13_cosetMonodromies2 j = 0)) ∧
    g32p_row13_characterValues (g32p_row13_cosetMonodromies2 j) = g32p_row13_cosetExponents2 j := by
  revert j
  apply g32p_forall_fin_wide_blocks
  intro q
  fin_cases q
  · exact g32p_row13_involutionPart0000
  · exact g32p_row13_involutionPart0001
  · exact g32p_row13_involutionPart0002
  · exact g32p_row13_involutionPart0003
  · exact g32p_row13_involutionPart0004
  · exact g32p_row13_involutionPart0005
  · exact g32p_row13_involutionPart0006

end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetActualMonodromy2 (j : Fin 3312) :
    (g32p_cosetBranches 2) ^ g32p_row13_cosetLengths2 j * g32p_row13_cosetActualRepresentatives (g32p_row13_cosetRoots2 j) =
      g32p_row13_cosetActualRepresentatives (g32p_row13_cosetRoots2 j) *
        (g32p_row13_groupEquiv (g32p_row13_cosetMonodromies2 j) : g32p_G) := by
  rcases (g32p_row13_cosetInvolutionCases2 j).1 with h | h
  · rcases h with ⟨hl, hn, hm⟩
    rw [hl, pow_one, hm]
    simpa only [hn] using
      g32p_row13_cosetActualBranchStep 2 (g32p_row13_cosetRoots2 j)
  · rcases h with ⟨hl, hm⟩
    have hg : (g32p_cosetBranches 2) ^ 2 = 1 := g32p_branch_power 12
    rw [hl, hm, g32p_row13_groupEquiv_one, Subgroup.coe_one, hg, one_mul, mul_one]


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetCharacter2 (j : Fin 3312) :
    g32p_row13_finiteSupplier.χ (g32p_row13_groupEquiv (g32p_row13_cosetMonodromies2 j)) = g32p_row13_cosetExponents2 j := by
  rw [g32p_row13_finiteSupplier_value]
  exact (g32p_row13_cosetInvolutionCases2 j).2

end HodgeLean.Foundations.Program

end
end
