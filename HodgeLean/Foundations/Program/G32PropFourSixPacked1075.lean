import HodgeLean.Foundations.Program.G32PropFourSixPacked1070
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixPacked1074
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness13CosetOrbitEquiv
import HodgeLean.Foundations.Program.G32PropFourSixPacked1073
import HodgeLean.Foundations.Program.G32PropFourSixPacked1071

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetPeriod2 (j : Fin 3312) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row13_cosetEquiv (g32p_row13_cosetRoots2 j)) = g32p_row13_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row13_cosetEquiv (g32p_row13_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row13_cosetQuotientStep 2) _ _ (g32p_row13_cosetPeriods2 j).1 (g32p_row13_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row13_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

theorem g32p_row13_cosetBranchExponents2 :
    papersExps g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 3312 => Multiplicative.toAdd (g32p_row13_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row13_cosetOrbitEquiv2
    (fun j => g32p_row13_cosetActualRepresentatives (g32p_row13_cosetRoots2 j)) (fun _ => rfl) g32p_row13_cosetLengths2 g32p_row13_cosetPeriod2
    (fun j => g32p_row13_groupEquiv (g32p_row13_cosetMonodromies2 j)) g32p_row13_cosetActualMonodromy2]
  simp only [g32p_row13_cosetCharacter2]
  rfl

end HodgeLean.Foundations.Program

end
end
