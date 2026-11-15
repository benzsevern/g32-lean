import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness03CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0636
import HodgeLean.Foundations.Program.G32PropFourSixPacked0637
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow03

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetWord_0032 :
    g32p_archiveIntegralWord (g32p_row03_cosetWords 32) = g32p_row03_cosetRepresentatives 32 := by
  decide +kernel

theorem g32p_row03_cosetGeneratorStep_0032 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row03_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetGeneratorNext s 32))
        (g32p_row03_groupNodes (g32p_row03_cosetGeneratorFactor s 32)) := by
  decide +kernel

theorem g32p_row03_cosetBranchStep_0032 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices s) (g32p_row03_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetBranchNext s 32))
        (g32p_row03_groupNodes (g32p_row03_cosetBranchFactor s 32)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetWord_0033 :
    g32p_archiveIntegralWord (g32p_row03_cosetWords 33) = g32p_row03_cosetRepresentatives 33 := by
  decide +kernel

theorem g32p_row03_cosetGeneratorStep_0033 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row03_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetGeneratorNext s 33))
        (g32p_row03_groupNodes (g32p_row03_cosetGeneratorFactor s 33)) := by
  decide +kernel

theorem g32p_row03_cosetBranchStep_0033 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices s) (g32p_row03_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetBranchNext s 33))
        (g32p_row03_groupNodes (g32p_row03_cosetBranchFactor s 33)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetWord_0034 :
    g32p_archiveIntegralWord (g32p_row03_cosetWords 34) = g32p_row03_cosetRepresentatives 34 := by
  decide +kernel

theorem g32p_row03_cosetGeneratorStep_0034 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row03_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetGeneratorNext s 34))
        (g32p_row03_groupNodes (g32p_row03_cosetGeneratorFactor s 34)) := by
  decide +kernel

theorem g32p_row03_cosetBranchStep_0034 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices s) (g32p_row03_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetBranchNext s 34))
        (g32p_row03_groupNodes (g32p_row03_cosetBranchFactor s 34)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetWord_0035 :
    g32p_archiveIntegralWord (g32p_row03_cosetWords 35) = g32p_row03_cosetRepresentatives 35 := by
  decide +kernel

theorem g32p_row03_cosetGeneratorStep_0035 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row03_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetGeneratorNext s 35))
        (g32p_row03_groupNodes (g32p_row03_cosetGeneratorFactor s 35)) := by
  decide +kernel

theorem g32p_row03_cosetBranchStep_0035 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices s) (g32p_row03_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetBranchNext s 35))
        (g32p_row03_groupNodes (g32p_row03_cosetBranchFactor s 35)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row03_cosetWord (i : Fin 36) :
    g32p_archiveIntegralWord (g32p_row03_cosetWords i) = g32p_row03_cosetRepresentatives i := by
  fin_cases i
  · exact g32p_row03_cosetWord_0000
  · exact g32p_row03_cosetWord_0001
  · exact g32p_row03_cosetWord_0002
  · exact g32p_row03_cosetWord_0003
  · exact g32p_row03_cosetWord_0004
  · exact g32p_row03_cosetWord_0005
  · exact g32p_row03_cosetWord_0006
  · exact g32p_row03_cosetWord_0007
  · exact g32p_row03_cosetWord_0008
  · exact g32p_row03_cosetWord_0009
  · exact g32p_row03_cosetWord_0010
  · exact g32p_row03_cosetWord_0011
  · exact g32p_row03_cosetWord_0012
  · exact g32p_row03_cosetWord_0013
  · exact g32p_row03_cosetWord_0014
  · exact g32p_row03_cosetWord_0015
  · exact g32p_row03_cosetWord_0016
  · exact g32p_row03_cosetWord_0017
  · exact g32p_row03_cosetWord_0018
  · exact g32p_row03_cosetWord_0019
  · exact g32p_row03_cosetWord_0020
  · exact g32p_row03_cosetWord_0021
  · exact g32p_row03_cosetWord_0022
  · exact g32p_row03_cosetWord_0023
  · exact g32p_row03_cosetWord_0024
  · exact g32p_row03_cosetWord_0025
  · exact g32p_row03_cosetWord_0026
  · exact g32p_row03_cosetWord_0027
  · exact g32p_row03_cosetWord_0028
  · exact g32p_row03_cosetWord_0029
  · exact g32p_row03_cosetWord_0030
  · exact g32p_row03_cosetWord_0031
  · exact g32p_row03_cosetWord_0032
  · exact g32p_row03_cosetWord_0033
  · exact g32p_row03_cosetWord_0034
  · exact g32p_row03_cosetWord_0035

def g32p_row03_cosetActualRepresentatives (i : Fin 36) : g32p_G := g32p_archiveWord (g32p_row03_cosetWords i)

theorem g32p_row03_cosetActualRepresentatives_map (i : Fin 36) :
    b4b_toMatrix (g32p_row03_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row03_cosetRepresentatives i)) := by
  rw [g32p_row03_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row03_cosetWord]

theorem g32p_row03_cosetGeneratorStep (s : Fin 4) (i : Fin 36) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row03_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives (g32p_row03_cosetGeneratorNext s i))
        (g32p_row03_groupNodes (g32p_row03_cosetGeneratorFactor s i)) := by
  fin_cases i
  · exact g32p_row03_cosetGeneratorStep_0000 s
  · exact g32p_row03_cosetGeneratorStep_0001 s
  · exact g32p_row03_cosetGeneratorStep_0002 s
  · exact g32p_row03_cosetGeneratorStep_0003 s
  · exact g32p_row03_cosetGeneratorStep_0004 s
  · exact g32p_row03_cosetGeneratorStep_0005 s
  · exact g32p_row03_cosetGeneratorStep_0006 s
  · exact g32p_row03_cosetGeneratorStep_0007 s
  · exact g32p_row03_cosetGeneratorStep_0008 s
  · exact g32p_row03_cosetGeneratorStep_0009 s
  · exact g32p_row03_cosetGeneratorStep_0010 s
  · exact g32p_row03_cosetGeneratorStep_0011 s
  · exact g32p_row03_cosetGeneratorStep_0012 s
  · exact g32p_row03_cosetGeneratorStep_0013 s
  · exact g32p_row03_cosetGeneratorStep_0014 s
  · exact g32p_row03_cosetGeneratorStep_0015 s
  · exact g32p_row03_cosetGeneratorStep_0016 s
  · exact g32p_row03_cosetGeneratorStep_0017 s
  · exact g32p_row03_cosetGeneratorStep_0018 s
  · exact g32p_row03_cosetGeneratorStep_0019 s
  · exact g32p_row03_cosetGeneratorStep_0020 s
  · exact g32p_row03_cosetGeneratorStep_0021 s
  · exact g32p_row03_cosetGeneratorStep_0022 s
  · exact g32p_row03_cosetGeneratorStep_0023 s
  · exact g32p_row03_cosetGeneratorStep_0024 s
  · exact g32p_row03_cosetGeneratorStep_0025 s
  · exact g32p_row03_cosetGeneratorStep_0026 s
  · exact g32p_row03_cosetGeneratorStep_0027 s
  · exact g32p_row03_cosetGeneratorStep_0028 s
  · exact g32p_row03_cosetGeneratorStep_0029 s
  · exact g32p_row03_cosetGeneratorStep_0030 s
  · exact g32p_row03_cosetGeneratorStep_0031 s
  · exact g32p_row03_cosetGeneratorStep_0032 s
  · exact g32p_row03_cosetGeneratorStep_0033 s
  · exact g32p_row03_cosetGeneratorStep_0034 s
  · exact g32p_row03_cosetGeneratorStep_0035 s

theorem g32p_row03_cosetActualStep (s : Fin 4) (i : Fin 36) :
    g32p_word (g32p_archiveWords s) * g32p_row03_cosetActualRepresentatives i =
      g32p_row03_cosetActualRepresentatives (g32p_row03_cosetGeneratorNext s i) *
        (g32p_row03_groupEquiv (g32p_row03_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row03_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row03_cosetActualRepresentatives (g32p_row03_cosetGeneratorNext s i) *
      (g32p_row03_groupEquiv (g32p_row03_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row03_cosetActualRepresentatives_map,
    g32p_row03_cosetActualRepresentatives_map, g32p_row03_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row03_cosetGeneratorStep]

theorem g32p_row03_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row03_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row03_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row03_cosetGeneratorNext
      (fun s i => g32p_row03_groupEquiv (g32p_row03_cosetGeneratorFactor s i))
    exact g32p_row03_cosetActualStep
  · rw [g32p_row03_finiteSupplier_order]
    have hg : Nat.card g32p_G = 155520 :=
      (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
        HurwitzPrymRex_g32_ncard
    rw [hg]


end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 0)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 0)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 0) = g32p_row03_cosetExponents0 0 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 1)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 1)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 1) = g32p_row03_cosetExponents0 1 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 2)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 2)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 2) = g32p_row03_cosetExponents0 2 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 3)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 3)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 3) = g32p_row03_cosetExponents0 3 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 4)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 4)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 4) = g32p_row03_cosetExponents0 4 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 5)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 5)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 5) = g32p_row03_cosetExponents0 5 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 6)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 6)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 6) = g32p_row03_cosetExponents0 6 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 7)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 7)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 7) = g32p_row03_cosetExponents0 7 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 11)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 8)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 8) = g32p_row03_cosetExponents0 8 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 12)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 9)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 9) = g32p_row03_cosetExponents0 9 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row03_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row03_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row03_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row03_cosetRepresentatives 17)
        (g32p_row03_groupNodes (g32p_row03_cosetMonodromies0 10)) ∧
    g32p_row03_characterValues (g32p_row03_cosetMonodromies0 10) = g32p_row03_cosetExponents0 10 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
