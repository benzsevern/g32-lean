import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness04CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow04

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetWord_0000 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 0) = g32p_row04_cosetRepresentatives 0 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0000 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 0))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 0)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0000 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 0))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 0)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0001 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 1) = g32p_row04_cosetRepresentatives 1 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0001 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 1))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 1)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0001 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 1))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 1)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0002 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 2) = g32p_row04_cosetRepresentatives 2 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0002 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 2))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 2)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0002 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 2))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 2)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0003 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 3) = g32p_row04_cosetRepresentatives 3 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0003 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 3))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 3)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0003 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 3))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 3)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0004 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 4) = g32p_row04_cosetRepresentatives 4 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0004 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 4))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 4)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0004 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 4))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 4)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0005 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 5) = g32p_row04_cosetRepresentatives 5 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0005 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 5))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 5)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0005 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 5))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 5)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0006 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 6) = g32p_row04_cosetRepresentatives 6 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0006 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 6))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 6)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0006 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 6))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 6)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0007 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 7) = g32p_row04_cosetRepresentatives 7 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0007 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 7))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 7)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0007 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 7))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 7)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0008 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 8) = g32p_row04_cosetRepresentatives 8 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0008 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 8))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 8)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0008 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 8))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 8)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0009 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 9) = g32p_row04_cosetRepresentatives 9 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0009 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 9))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 9)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0009 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 9))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 9)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0010 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 10) = g32p_row04_cosetRepresentatives 10 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0010 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 10))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 10)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0010 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 10))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 10)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0011 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 11) = g32p_row04_cosetRepresentatives 11 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0011 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 11))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 11)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0011 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 11))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 11)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0012 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 12) = g32p_row04_cosetRepresentatives 12 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0012 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 12))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 12)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0012 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 12))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 12)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0013 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 13) = g32p_row04_cosetRepresentatives 13 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0013 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 13))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 13)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0013 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 13))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 13)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0014 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 14) = g32p_row04_cosetRepresentatives 14 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0014 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 14))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 14)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0014 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 14))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 14)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0015 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 15) = g32p_row04_cosetRepresentatives 15 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0015 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 15))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 15)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0015 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 15))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 15)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetWord_0016 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 16) = g32p_row04_cosetRepresentatives 16 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0016 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 16))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 16)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0016 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 16))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 16)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0017 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 17) = g32p_row04_cosetRepresentatives 17 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0017 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 17))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 17)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0017 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 17))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 17)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0018 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 18) = g32p_row04_cosetRepresentatives 18 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0018 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 18))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 18)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0018 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 18))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 18)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0019 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 19) = g32p_row04_cosetRepresentatives 19 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0019 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 19))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 19)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0019 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 19))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 19)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0020 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 20) = g32p_row04_cosetRepresentatives 20 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0020 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 20))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 20)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0020 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 20))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 20)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0021 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 21) = g32p_row04_cosetRepresentatives 21 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0021 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 21))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 21)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0021 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 21))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 21)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0022 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 22) = g32p_row04_cosetRepresentatives 22 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0022 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 22))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 22)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0022 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 22))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 22)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0023 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 23) = g32p_row04_cosetRepresentatives 23 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0023 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 23))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 23)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0023 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 23))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 23)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0024 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 24) = g32p_row04_cosetRepresentatives 24 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0024 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 24))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 24)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0024 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 24))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 24)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0025 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 25) = g32p_row04_cosetRepresentatives 25 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0025 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 25))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 25)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0025 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 25))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 25)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0026 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 26) = g32p_row04_cosetRepresentatives 26 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0026 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 26))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 26)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0026 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 26))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 26)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0027 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 27) = g32p_row04_cosetRepresentatives 27 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0027 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 27))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 27)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0027 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 27))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 27)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0028 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 28) = g32p_row04_cosetRepresentatives 28 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0028 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 28))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 28)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0028 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 28))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 28)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0029 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 29) = g32p_row04_cosetRepresentatives 29 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0029 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 29))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 29)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0029 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 29))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 29)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0030 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 30) = g32p_row04_cosetRepresentatives 30 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0030 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 30))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 30)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0030 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 30))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 30)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0031 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 31) = g32p_row04_cosetRepresentatives 31 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0031 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 31))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 31)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0031 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 31))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 31)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetWord_0032 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 32) = g32p_row04_cosetRepresentatives 32 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0032 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 32))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 32)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0032 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 32))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 32)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0033 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 33) = g32p_row04_cosetRepresentatives 33 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0033 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 33))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 33)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0033 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 33))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 33)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0034 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 34) = g32p_row04_cosetRepresentatives 34 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0034 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 34))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 34)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0034 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 34))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 34)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0035 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 35) = g32p_row04_cosetRepresentatives 35 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0035 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 35))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 35)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0035 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 35))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 35)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0036 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 36) = g32p_row04_cosetRepresentatives 36 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0036 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 36))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 36)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0036 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 36))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 36)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0037 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 37) = g32p_row04_cosetRepresentatives 37 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0037 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 37))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 37)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0037 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 37))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 37)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0038 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 38) = g32p_row04_cosetRepresentatives 38 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0038 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 38))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 38)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0038 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 38))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 38)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0039 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 39) = g32p_row04_cosetRepresentatives 39 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0039 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 39))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 39)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0039 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 39))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 39)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0040 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 40) = g32p_row04_cosetRepresentatives 40 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0040 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 40))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 40)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0040 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 40))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 40)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0041 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 41) = g32p_row04_cosetRepresentatives 41 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0041 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 41))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 41)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0041 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 41))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 41)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0042 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 42) = g32p_row04_cosetRepresentatives 42 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0042 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 42))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 42)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0042 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 42))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 42)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0043 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 43) = g32p_row04_cosetRepresentatives 43 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0043 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 43))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 43)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0043 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 43))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 43)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0044 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 44) = g32p_row04_cosetRepresentatives 44 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0044 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 44))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 44)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0044 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 44))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 44)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0045 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 45) = g32p_row04_cosetRepresentatives 45 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0045 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 45))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 45)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0045 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 45))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 45)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0046 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 46) = g32p_row04_cosetRepresentatives 46 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0046 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 46))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 46)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0046 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 46))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 46)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0047 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 47) = g32p_row04_cosetRepresentatives 47 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0047 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 47))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 47)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0047 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 47))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 47)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetWord_0048 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 48) = g32p_row04_cosetRepresentatives 48 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0048 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 48))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 48)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0048 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 48))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 48)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0049 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 49) = g32p_row04_cosetRepresentatives 49 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0049 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 49))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 49)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0049 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 49))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 49)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0050 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 50) = g32p_row04_cosetRepresentatives 50 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0050 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 50))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 50)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0050 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 50))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 50)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0051 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 51) = g32p_row04_cosetRepresentatives 51 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0051 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 51))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 51)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0051 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 51))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 51)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0052 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 52) = g32p_row04_cosetRepresentatives 52 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0052 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 52))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 52)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0052 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 52))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 52)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0053 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 53) = g32p_row04_cosetRepresentatives 53 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0053 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 53))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 53)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0053 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 53))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 53)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0054 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 54) = g32p_row04_cosetRepresentatives 54 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0054 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 54))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 54)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0054 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 54))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 54)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0055 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 55) = g32p_row04_cosetRepresentatives 55 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0055 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 55))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 55)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0055 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 55))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 55)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0056 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 56) = g32p_row04_cosetRepresentatives 56 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0056 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 56))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 56)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0056 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 56))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 56)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0057 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 57) = g32p_row04_cosetRepresentatives 57 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0057 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 57) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 57))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 57)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0057 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 57) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 57))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 57)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0058 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 58) = g32p_row04_cosetRepresentatives 58 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0058 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 58))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 58)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0058 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 58))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 58)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0059 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 59) = g32p_row04_cosetRepresentatives 59 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0059 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 59))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 59)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0059 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 59))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 59)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0060 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 60) = g32p_row04_cosetRepresentatives 60 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0060 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 60) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 60))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 60)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0060 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 60) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 60))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 60)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0061 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 61) = g32p_row04_cosetRepresentatives 61 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0061 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 61))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 61)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0061 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 61))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 61)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0062 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 62) = g32p_row04_cosetRepresentatives 62 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0062 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 62))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 62)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0062 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 62))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 62)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0063 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 63) = g32p_row04_cosetRepresentatives 63 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0063 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 63))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 63)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0063 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 63))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 63)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetWord_0064 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 64) = g32p_row04_cosetRepresentatives 64 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0064 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 64))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 64)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0064 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 64))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 64)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0065 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 65) = g32p_row04_cosetRepresentatives 65 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0065 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 65))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 65)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0065 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 65))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 65)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0066 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 66) = g32p_row04_cosetRepresentatives 66 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0066 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 66))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 66)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0066 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 66))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 66)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0067 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 67) = g32p_row04_cosetRepresentatives 67 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0067 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 67) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 67))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 67)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0067 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 67) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 67))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 67)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0068 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 68) = g32p_row04_cosetRepresentatives 68 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0068 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 68))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 68)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0068 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 68))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 68)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0069 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 69) = g32p_row04_cosetRepresentatives 69 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0069 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 69))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 69)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0069 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 69))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 69)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0070 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 70) = g32p_row04_cosetRepresentatives 70 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0070 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 70))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 70)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0070 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 70))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 70)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0071 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 71) = g32p_row04_cosetRepresentatives 71 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0071 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 71))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 71)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0071 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 71))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 71)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0072 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 72) = g32p_row04_cosetRepresentatives 72 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0072 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 72))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 72)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0072 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 72))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 72)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0073 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 73) = g32p_row04_cosetRepresentatives 73 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0073 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 73))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 73)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0073 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 73))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 73)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0074 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 74) = g32p_row04_cosetRepresentatives 74 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0074 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 74))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 74)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0074 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 74))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 74)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0075 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 75) = g32p_row04_cosetRepresentatives 75 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0075 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 75))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 75)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0075 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 75))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 75)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0076 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 76) = g32p_row04_cosetRepresentatives 76 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0076 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 76))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 76)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0076 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 76))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 76)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0077 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 77) = g32p_row04_cosetRepresentatives 77 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0077 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 77))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 77)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0077 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 77))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 77)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0078 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 78) = g32p_row04_cosetRepresentatives 78 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0078 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 78) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 78))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 78)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0078 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 78) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 78))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 78)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0079 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 79) = g32p_row04_cosetRepresentatives 79 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0079 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 79))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 79)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0079 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 79))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 79)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetWord_0080 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 80) = g32p_row04_cosetRepresentatives 80 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0080 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 80))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 80)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0080 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 80))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 80)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0081 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 81) = g32p_row04_cosetRepresentatives 81 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0081 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 81))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 81)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0081 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 81))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 81)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0082 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 82) = g32p_row04_cosetRepresentatives 82 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0082 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 82))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 82)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0082 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 82))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 82)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0083 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 83) = g32p_row04_cosetRepresentatives 83 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0083 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 83) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 83))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 83)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0083 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 83) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 83))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 83)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0084 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 84) = g32p_row04_cosetRepresentatives 84 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0084 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 84) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 84))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 84)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0084 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 84) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 84))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 84)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0085 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 85) = g32p_row04_cosetRepresentatives 85 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0085 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 85))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 85)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0085 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 85))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 85)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0086 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 86) = g32p_row04_cosetRepresentatives 86 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0086 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 86) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 86))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 86)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0086 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 86) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 86))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 86)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0087 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 87) = g32p_row04_cosetRepresentatives 87 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0087 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 87) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 87))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 87)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0087 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 87) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 87))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 87)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0088 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 88) = g32p_row04_cosetRepresentatives 88 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0088 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 88))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 88)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0088 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 88))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 88)) := by
  decide +kernel

theorem g32p_row04_cosetWord_0089 :
    g32p_archiveIntegralWord (g32p_row04_cosetWords 89) = g32p_row04_cosetRepresentatives 89 := by
  decide +kernel

theorem g32p_row04_cosetGeneratorStep_0089 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives 89) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s 89))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s 89)) := by
  decide +kernel

theorem g32p_row04_cosetBranchStep_0089 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices s) (g32p_row04_cosetRepresentatives 89) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetBranchNext s 89))
        (g32p_row04_groupNodes (g32p_row04_cosetBranchFactor s 89)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row04_cosetWord (i : Fin 90) :
    g32p_archiveIntegralWord (g32p_row04_cosetWords i) = g32p_row04_cosetRepresentatives i := by
  fin_cases i
  · exact g32p_row04_cosetWord_0000
  · exact g32p_row04_cosetWord_0001
  · exact g32p_row04_cosetWord_0002
  · exact g32p_row04_cosetWord_0003
  · exact g32p_row04_cosetWord_0004
  · exact g32p_row04_cosetWord_0005
  · exact g32p_row04_cosetWord_0006
  · exact g32p_row04_cosetWord_0007
  · exact g32p_row04_cosetWord_0008
  · exact g32p_row04_cosetWord_0009
  · exact g32p_row04_cosetWord_0010
  · exact g32p_row04_cosetWord_0011
  · exact g32p_row04_cosetWord_0012
  · exact g32p_row04_cosetWord_0013
  · exact g32p_row04_cosetWord_0014
  · exact g32p_row04_cosetWord_0015
  · exact g32p_row04_cosetWord_0016
  · exact g32p_row04_cosetWord_0017
  · exact g32p_row04_cosetWord_0018
  · exact g32p_row04_cosetWord_0019
  · exact g32p_row04_cosetWord_0020
  · exact g32p_row04_cosetWord_0021
  · exact g32p_row04_cosetWord_0022
  · exact g32p_row04_cosetWord_0023
  · exact g32p_row04_cosetWord_0024
  · exact g32p_row04_cosetWord_0025
  · exact g32p_row04_cosetWord_0026
  · exact g32p_row04_cosetWord_0027
  · exact g32p_row04_cosetWord_0028
  · exact g32p_row04_cosetWord_0029
  · exact g32p_row04_cosetWord_0030
  · exact g32p_row04_cosetWord_0031
  · exact g32p_row04_cosetWord_0032
  · exact g32p_row04_cosetWord_0033
  · exact g32p_row04_cosetWord_0034
  · exact g32p_row04_cosetWord_0035
  · exact g32p_row04_cosetWord_0036
  · exact g32p_row04_cosetWord_0037
  · exact g32p_row04_cosetWord_0038
  · exact g32p_row04_cosetWord_0039
  · exact g32p_row04_cosetWord_0040
  · exact g32p_row04_cosetWord_0041
  · exact g32p_row04_cosetWord_0042
  · exact g32p_row04_cosetWord_0043
  · exact g32p_row04_cosetWord_0044
  · exact g32p_row04_cosetWord_0045
  · exact g32p_row04_cosetWord_0046
  · exact g32p_row04_cosetWord_0047
  · exact g32p_row04_cosetWord_0048
  · exact g32p_row04_cosetWord_0049
  · exact g32p_row04_cosetWord_0050
  · exact g32p_row04_cosetWord_0051
  · exact g32p_row04_cosetWord_0052
  · exact g32p_row04_cosetWord_0053
  · exact g32p_row04_cosetWord_0054
  · exact g32p_row04_cosetWord_0055
  · exact g32p_row04_cosetWord_0056
  · exact g32p_row04_cosetWord_0057
  · exact g32p_row04_cosetWord_0058
  · exact g32p_row04_cosetWord_0059
  · exact g32p_row04_cosetWord_0060
  · exact g32p_row04_cosetWord_0061
  · exact g32p_row04_cosetWord_0062
  · exact g32p_row04_cosetWord_0063
  · exact g32p_row04_cosetWord_0064
  · exact g32p_row04_cosetWord_0065
  · exact g32p_row04_cosetWord_0066
  · exact g32p_row04_cosetWord_0067
  · exact g32p_row04_cosetWord_0068
  · exact g32p_row04_cosetWord_0069
  · exact g32p_row04_cosetWord_0070
  · exact g32p_row04_cosetWord_0071
  · exact g32p_row04_cosetWord_0072
  · exact g32p_row04_cosetWord_0073
  · exact g32p_row04_cosetWord_0074
  · exact g32p_row04_cosetWord_0075
  · exact g32p_row04_cosetWord_0076
  · exact g32p_row04_cosetWord_0077
  · exact g32p_row04_cosetWord_0078
  · exact g32p_row04_cosetWord_0079
  · exact g32p_row04_cosetWord_0080
  · exact g32p_row04_cosetWord_0081
  · exact g32p_row04_cosetWord_0082
  · exact g32p_row04_cosetWord_0083
  · exact g32p_row04_cosetWord_0084
  · exact g32p_row04_cosetWord_0085
  · exact g32p_row04_cosetWord_0086
  · exact g32p_row04_cosetWord_0087
  · exact g32p_row04_cosetWord_0088
  · exact g32p_row04_cosetWord_0089

def g32p_row04_cosetActualRepresentatives (i : Fin 90) : g32p_G := g32p_archiveWord (g32p_row04_cosetWords i)

theorem g32p_row04_cosetActualRepresentatives_map (i : Fin 90) :
    b4b_toMatrix (g32p_row04_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row04_cosetRepresentatives i)) := by
  rw [g32p_row04_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row04_cosetWord]

theorem g32p_row04_cosetGeneratorStep (s : Fin 4) (i : Fin 90) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row04_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives (g32p_row04_cosetGeneratorNext s i))
        (g32p_row04_groupNodes (g32p_row04_cosetGeneratorFactor s i)) := by
  fin_cases i
  · exact g32p_row04_cosetGeneratorStep_0000 s
  · exact g32p_row04_cosetGeneratorStep_0001 s
  · exact g32p_row04_cosetGeneratorStep_0002 s
  · exact g32p_row04_cosetGeneratorStep_0003 s
  · exact g32p_row04_cosetGeneratorStep_0004 s
  · exact g32p_row04_cosetGeneratorStep_0005 s
  · exact g32p_row04_cosetGeneratorStep_0006 s
  · exact g32p_row04_cosetGeneratorStep_0007 s
  · exact g32p_row04_cosetGeneratorStep_0008 s
  · exact g32p_row04_cosetGeneratorStep_0009 s
  · exact g32p_row04_cosetGeneratorStep_0010 s
  · exact g32p_row04_cosetGeneratorStep_0011 s
  · exact g32p_row04_cosetGeneratorStep_0012 s
  · exact g32p_row04_cosetGeneratorStep_0013 s
  · exact g32p_row04_cosetGeneratorStep_0014 s
  · exact g32p_row04_cosetGeneratorStep_0015 s
  · exact g32p_row04_cosetGeneratorStep_0016 s
  · exact g32p_row04_cosetGeneratorStep_0017 s
  · exact g32p_row04_cosetGeneratorStep_0018 s
  · exact g32p_row04_cosetGeneratorStep_0019 s
  · exact g32p_row04_cosetGeneratorStep_0020 s
  · exact g32p_row04_cosetGeneratorStep_0021 s
  · exact g32p_row04_cosetGeneratorStep_0022 s
  · exact g32p_row04_cosetGeneratorStep_0023 s
  · exact g32p_row04_cosetGeneratorStep_0024 s
  · exact g32p_row04_cosetGeneratorStep_0025 s
  · exact g32p_row04_cosetGeneratorStep_0026 s
  · exact g32p_row04_cosetGeneratorStep_0027 s
  · exact g32p_row04_cosetGeneratorStep_0028 s
  · exact g32p_row04_cosetGeneratorStep_0029 s
  · exact g32p_row04_cosetGeneratorStep_0030 s
  · exact g32p_row04_cosetGeneratorStep_0031 s
  · exact g32p_row04_cosetGeneratorStep_0032 s
  · exact g32p_row04_cosetGeneratorStep_0033 s
  · exact g32p_row04_cosetGeneratorStep_0034 s
  · exact g32p_row04_cosetGeneratorStep_0035 s
  · exact g32p_row04_cosetGeneratorStep_0036 s
  · exact g32p_row04_cosetGeneratorStep_0037 s
  · exact g32p_row04_cosetGeneratorStep_0038 s
  · exact g32p_row04_cosetGeneratorStep_0039 s
  · exact g32p_row04_cosetGeneratorStep_0040 s
  · exact g32p_row04_cosetGeneratorStep_0041 s
  · exact g32p_row04_cosetGeneratorStep_0042 s
  · exact g32p_row04_cosetGeneratorStep_0043 s
  · exact g32p_row04_cosetGeneratorStep_0044 s
  · exact g32p_row04_cosetGeneratorStep_0045 s
  · exact g32p_row04_cosetGeneratorStep_0046 s
  · exact g32p_row04_cosetGeneratorStep_0047 s
  · exact g32p_row04_cosetGeneratorStep_0048 s
  · exact g32p_row04_cosetGeneratorStep_0049 s
  · exact g32p_row04_cosetGeneratorStep_0050 s
  · exact g32p_row04_cosetGeneratorStep_0051 s
  · exact g32p_row04_cosetGeneratorStep_0052 s
  · exact g32p_row04_cosetGeneratorStep_0053 s
  · exact g32p_row04_cosetGeneratorStep_0054 s
  · exact g32p_row04_cosetGeneratorStep_0055 s
  · exact g32p_row04_cosetGeneratorStep_0056 s
  · exact g32p_row04_cosetGeneratorStep_0057 s
  · exact g32p_row04_cosetGeneratorStep_0058 s
  · exact g32p_row04_cosetGeneratorStep_0059 s
  · exact g32p_row04_cosetGeneratorStep_0060 s
  · exact g32p_row04_cosetGeneratorStep_0061 s
  · exact g32p_row04_cosetGeneratorStep_0062 s
  · exact g32p_row04_cosetGeneratorStep_0063 s
  · exact g32p_row04_cosetGeneratorStep_0064 s
  · exact g32p_row04_cosetGeneratorStep_0065 s
  · exact g32p_row04_cosetGeneratorStep_0066 s
  · exact g32p_row04_cosetGeneratorStep_0067 s
  · exact g32p_row04_cosetGeneratorStep_0068 s
  · exact g32p_row04_cosetGeneratorStep_0069 s
  · exact g32p_row04_cosetGeneratorStep_0070 s
  · exact g32p_row04_cosetGeneratorStep_0071 s
  · exact g32p_row04_cosetGeneratorStep_0072 s
  · exact g32p_row04_cosetGeneratorStep_0073 s
  · exact g32p_row04_cosetGeneratorStep_0074 s
  · exact g32p_row04_cosetGeneratorStep_0075 s
  · exact g32p_row04_cosetGeneratorStep_0076 s
  · exact g32p_row04_cosetGeneratorStep_0077 s
  · exact g32p_row04_cosetGeneratorStep_0078 s
  · exact g32p_row04_cosetGeneratorStep_0079 s
  · exact g32p_row04_cosetGeneratorStep_0080 s
  · exact g32p_row04_cosetGeneratorStep_0081 s
  · exact g32p_row04_cosetGeneratorStep_0082 s
  · exact g32p_row04_cosetGeneratorStep_0083 s
  · exact g32p_row04_cosetGeneratorStep_0084 s
  · exact g32p_row04_cosetGeneratorStep_0085 s
  · exact g32p_row04_cosetGeneratorStep_0086 s
  · exact g32p_row04_cosetGeneratorStep_0087 s
  · exact g32p_row04_cosetGeneratorStep_0088 s
  · exact g32p_row04_cosetGeneratorStep_0089 s

theorem g32p_row04_cosetActualStep (s : Fin 4) (i : Fin 90) :
    g32p_word (g32p_archiveWords s) * g32p_row04_cosetActualRepresentatives i =
      g32p_row04_cosetActualRepresentatives (g32p_row04_cosetGeneratorNext s i) *
        (g32p_row04_groupEquiv (g32p_row04_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row04_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row04_cosetActualRepresentatives (g32p_row04_cosetGeneratorNext s i) *
      (g32p_row04_groupEquiv (g32p_row04_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row04_cosetActualRepresentatives_map,
    g32p_row04_cosetActualRepresentatives_map, g32p_row04_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row04_cosetGeneratorStep]

theorem g32p_row04_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row04_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row04_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row04_cosetGeneratorNext
      (fun s i => g32p_row04_groupEquiv (g32p_row04_cosetGeneratorFactor s i))
    exact g32p_row04_cosetActualStep
  · rw [g32p_row04_finiteSupplier_order]
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

theorem g32p_row04_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 0)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 0)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 0) = g32p_row04_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 1)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 1)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 1) = g32p_row04_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 2)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 2)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 2) = g32p_row04_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 3)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 3)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 3) = g32p_row04_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 4)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 4)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 4) = g32p_row04_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 5)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 5)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 5) = g32p_row04_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 6)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 6)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 6) = g32p_row04_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 9)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 7)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 7) = g32p_row04_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 10)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 8)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 8) = g32p_row04_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 11)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 9)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 9) = g32p_row04_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 12)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 10)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 10) = g32p_row04_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 13)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 11)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 11) = g32p_row04_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 15)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 12)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 12) = g32p_row04_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 16)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 13)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 13) = g32p_row04_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 17)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 14)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 14) = g32p_row04_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 18)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 15)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 15) = g32p_row04_cosetExponents0 15 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 19)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 16)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 16) = g32p_row04_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 20)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 17)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 17) = g32p_row04_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 21)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 18)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 18) = g32p_row04_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 24)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 19)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 19) = g32p_row04_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 25)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 20)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 20) = g32p_row04_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 26)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 21)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 21) = g32p_row04_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 28)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 22)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 22) = g32p_row04_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 29)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 23)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 23) = g32p_row04_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 31)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 24)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 24) = g32p_row04_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 32)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 25)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 25) = g32p_row04_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 37)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 26)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 26) = g32p_row04_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 38)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 27)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 27) = g32p_row04_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 39)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 28)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 28) = g32p_row04_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 42)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 29)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 29) = g32p_row04_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 43)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 30)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 30) = g32p_row04_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 45)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 31)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 31) = g32p_row04_cosetExponents0 31 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetMonodromy_0_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 47)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 32)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 32) = g32p_row04_cosetExponents0 32 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 53)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 33)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 33) = g32p_row04_cosetExponents0 33 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 54)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 34)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 34) = g32p_row04_cosetExponents0 34 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 62)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 35)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 35) = g32p_row04_cosetExponents0 35 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 64)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 36)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 36) = g32p_row04_cosetExponents0 36 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 68)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 37)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 37) = g32p_row04_cosetExponents0 37 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 69)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 38)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 38) = g32p_row04_cosetExponents0 38 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 71)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 39)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 39) = g32p_row04_cosetExponents0 39 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 75)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 40)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 40) = g32p_row04_cosetExponents0 40 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_0_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 85)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies0 41)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies0 41) = g32p_row04_cosetExponents0 41 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetMonodromy_1_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 0)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 0)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 0) = g32p_row04_cosetExponents1 0 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 1)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 1)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 1) = g32p_row04_cosetExponents1 1 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 2)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 2)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 2) = g32p_row04_cosetExponents1 2 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 3)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 3)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 3) = g32p_row04_cosetExponents1 3 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 5)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 4)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 4) = g32p_row04_cosetExponents1 4 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 7)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 5)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 5) = g32p_row04_cosetExponents1 5 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 8)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 6)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 6) = g32p_row04_cosetExponents1 6 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 9)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 7)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 7) = g32p_row04_cosetExponents1 7 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 10)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 8)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 8) = g32p_row04_cosetExponents1 8 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 11)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 9)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 9) = g32p_row04_cosetExponents1 9 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 12)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 10)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 10) = g32p_row04_cosetExponents1 10 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 14)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 11)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 11) = g32p_row04_cosetExponents1 11 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 15)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 12)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 12) = g32p_row04_cosetExponents1 12 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 16)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 13)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 13) = g32p_row04_cosetExponents1 13 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 18)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 14)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 14) = g32p_row04_cosetExponents1 14 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 21)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 15)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 15) = g32p_row04_cosetExponents1 15 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetMonodromy_1_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 24)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 16)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 16) = g32p_row04_cosetExponents1 16 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 25)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 17)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 17) = g32p_row04_cosetExponents1 17 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 26)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 18)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 18) = g32p_row04_cosetExponents1 18 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 30)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 19)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 19) = g32p_row04_cosetExponents1 19 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 32)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 20)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 20) = g32p_row04_cosetExponents1 20 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 33)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 21)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 21) = g32p_row04_cosetExponents1 21 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 34)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 22)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 22) = g32p_row04_cosetExponents1 22 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 35)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 23)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 23) = g32p_row04_cosetExponents1 23 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 36)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 24)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 24) = g32p_row04_cosetExponents1 24 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 38)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 25)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 25) = g32p_row04_cosetExponents1 25 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 41)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 26)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 26) = g32p_row04_cosetExponents1 26 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 44)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 27)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 27) = g32p_row04_cosetExponents1 27 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 45)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 28)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 28) = g32p_row04_cosetExponents1 28 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 50)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 29)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 29) = g32p_row04_cosetExponents1 29 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 52)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 30)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 30) = g32p_row04_cosetExponents1 30 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 53)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 31)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 31) = g32p_row04_cosetExponents1 31 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetMonodromy_1_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 54)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 32)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 32) = g32p_row04_cosetExponents1 32 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 56)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 33)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 33) = g32p_row04_cosetExponents1 33 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 61)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 34)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 34) = g32p_row04_cosetExponents1 34 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 64)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 35)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 35) = g32p_row04_cosetExponents1 35 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 65)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 36)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 36) = g32p_row04_cosetExponents1 36 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 69)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 37)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 37) = g32p_row04_cosetExponents1 37 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 71)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 38)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 38) = g32p_row04_cosetExponents1 38 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 73)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 39)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 39) = g32p_row04_cosetExponents1 39 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row04_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 74)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 40)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 40) = g32p_row04_cosetExponents1 40 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_1_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 82)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies1 41)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies1 41) = g32p_row04_cosetExponents1 41 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetMonodromy_2_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 0)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 0)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 0) = g32p_row04_cosetExponents2 0 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 1)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 1)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 1) = g32p_row04_cosetExponents2 1 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 2)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 2)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 2) = g32p_row04_cosetExponents2 2 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 3)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 3)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 3) = g32p_row04_cosetExponents2 3 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 4)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 4)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 4) = g32p_row04_cosetExponents2 4 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 6)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 5)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 5) = g32p_row04_cosetExponents2 5 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 7)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 6)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 6) = g32p_row04_cosetExponents2 6 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 8)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 7)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 7) = g32p_row04_cosetExponents2 7 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 9)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 8)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 8) = g32p_row04_cosetExponents2 8 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 11)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 9)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 9) = g32p_row04_cosetExponents2 9 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 13)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 10)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 10) = g32p_row04_cosetExponents2 10 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 14)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 11)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 11) = g32p_row04_cosetExponents2 11 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 16)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 12)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 12) = g32p_row04_cosetExponents2 12 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 17)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 13)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 13) = g32p_row04_cosetExponents2 13 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 18)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 14)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 14) = g32p_row04_cosetExponents2 14 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 19)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 15)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 15) = g32p_row04_cosetExponents2 15 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetMonodromy_2_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 20)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 16)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 16) = g32p_row04_cosetExponents2 16 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 21)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 17)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 17) = g32p_row04_cosetExponents2 17 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 22)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 18)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 18) = g32p_row04_cosetExponents2 18 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 25)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 19)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 19) = g32p_row04_cosetExponents2 19 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 27)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 20)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 20) = g32p_row04_cosetExponents2 20 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 29)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 21)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 21) = g32p_row04_cosetExponents2 21 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 30)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 22)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 22) = g32p_row04_cosetExponents2 22 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 31)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 23)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 23) = g32p_row04_cosetExponents2 23 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 32)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 24)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 24) = g32p_row04_cosetExponents2 24 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 34)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 25)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 25) = g32p_row04_cosetExponents2 25 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 35)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 26)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 26) = g32p_row04_cosetExponents2 26 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 39)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 27)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 27) = g32p_row04_cosetExponents2 27 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 42)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 28)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 28) = g32p_row04_cosetExponents2 28 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 44)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 29)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 29) = g32p_row04_cosetExponents2 29 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 47)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 30)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 30) = g32p_row04_cosetExponents2 30 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 48)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 31)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 31) = g32p_row04_cosetExponents2 31 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row04_cosetMonodromy_2_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 50)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 32)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 32) = g32p_row04_cosetExponents2 32 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 51)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 33)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 33) = g32p_row04_cosetExponents2 33 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 54)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 34)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 34) = g32p_row04_cosetExponents2 34 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 55)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 35)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 35) = g32p_row04_cosetExponents2 35 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 58)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 36)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 36) = g32p_row04_cosetExponents2 36 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 59)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 37)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 37) = g32p_row04_cosetExponents2 37 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 61)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 38)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 38) = g32p_row04_cosetExponents2 38 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone)) (g32p_row04_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 63)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 39)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 39) = g32p_row04_cosetExponents2 39 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 64)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 40)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 40) = g32p_row04_cosetExponents2 40 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 69)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 41)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 41) = g32p_row04_cosetExponents2 41 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 70)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 42)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 42) = g32p_row04_cosetExponents2 42 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 71)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 43)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 43) = g32p_row04_cosetExponents2 43 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 72)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 44)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 44) = g32p_row04_cosetExponents2 44 := by
  decide +kernel

theorem g32p_row04_cosetMonodromy_2_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row04_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row04_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row04_cosetRepresentatives 80)
        (g32p_row04_groupNodes (g32p_row04_cosetMonodromies2 45)) ∧
    g32p_row04_characterValues (g32p_row04_cosetMonodromies2 45) = g32p_row04_cosetExponents2 45 := by
  decide +kernel


end HodgeLean.Foundations.Program

end
