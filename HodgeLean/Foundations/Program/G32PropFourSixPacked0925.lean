import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness36CosetData

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0000 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 0) = g32p_row36_cosetRepresentatives 0 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0000 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 0))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 0)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0000 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 0))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 0)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0001 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 1) = g32p_row36_cosetRepresentatives 1 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0001 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 1))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 1)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0001 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 1))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 1)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0002 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 2) = g32p_row36_cosetRepresentatives 2 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0002 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 2))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 2)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0002 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 2))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 2)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0003 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 3) = g32p_row36_cosetRepresentatives 3 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0003 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 3))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 3)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0003 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 3))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 3)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0004 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 4) = g32p_row36_cosetRepresentatives 4 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0004 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 4))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 4)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0004 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 4))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 4)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0005 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 5) = g32p_row36_cosetRepresentatives 5 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0005 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 5))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 5)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0005 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 5))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 5)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0006 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 6) = g32p_row36_cosetRepresentatives 6 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0006 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 6))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 6)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0006 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 6))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 6)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0007 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 7) = g32p_row36_cosetRepresentatives 7 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0007 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 7))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 7)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0007 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 7))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 7)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0008 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 8) = g32p_row36_cosetRepresentatives 8 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0008 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 8))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 8)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0008 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 8))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 8)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0009 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 9) = g32p_row36_cosetRepresentatives 9 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0009 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 9))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 9)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0009 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 9))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 9)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0010 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 10) = g32p_row36_cosetRepresentatives 10 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0010 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 10))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 10)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0010 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 10))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 10)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0011 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 11) = g32p_row36_cosetRepresentatives 11 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0011 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 11))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 11)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0011 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 11))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 11)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0012 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 12) = g32p_row36_cosetRepresentatives 12 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0012 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 12))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 12)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0012 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 12))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 12)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0013 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 13) = g32p_row36_cosetRepresentatives 13 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0013 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 13))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 13)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0013 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 13))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 13)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0014 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 14) = g32p_row36_cosetRepresentatives 14 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0014 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 14))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 14)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0014 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 14))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 14)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0015 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 15) = g32p_row36_cosetRepresentatives 15 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0015 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 15))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 15)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0015 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 15))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 15)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0000 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 0 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 0 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0000
  · exact g32p_row36_cosetWord_0001
  · exact g32p_row36_cosetWord_0002
  · exact g32p_row36_cosetWord_0003
  · exact g32p_row36_cosetWord_0004
  · exact g32p_row36_cosetWord_0005
  · exact g32p_row36_cosetWord_0006
  · exact g32p_row36_cosetWord_0007
  · exact g32p_row36_cosetWord_0008
  · exact g32p_row36_cosetWord_0009
  · exact g32p_row36_cosetWord_0010
  · exact g32p_row36_cosetWord_0011
  · exact g32p_row36_cosetWord_0012
  · exact g32p_row36_cosetWord_0013
  · exact g32p_row36_cosetWord_0014
  · exact g32p_row36_cosetWord_0015

theorem g32p_row36_cosetGeneratorBlock_0000 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 0 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 0 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 0 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0000 s
  · exact g32p_row36_cosetGeneratorStep_0001 s
  · exact g32p_row36_cosetGeneratorStep_0002 s
  · exact g32p_row36_cosetGeneratorStep_0003 s
  · exact g32p_row36_cosetGeneratorStep_0004 s
  · exact g32p_row36_cosetGeneratorStep_0005 s
  · exact g32p_row36_cosetGeneratorStep_0006 s
  · exact g32p_row36_cosetGeneratorStep_0007 s
  · exact g32p_row36_cosetGeneratorStep_0008 s
  · exact g32p_row36_cosetGeneratorStep_0009 s
  · exact g32p_row36_cosetGeneratorStep_0010 s
  · exact g32p_row36_cosetGeneratorStep_0011 s
  · exact g32p_row36_cosetGeneratorStep_0012 s
  · exact g32p_row36_cosetGeneratorStep_0013 s
  · exact g32p_row36_cosetGeneratorStep_0014 s
  · exact g32p_row36_cosetGeneratorStep_0015 s

theorem g32p_row36_cosetBranchBlock_0000 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 0 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 0 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 0 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0000 s
  · exact g32p_row36_cosetBranchStep_0001 s
  · exact g32p_row36_cosetBranchStep_0002 s
  · exact g32p_row36_cosetBranchStep_0003 s
  · exact g32p_row36_cosetBranchStep_0004 s
  · exact g32p_row36_cosetBranchStep_0005 s
  · exact g32p_row36_cosetBranchStep_0006 s
  · exact g32p_row36_cosetBranchStep_0007 s
  · exact g32p_row36_cosetBranchStep_0008 s
  · exact g32p_row36_cosetBranchStep_0009 s
  · exact g32p_row36_cosetBranchStep_0010 s
  · exact g32p_row36_cosetBranchStep_0011 s
  · exact g32p_row36_cosetBranchStep_0012 s
  · exact g32p_row36_cosetBranchStep_0013 s
  · exact g32p_row36_cosetBranchStep_0014 s
  · exact g32p_row36_cosetBranchStep_0015 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0016 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 16) = g32p_row36_cosetRepresentatives 16 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0016 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 16))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 16)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0016 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 16))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 16)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0017 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 17) = g32p_row36_cosetRepresentatives 17 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0017 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 17))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 17)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0017 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 17))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 17)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0018 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 18) = g32p_row36_cosetRepresentatives 18 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0018 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 18))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 18)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0018 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 18))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 18)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0019 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 19) = g32p_row36_cosetRepresentatives 19 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0019 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 19))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 19)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0019 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 19))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 19)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0020 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 20) = g32p_row36_cosetRepresentatives 20 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0020 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 20))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 20)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0020 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 20))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 20)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0021 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 21) = g32p_row36_cosetRepresentatives 21 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0021 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 21))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 21)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0021 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 21))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 21)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0022 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 22) = g32p_row36_cosetRepresentatives 22 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0022 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 22))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 22)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0022 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 22))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 22)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0023 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 23) = g32p_row36_cosetRepresentatives 23 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0023 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 23))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 23)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0023 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 23))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 23)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0024 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 24) = g32p_row36_cosetRepresentatives 24 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0024 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 24))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 24)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0024 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 24))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 24)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0025 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 25) = g32p_row36_cosetRepresentatives 25 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0025 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 25))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 25)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0025 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 25))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 25)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0026 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 26) = g32p_row36_cosetRepresentatives 26 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0026 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 26))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 26)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0026 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 26))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 26)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0027 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 27) = g32p_row36_cosetRepresentatives 27 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0027 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 27))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 27)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0027 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 27))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 27)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0028 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 28) = g32p_row36_cosetRepresentatives 28 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0028 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 28))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 28)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0028 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 28))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 28)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0029 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 29) = g32p_row36_cosetRepresentatives 29 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0029 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 29))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 29)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0029 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 29))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 29)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0030 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 30) = g32p_row36_cosetRepresentatives 30 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0030 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 30))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 30)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0030 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 30))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 30)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0031 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 31) = g32p_row36_cosetRepresentatives 31 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0031 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 31))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 31)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0031 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 31))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 31)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0001 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 1 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 1 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0016
  · exact g32p_row36_cosetWord_0017
  · exact g32p_row36_cosetWord_0018
  · exact g32p_row36_cosetWord_0019
  · exact g32p_row36_cosetWord_0020
  · exact g32p_row36_cosetWord_0021
  · exact g32p_row36_cosetWord_0022
  · exact g32p_row36_cosetWord_0023
  · exact g32p_row36_cosetWord_0024
  · exact g32p_row36_cosetWord_0025
  · exact g32p_row36_cosetWord_0026
  · exact g32p_row36_cosetWord_0027
  · exact g32p_row36_cosetWord_0028
  · exact g32p_row36_cosetWord_0029
  · exact g32p_row36_cosetWord_0030
  · exact g32p_row36_cosetWord_0031

theorem g32p_row36_cosetGeneratorBlock_0001 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 1 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 1 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 1 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0016 s
  · exact g32p_row36_cosetGeneratorStep_0017 s
  · exact g32p_row36_cosetGeneratorStep_0018 s
  · exact g32p_row36_cosetGeneratorStep_0019 s
  · exact g32p_row36_cosetGeneratorStep_0020 s
  · exact g32p_row36_cosetGeneratorStep_0021 s
  · exact g32p_row36_cosetGeneratorStep_0022 s
  · exact g32p_row36_cosetGeneratorStep_0023 s
  · exact g32p_row36_cosetGeneratorStep_0024 s
  · exact g32p_row36_cosetGeneratorStep_0025 s
  · exact g32p_row36_cosetGeneratorStep_0026 s
  · exact g32p_row36_cosetGeneratorStep_0027 s
  · exact g32p_row36_cosetGeneratorStep_0028 s
  · exact g32p_row36_cosetGeneratorStep_0029 s
  · exact g32p_row36_cosetGeneratorStep_0030 s
  · exact g32p_row36_cosetGeneratorStep_0031 s

theorem g32p_row36_cosetBranchBlock_0001 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 1 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 1 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 1 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0016 s
  · exact g32p_row36_cosetBranchStep_0017 s
  · exact g32p_row36_cosetBranchStep_0018 s
  · exact g32p_row36_cosetBranchStep_0019 s
  · exact g32p_row36_cosetBranchStep_0020 s
  · exact g32p_row36_cosetBranchStep_0021 s
  · exact g32p_row36_cosetBranchStep_0022 s
  · exact g32p_row36_cosetBranchStep_0023 s
  · exact g32p_row36_cosetBranchStep_0024 s
  · exact g32p_row36_cosetBranchStep_0025 s
  · exact g32p_row36_cosetBranchStep_0026 s
  · exact g32p_row36_cosetBranchStep_0027 s
  · exact g32p_row36_cosetBranchStep_0028 s
  · exact g32p_row36_cosetBranchStep_0029 s
  · exact g32p_row36_cosetBranchStep_0030 s
  · exact g32p_row36_cosetBranchStep_0031 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0032 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 32) = g32p_row36_cosetRepresentatives 32 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0032 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 32))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 32)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0032 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 32))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 32)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0033 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 33) = g32p_row36_cosetRepresentatives 33 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0033 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 33))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 33)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0033 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 33))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 33)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0034 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 34) = g32p_row36_cosetRepresentatives 34 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0034 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 34))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 34)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0034 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 34))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 34)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0035 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 35) = g32p_row36_cosetRepresentatives 35 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0035 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 35))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 35)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0035 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 35))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 35)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0036 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 36) = g32p_row36_cosetRepresentatives 36 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0036 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 36))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 36)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0036 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 36))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 36)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0037 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 37) = g32p_row36_cosetRepresentatives 37 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0037 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 37))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 37)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0037 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 37))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 37)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0038 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 38) = g32p_row36_cosetRepresentatives 38 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0038 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 38))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 38)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0038 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 38))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 38)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0039 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 39) = g32p_row36_cosetRepresentatives 39 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0039 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 39))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 39)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0039 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 39))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 39)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0040 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 40) = g32p_row36_cosetRepresentatives 40 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0040 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 40))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 40)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0040 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 40))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 40)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0041 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 41) = g32p_row36_cosetRepresentatives 41 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0041 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 41))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 41)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0041 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 41))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 41)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0042 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 42) = g32p_row36_cosetRepresentatives 42 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0042 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 42))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 42)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0042 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 42))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 42)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0043 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 43) = g32p_row36_cosetRepresentatives 43 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0043 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 43))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 43)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0043 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 43))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 43)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0044 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 44) = g32p_row36_cosetRepresentatives 44 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0044 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 44))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 44)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0044 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 44))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 44)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0045 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 45) = g32p_row36_cosetRepresentatives 45 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0045 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 45))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 45)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0045 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 45))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 45)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0046 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 46) = g32p_row36_cosetRepresentatives 46 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0046 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 46))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 46)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0046 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 46))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 46)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0047 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 47) = g32p_row36_cosetRepresentatives 47 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0047 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 47))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 47)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0047 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 47))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 47)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0002 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 2 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 2 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0032
  · exact g32p_row36_cosetWord_0033
  · exact g32p_row36_cosetWord_0034
  · exact g32p_row36_cosetWord_0035
  · exact g32p_row36_cosetWord_0036
  · exact g32p_row36_cosetWord_0037
  · exact g32p_row36_cosetWord_0038
  · exact g32p_row36_cosetWord_0039
  · exact g32p_row36_cosetWord_0040
  · exact g32p_row36_cosetWord_0041
  · exact g32p_row36_cosetWord_0042
  · exact g32p_row36_cosetWord_0043
  · exact g32p_row36_cosetWord_0044
  · exact g32p_row36_cosetWord_0045
  · exact g32p_row36_cosetWord_0046
  · exact g32p_row36_cosetWord_0047

theorem g32p_row36_cosetGeneratorBlock_0002 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 2 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 2 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 2 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0032 s
  · exact g32p_row36_cosetGeneratorStep_0033 s
  · exact g32p_row36_cosetGeneratorStep_0034 s
  · exact g32p_row36_cosetGeneratorStep_0035 s
  · exact g32p_row36_cosetGeneratorStep_0036 s
  · exact g32p_row36_cosetGeneratorStep_0037 s
  · exact g32p_row36_cosetGeneratorStep_0038 s
  · exact g32p_row36_cosetGeneratorStep_0039 s
  · exact g32p_row36_cosetGeneratorStep_0040 s
  · exact g32p_row36_cosetGeneratorStep_0041 s
  · exact g32p_row36_cosetGeneratorStep_0042 s
  · exact g32p_row36_cosetGeneratorStep_0043 s
  · exact g32p_row36_cosetGeneratorStep_0044 s
  · exact g32p_row36_cosetGeneratorStep_0045 s
  · exact g32p_row36_cosetGeneratorStep_0046 s
  · exact g32p_row36_cosetGeneratorStep_0047 s

theorem g32p_row36_cosetBranchBlock_0002 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 2 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 2 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 2 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0032 s
  · exact g32p_row36_cosetBranchStep_0033 s
  · exact g32p_row36_cosetBranchStep_0034 s
  · exact g32p_row36_cosetBranchStep_0035 s
  · exact g32p_row36_cosetBranchStep_0036 s
  · exact g32p_row36_cosetBranchStep_0037 s
  · exact g32p_row36_cosetBranchStep_0038 s
  · exact g32p_row36_cosetBranchStep_0039 s
  · exact g32p_row36_cosetBranchStep_0040 s
  · exact g32p_row36_cosetBranchStep_0041 s
  · exact g32p_row36_cosetBranchStep_0042 s
  · exact g32p_row36_cosetBranchStep_0043 s
  · exact g32p_row36_cosetBranchStep_0044 s
  · exact g32p_row36_cosetBranchStep_0045 s
  · exact g32p_row36_cosetBranchStep_0046 s
  · exact g32p_row36_cosetBranchStep_0047 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0048 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 48) = g32p_row36_cosetRepresentatives 48 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0048 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 48))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 48)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0048 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 48))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 48)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0049 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 49) = g32p_row36_cosetRepresentatives 49 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0049 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 49))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 49)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0049 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 49))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 49)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0050 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 50) = g32p_row36_cosetRepresentatives 50 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0050 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 50))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 50)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0050 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 50))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 50)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0051 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 51) = g32p_row36_cosetRepresentatives 51 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0051 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 51))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 51)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0051 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 51))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 51)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0052 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 52) = g32p_row36_cosetRepresentatives 52 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0052 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 52))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 52)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0052 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 52))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 52)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0053 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 53) = g32p_row36_cosetRepresentatives 53 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0053 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 53))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 53)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0053 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 53))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 53)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0054 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 54) = g32p_row36_cosetRepresentatives 54 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0054 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 54))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 54)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0054 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 54))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 54)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0055 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 55) = g32p_row36_cosetRepresentatives 55 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0055 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 55))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 55)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0055 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 55))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 55)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0056 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 56) = g32p_row36_cosetRepresentatives 56 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0056 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 56))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 56)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0056 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 56))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 56)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0057 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 57) = g32p_row36_cosetRepresentatives 57 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0057 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 57) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 57))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 57)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0057 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 57) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 57))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 57)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0058 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 58) = g32p_row36_cosetRepresentatives 58 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0058 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 58))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 58)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0058 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 58))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 58)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0059 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 59) = g32p_row36_cosetRepresentatives 59 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0059 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 59))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 59)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0059 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 59))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 59)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0060 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 60) = g32p_row36_cosetRepresentatives 60 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0060 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 60) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 60))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 60)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0060 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 60) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 60))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 60)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0061 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 61) = g32p_row36_cosetRepresentatives 61 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0061 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 61))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 61)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0061 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 61))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 61)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0062 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 62) = g32p_row36_cosetRepresentatives 62 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0062 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 62))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 62)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0062 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 62))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 62)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0063 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 63) = g32p_row36_cosetRepresentatives 63 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0063 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 63))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 63)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0063 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 63))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 63)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0003 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 3 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 3 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0048
  · exact g32p_row36_cosetWord_0049
  · exact g32p_row36_cosetWord_0050
  · exact g32p_row36_cosetWord_0051
  · exact g32p_row36_cosetWord_0052
  · exact g32p_row36_cosetWord_0053
  · exact g32p_row36_cosetWord_0054
  · exact g32p_row36_cosetWord_0055
  · exact g32p_row36_cosetWord_0056
  · exact g32p_row36_cosetWord_0057
  · exact g32p_row36_cosetWord_0058
  · exact g32p_row36_cosetWord_0059
  · exact g32p_row36_cosetWord_0060
  · exact g32p_row36_cosetWord_0061
  · exact g32p_row36_cosetWord_0062
  · exact g32p_row36_cosetWord_0063

theorem g32p_row36_cosetGeneratorBlock_0003 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 3 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 3 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 3 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0048 s
  · exact g32p_row36_cosetGeneratorStep_0049 s
  · exact g32p_row36_cosetGeneratorStep_0050 s
  · exact g32p_row36_cosetGeneratorStep_0051 s
  · exact g32p_row36_cosetGeneratorStep_0052 s
  · exact g32p_row36_cosetGeneratorStep_0053 s
  · exact g32p_row36_cosetGeneratorStep_0054 s
  · exact g32p_row36_cosetGeneratorStep_0055 s
  · exact g32p_row36_cosetGeneratorStep_0056 s
  · exact g32p_row36_cosetGeneratorStep_0057 s
  · exact g32p_row36_cosetGeneratorStep_0058 s
  · exact g32p_row36_cosetGeneratorStep_0059 s
  · exact g32p_row36_cosetGeneratorStep_0060 s
  · exact g32p_row36_cosetGeneratorStep_0061 s
  · exact g32p_row36_cosetGeneratorStep_0062 s
  · exact g32p_row36_cosetGeneratorStep_0063 s

theorem g32p_row36_cosetBranchBlock_0003 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 3 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 3 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 3 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0048 s
  · exact g32p_row36_cosetBranchStep_0049 s
  · exact g32p_row36_cosetBranchStep_0050 s
  · exact g32p_row36_cosetBranchStep_0051 s
  · exact g32p_row36_cosetBranchStep_0052 s
  · exact g32p_row36_cosetBranchStep_0053 s
  · exact g32p_row36_cosetBranchStep_0054 s
  · exact g32p_row36_cosetBranchStep_0055 s
  · exact g32p_row36_cosetBranchStep_0056 s
  · exact g32p_row36_cosetBranchStep_0057 s
  · exact g32p_row36_cosetBranchStep_0058 s
  · exact g32p_row36_cosetBranchStep_0059 s
  · exact g32p_row36_cosetBranchStep_0060 s
  · exact g32p_row36_cosetBranchStep_0061 s
  · exact g32p_row36_cosetBranchStep_0062 s
  · exact g32p_row36_cosetBranchStep_0063 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0064 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 64) = g32p_row36_cosetRepresentatives 64 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0064 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 64))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 64)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0064 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 64))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 64)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0065 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 65) = g32p_row36_cosetRepresentatives 65 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0065 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 65))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 65)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0065 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 65))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 65)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0066 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 66) = g32p_row36_cosetRepresentatives 66 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0066 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 66))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 66)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0066 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 66))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 66)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0067 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 67) = g32p_row36_cosetRepresentatives 67 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0067 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 67) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 67))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 67)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0067 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 67) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 67))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 67)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0068 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 68) = g32p_row36_cosetRepresentatives 68 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0068 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 68))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 68)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0068 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 68))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 68)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0069 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 69) = g32p_row36_cosetRepresentatives 69 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0069 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 69))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 69)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0069 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 69))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 69)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0070 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 70) = g32p_row36_cosetRepresentatives 70 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0070 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 70))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 70)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0070 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 70))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 70)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0071 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 71) = g32p_row36_cosetRepresentatives 71 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0071 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 71))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 71)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0071 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 71))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 71)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0072 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 72) = g32p_row36_cosetRepresentatives 72 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0072 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 72))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 72)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0072 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 72))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 72)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0073 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 73) = g32p_row36_cosetRepresentatives 73 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0073 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 73))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 73)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0073 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 73))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 73)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0074 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 74) = g32p_row36_cosetRepresentatives 74 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0074 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 74))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 74)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0074 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 74))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 74)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0075 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 75) = g32p_row36_cosetRepresentatives 75 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0075 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 75))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 75)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0075 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 75))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 75)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0076 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 76) = g32p_row36_cosetRepresentatives 76 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0076 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 76))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 76)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0076 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 76))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 76)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0077 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 77) = g32p_row36_cosetRepresentatives 77 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0077 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 77))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 77)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0077 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 77))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 77)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0078 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 78) = g32p_row36_cosetRepresentatives 78 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0078 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 78) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 78))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 78)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0078 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 78) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 78))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 78)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0079 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 79) = g32p_row36_cosetRepresentatives 79 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0079 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 79))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 79)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0079 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 79))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 79)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0004 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 4 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 4 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0064
  · exact g32p_row36_cosetWord_0065
  · exact g32p_row36_cosetWord_0066
  · exact g32p_row36_cosetWord_0067
  · exact g32p_row36_cosetWord_0068
  · exact g32p_row36_cosetWord_0069
  · exact g32p_row36_cosetWord_0070
  · exact g32p_row36_cosetWord_0071
  · exact g32p_row36_cosetWord_0072
  · exact g32p_row36_cosetWord_0073
  · exact g32p_row36_cosetWord_0074
  · exact g32p_row36_cosetWord_0075
  · exact g32p_row36_cosetWord_0076
  · exact g32p_row36_cosetWord_0077
  · exact g32p_row36_cosetWord_0078
  · exact g32p_row36_cosetWord_0079

theorem g32p_row36_cosetGeneratorBlock_0004 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 4 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 4 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 4 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0064 s
  · exact g32p_row36_cosetGeneratorStep_0065 s
  · exact g32p_row36_cosetGeneratorStep_0066 s
  · exact g32p_row36_cosetGeneratorStep_0067 s
  · exact g32p_row36_cosetGeneratorStep_0068 s
  · exact g32p_row36_cosetGeneratorStep_0069 s
  · exact g32p_row36_cosetGeneratorStep_0070 s
  · exact g32p_row36_cosetGeneratorStep_0071 s
  · exact g32p_row36_cosetGeneratorStep_0072 s
  · exact g32p_row36_cosetGeneratorStep_0073 s
  · exact g32p_row36_cosetGeneratorStep_0074 s
  · exact g32p_row36_cosetGeneratorStep_0075 s
  · exact g32p_row36_cosetGeneratorStep_0076 s
  · exact g32p_row36_cosetGeneratorStep_0077 s
  · exact g32p_row36_cosetGeneratorStep_0078 s
  · exact g32p_row36_cosetGeneratorStep_0079 s

theorem g32p_row36_cosetBranchBlock_0004 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 4 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 4 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 4 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0064 s
  · exact g32p_row36_cosetBranchStep_0065 s
  · exact g32p_row36_cosetBranchStep_0066 s
  · exact g32p_row36_cosetBranchStep_0067 s
  · exact g32p_row36_cosetBranchStep_0068 s
  · exact g32p_row36_cosetBranchStep_0069 s
  · exact g32p_row36_cosetBranchStep_0070 s
  · exact g32p_row36_cosetBranchStep_0071 s
  · exact g32p_row36_cosetBranchStep_0072 s
  · exact g32p_row36_cosetBranchStep_0073 s
  · exact g32p_row36_cosetBranchStep_0074 s
  · exact g32p_row36_cosetBranchStep_0075 s
  · exact g32p_row36_cosetBranchStep_0076 s
  · exact g32p_row36_cosetBranchStep_0077 s
  · exact g32p_row36_cosetBranchStep_0078 s
  · exact g32p_row36_cosetBranchStep_0079 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0080 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 80) = g32p_row36_cosetRepresentatives 80 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0080 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 80))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 80)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0080 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 80))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 80)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0081 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 81) = g32p_row36_cosetRepresentatives 81 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0081 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 81))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 81)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0081 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 81))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 81)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0082 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 82) = g32p_row36_cosetRepresentatives 82 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0082 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 82))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 82)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0082 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 82))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 82)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0083 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 83) = g32p_row36_cosetRepresentatives 83 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0083 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 83) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 83))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 83)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0083 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 83) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 83))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 83)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0084 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 84) = g32p_row36_cosetRepresentatives 84 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0084 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 84) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 84))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 84)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0084 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 84) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 84))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 84)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0085 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 85) = g32p_row36_cosetRepresentatives 85 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0085 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 85))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 85)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0085 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 85))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 85)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0086 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 86) = g32p_row36_cosetRepresentatives 86 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0086 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 86) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 86))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 86)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0086 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 86) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 86))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 86)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0087 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 87) = g32p_row36_cosetRepresentatives 87 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0087 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 87) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 87))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 87)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0087 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 87) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 87))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 87)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0088 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 88) = g32p_row36_cosetRepresentatives 88 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0088 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 88))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 88)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0088 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 88))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 88)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0089 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 89) = g32p_row36_cosetRepresentatives 89 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0089 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 89) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 89))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 89)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0089 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 89) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 89))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 89)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0090 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 90) = g32p_row36_cosetRepresentatives 90 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0090 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 90) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 90))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 90)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0090 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 90) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 90))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 90)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0091 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 91) = g32p_row36_cosetRepresentatives 91 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0091 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 91) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 91))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 91)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0091 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 91) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 91))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 91)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0092 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 92) = g32p_row36_cosetRepresentatives 92 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0092 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 92) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 92))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 92)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0092 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 92) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 92))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 92)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0093 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 93) = g32p_row36_cosetRepresentatives 93 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0093 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 93) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 93))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 93)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0093 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 93) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 93))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 93)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0094 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 94) = g32p_row36_cosetRepresentatives 94 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0094 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 94) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 94))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 94)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0094 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 94) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 94))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 94)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0095 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 95) = g32p_row36_cosetRepresentatives 95 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0095 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 95) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 95))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 95)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0095 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 95) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 95))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 95)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0005 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 5 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 5 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0080
  · exact g32p_row36_cosetWord_0081
  · exact g32p_row36_cosetWord_0082
  · exact g32p_row36_cosetWord_0083
  · exact g32p_row36_cosetWord_0084
  · exact g32p_row36_cosetWord_0085
  · exact g32p_row36_cosetWord_0086
  · exact g32p_row36_cosetWord_0087
  · exact g32p_row36_cosetWord_0088
  · exact g32p_row36_cosetWord_0089
  · exact g32p_row36_cosetWord_0090
  · exact g32p_row36_cosetWord_0091
  · exact g32p_row36_cosetWord_0092
  · exact g32p_row36_cosetWord_0093
  · exact g32p_row36_cosetWord_0094
  · exact g32p_row36_cosetWord_0095

theorem g32p_row36_cosetGeneratorBlock_0005 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 5 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 5 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 5 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0080 s
  · exact g32p_row36_cosetGeneratorStep_0081 s
  · exact g32p_row36_cosetGeneratorStep_0082 s
  · exact g32p_row36_cosetGeneratorStep_0083 s
  · exact g32p_row36_cosetGeneratorStep_0084 s
  · exact g32p_row36_cosetGeneratorStep_0085 s
  · exact g32p_row36_cosetGeneratorStep_0086 s
  · exact g32p_row36_cosetGeneratorStep_0087 s
  · exact g32p_row36_cosetGeneratorStep_0088 s
  · exact g32p_row36_cosetGeneratorStep_0089 s
  · exact g32p_row36_cosetGeneratorStep_0090 s
  · exact g32p_row36_cosetGeneratorStep_0091 s
  · exact g32p_row36_cosetGeneratorStep_0092 s
  · exact g32p_row36_cosetGeneratorStep_0093 s
  · exact g32p_row36_cosetGeneratorStep_0094 s
  · exact g32p_row36_cosetGeneratorStep_0095 s

theorem g32p_row36_cosetBranchBlock_0005 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 5 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 5 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 5 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0080 s
  · exact g32p_row36_cosetBranchStep_0081 s
  · exact g32p_row36_cosetBranchStep_0082 s
  · exact g32p_row36_cosetBranchStep_0083 s
  · exact g32p_row36_cosetBranchStep_0084 s
  · exact g32p_row36_cosetBranchStep_0085 s
  · exact g32p_row36_cosetBranchStep_0086 s
  · exact g32p_row36_cosetBranchStep_0087 s
  · exact g32p_row36_cosetBranchStep_0088 s
  · exact g32p_row36_cosetBranchStep_0089 s
  · exact g32p_row36_cosetBranchStep_0090 s
  · exact g32p_row36_cosetBranchStep_0091 s
  · exact g32p_row36_cosetBranchStep_0092 s
  · exact g32p_row36_cosetBranchStep_0093 s
  · exact g32p_row36_cosetBranchStep_0094 s
  · exact g32p_row36_cosetBranchStep_0095 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0096 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 96) = g32p_row36_cosetRepresentatives 96 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0096 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 96) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 96))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 96)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0096 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 96) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 96))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 96)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0097 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 97) = g32p_row36_cosetRepresentatives 97 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0097 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 97) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 97))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 97)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0097 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 97) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 97))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 97)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0098 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 98) = g32p_row36_cosetRepresentatives 98 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0098 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 98) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 98))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 98)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0098 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 98) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 98))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 98)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0099 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 99) = g32p_row36_cosetRepresentatives 99 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0099 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 99) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 99))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 99)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0099 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 99) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 99))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 99)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0100 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 100) = g32p_row36_cosetRepresentatives 100 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0100 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 100) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 100))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 100)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0100 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 100) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 100))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 100)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0101 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 101) = g32p_row36_cosetRepresentatives 101 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0101 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 101) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 101))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 101)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0101 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 101) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 101))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 101)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0102 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 102) = g32p_row36_cosetRepresentatives 102 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0102 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 102) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 102))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 102)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0102 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 102) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 102))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 102)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0103 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 103) = g32p_row36_cosetRepresentatives 103 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0103 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 103) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 103))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 103)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0103 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 103) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 103))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 103)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0104 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 104) = g32p_row36_cosetRepresentatives 104 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0104 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 104) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 104))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 104)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0104 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 104) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 104))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 104)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0105 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 105) = g32p_row36_cosetRepresentatives 105 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0105 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 105) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 105))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 105)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0105 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 105) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 105))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 105)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0106 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 106) = g32p_row36_cosetRepresentatives 106 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0106 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 106) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 106))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 106)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0106 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 106) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 106))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 106)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0107 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 107) = g32p_row36_cosetRepresentatives 107 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0107 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 107) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 107))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 107)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0107 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 107) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 107))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 107)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0108 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 108) = g32p_row36_cosetRepresentatives 108 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0108 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 108) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 108))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 108)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0108 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 108) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 108))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 108)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0109 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 109) = g32p_row36_cosetRepresentatives 109 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0109 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 109) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 109))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 109)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0109 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 109) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 109))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 109)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0110 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 110) = g32p_row36_cosetRepresentatives 110 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0110 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 110) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 110))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 110)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0110 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 110) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 110))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 110)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0111 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 111) = g32p_row36_cosetRepresentatives 111 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0111 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 111) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 111))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 111)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0111 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 111) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 111))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 111)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0006 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 6 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 6 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0096
  · exact g32p_row36_cosetWord_0097
  · exact g32p_row36_cosetWord_0098
  · exact g32p_row36_cosetWord_0099
  · exact g32p_row36_cosetWord_0100
  · exact g32p_row36_cosetWord_0101
  · exact g32p_row36_cosetWord_0102
  · exact g32p_row36_cosetWord_0103
  · exact g32p_row36_cosetWord_0104
  · exact g32p_row36_cosetWord_0105
  · exact g32p_row36_cosetWord_0106
  · exact g32p_row36_cosetWord_0107
  · exact g32p_row36_cosetWord_0108
  · exact g32p_row36_cosetWord_0109
  · exact g32p_row36_cosetWord_0110
  · exact g32p_row36_cosetWord_0111

theorem g32p_row36_cosetGeneratorBlock_0006 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 6 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 6 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 6 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0096 s
  · exact g32p_row36_cosetGeneratorStep_0097 s
  · exact g32p_row36_cosetGeneratorStep_0098 s
  · exact g32p_row36_cosetGeneratorStep_0099 s
  · exact g32p_row36_cosetGeneratorStep_0100 s
  · exact g32p_row36_cosetGeneratorStep_0101 s
  · exact g32p_row36_cosetGeneratorStep_0102 s
  · exact g32p_row36_cosetGeneratorStep_0103 s
  · exact g32p_row36_cosetGeneratorStep_0104 s
  · exact g32p_row36_cosetGeneratorStep_0105 s
  · exact g32p_row36_cosetGeneratorStep_0106 s
  · exact g32p_row36_cosetGeneratorStep_0107 s
  · exact g32p_row36_cosetGeneratorStep_0108 s
  · exact g32p_row36_cosetGeneratorStep_0109 s
  · exact g32p_row36_cosetGeneratorStep_0110 s
  · exact g32p_row36_cosetGeneratorStep_0111 s

theorem g32p_row36_cosetBranchBlock_0006 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 6 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 6 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 6 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0096 s
  · exact g32p_row36_cosetBranchStep_0097 s
  · exact g32p_row36_cosetBranchStep_0098 s
  · exact g32p_row36_cosetBranchStep_0099 s
  · exact g32p_row36_cosetBranchStep_0100 s
  · exact g32p_row36_cosetBranchStep_0101 s
  · exact g32p_row36_cosetBranchStep_0102 s
  · exact g32p_row36_cosetBranchStep_0103 s
  · exact g32p_row36_cosetBranchStep_0104 s
  · exact g32p_row36_cosetBranchStep_0105 s
  · exact g32p_row36_cosetBranchStep_0106 s
  · exact g32p_row36_cosetBranchStep_0107 s
  · exact g32p_row36_cosetBranchStep_0108 s
  · exact g32p_row36_cosetBranchStep_0109 s
  · exact g32p_row36_cosetBranchStep_0110 s
  · exact g32p_row36_cosetBranchStep_0111 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0112 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 112) = g32p_row36_cosetRepresentatives 112 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0112 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 112) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 112))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 112)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0112 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 112) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 112))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 112)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0113 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 113) = g32p_row36_cosetRepresentatives 113 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0113 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 113) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 113))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 113)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0113 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 113) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 113))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 113)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0114 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 114) = g32p_row36_cosetRepresentatives 114 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0114 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 114) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 114))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 114)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0114 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 114) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 114))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 114)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0115 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 115) = g32p_row36_cosetRepresentatives 115 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0115 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 115) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 115))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 115)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0115 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 115) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 115))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 115)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0116 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 116) = g32p_row36_cosetRepresentatives 116 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0116 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 116) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 116))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 116)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0116 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 116) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 116))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 116)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0117 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 117) = g32p_row36_cosetRepresentatives 117 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0117 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 117) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 117))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 117)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0117 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 117) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 117))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 117)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0118 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 118) = g32p_row36_cosetRepresentatives 118 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0118 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 118) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 118))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 118)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0118 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 118) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 118))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 118)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0119 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 119) = g32p_row36_cosetRepresentatives 119 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0119 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 119) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 119))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 119)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0119 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 119) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 119))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 119)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0120 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 120) = g32p_row36_cosetRepresentatives 120 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0120 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 120) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 120))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 120)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0120 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 120) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 120))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 120)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0121 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 121) = g32p_row36_cosetRepresentatives 121 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0121 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 121) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 121))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 121)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0121 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 121) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 121))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 121)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0122 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 122) = g32p_row36_cosetRepresentatives 122 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0122 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 122) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 122))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 122)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0122 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 122) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 122))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 122)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0123 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 123) = g32p_row36_cosetRepresentatives 123 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0123 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 123) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 123))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 123)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0123 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 123) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 123))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 123)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0124 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 124) = g32p_row36_cosetRepresentatives 124 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0124 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 124) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 124))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 124)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0124 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 124) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 124))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 124)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0125 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 125) = g32p_row36_cosetRepresentatives 125 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0125 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 125) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 125))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 125)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0125 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 125) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 125))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 125)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0126 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 126) = g32p_row36_cosetRepresentatives 126 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0126 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 126) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 126))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 126)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0126 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 126) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 126))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 126)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0127 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 127) = g32p_row36_cosetRepresentatives 127 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0127 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 127) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 127))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 127)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0127 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 127) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 127))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 127)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0007 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 7 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 7 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0112
  · exact g32p_row36_cosetWord_0113
  · exact g32p_row36_cosetWord_0114
  · exact g32p_row36_cosetWord_0115
  · exact g32p_row36_cosetWord_0116
  · exact g32p_row36_cosetWord_0117
  · exact g32p_row36_cosetWord_0118
  · exact g32p_row36_cosetWord_0119
  · exact g32p_row36_cosetWord_0120
  · exact g32p_row36_cosetWord_0121
  · exact g32p_row36_cosetWord_0122
  · exact g32p_row36_cosetWord_0123
  · exact g32p_row36_cosetWord_0124
  · exact g32p_row36_cosetWord_0125
  · exact g32p_row36_cosetWord_0126
  · exact g32p_row36_cosetWord_0127

theorem g32p_row36_cosetGeneratorBlock_0007 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 7 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 7 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 7 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0112 s
  · exact g32p_row36_cosetGeneratorStep_0113 s
  · exact g32p_row36_cosetGeneratorStep_0114 s
  · exact g32p_row36_cosetGeneratorStep_0115 s
  · exact g32p_row36_cosetGeneratorStep_0116 s
  · exact g32p_row36_cosetGeneratorStep_0117 s
  · exact g32p_row36_cosetGeneratorStep_0118 s
  · exact g32p_row36_cosetGeneratorStep_0119 s
  · exact g32p_row36_cosetGeneratorStep_0120 s
  · exact g32p_row36_cosetGeneratorStep_0121 s
  · exact g32p_row36_cosetGeneratorStep_0122 s
  · exact g32p_row36_cosetGeneratorStep_0123 s
  · exact g32p_row36_cosetGeneratorStep_0124 s
  · exact g32p_row36_cosetGeneratorStep_0125 s
  · exact g32p_row36_cosetGeneratorStep_0126 s
  · exact g32p_row36_cosetGeneratorStep_0127 s

theorem g32p_row36_cosetBranchBlock_0007 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 7 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 7 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 7 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0112 s
  · exact g32p_row36_cosetBranchStep_0113 s
  · exact g32p_row36_cosetBranchStep_0114 s
  · exact g32p_row36_cosetBranchStep_0115 s
  · exact g32p_row36_cosetBranchStep_0116 s
  · exact g32p_row36_cosetBranchStep_0117 s
  · exact g32p_row36_cosetBranchStep_0118 s
  · exact g32p_row36_cosetBranchStep_0119 s
  · exact g32p_row36_cosetBranchStep_0120 s
  · exact g32p_row36_cosetBranchStep_0121 s
  · exact g32p_row36_cosetBranchStep_0122 s
  · exact g32p_row36_cosetBranchStep_0123 s
  · exact g32p_row36_cosetBranchStep_0124 s
  · exact g32p_row36_cosetBranchStep_0125 s
  · exact g32p_row36_cosetBranchStep_0126 s
  · exact g32p_row36_cosetBranchStep_0127 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0128 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 128) = g32p_row36_cosetRepresentatives 128 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0128 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 128) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 128))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 128)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0128 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 128) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 128))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 128)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0129 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 129) = g32p_row36_cosetRepresentatives 129 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0129 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 129) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 129))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 129)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0129 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 129) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 129))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 129)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0130 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 130) = g32p_row36_cosetRepresentatives 130 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0130 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 130) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 130))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 130)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0130 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 130) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 130))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 130)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0131 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 131) = g32p_row36_cosetRepresentatives 131 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0131 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 131) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 131))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 131)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0131 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 131) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 131))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 131)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0132 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 132) = g32p_row36_cosetRepresentatives 132 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0132 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 132) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 132))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 132)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0132 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 132) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 132))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 132)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0133 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 133) = g32p_row36_cosetRepresentatives 133 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0133 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 133) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 133))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 133)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0133 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 133) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 133))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 133)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0134 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 134) = g32p_row36_cosetRepresentatives 134 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0134 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 134) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 134))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 134)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0134 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 134) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 134))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 134)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0135 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 135) = g32p_row36_cosetRepresentatives 135 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0135 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 135) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 135))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 135)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0135 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 135) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 135))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 135)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0136 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 136) = g32p_row36_cosetRepresentatives 136 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0136 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 136) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 136))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 136)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0136 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 136) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 136))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 136)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0137 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 137) = g32p_row36_cosetRepresentatives 137 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0137 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 137) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 137))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 137)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0137 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 137) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 137))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 137)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0138 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 138) = g32p_row36_cosetRepresentatives 138 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0138 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 138) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 138))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 138)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0138 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 138) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 138))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 138)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0139 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 139) = g32p_row36_cosetRepresentatives 139 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0139 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 139) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 139))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 139)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0139 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 139) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 139))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 139)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0140 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 140) = g32p_row36_cosetRepresentatives 140 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0140 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 140) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 140))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 140)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0140 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 140) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 140))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 140)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0141 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 141) = g32p_row36_cosetRepresentatives 141 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0141 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 141) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 141))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 141)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0141 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 141) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 141))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 141)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0142 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 142) = g32p_row36_cosetRepresentatives 142 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0142 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 142) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 142))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 142)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0142 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 142) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 142))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 142)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0143 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 143) = g32p_row36_cosetRepresentatives 143 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0143 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 143) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 143))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 143)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0143 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 143) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 143))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 143)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0008 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 8 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 8 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0128
  · exact g32p_row36_cosetWord_0129
  · exact g32p_row36_cosetWord_0130
  · exact g32p_row36_cosetWord_0131
  · exact g32p_row36_cosetWord_0132
  · exact g32p_row36_cosetWord_0133
  · exact g32p_row36_cosetWord_0134
  · exact g32p_row36_cosetWord_0135
  · exact g32p_row36_cosetWord_0136
  · exact g32p_row36_cosetWord_0137
  · exact g32p_row36_cosetWord_0138
  · exact g32p_row36_cosetWord_0139
  · exact g32p_row36_cosetWord_0140
  · exact g32p_row36_cosetWord_0141
  · exact g32p_row36_cosetWord_0142
  · exact g32p_row36_cosetWord_0143

theorem g32p_row36_cosetGeneratorBlock_0008 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 8 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 8 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 8 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0128 s
  · exact g32p_row36_cosetGeneratorStep_0129 s
  · exact g32p_row36_cosetGeneratorStep_0130 s
  · exact g32p_row36_cosetGeneratorStep_0131 s
  · exact g32p_row36_cosetGeneratorStep_0132 s
  · exact g32p_row36_cosetGeneratorStep_0133 s
  · exact g32p_row36_cosetGeneratorStep_0134 s
  · exact g32p_row36_cosetGeneratorStep_0135 s
  · exact g32p_row36_cosetGeneratorStep_0136 s
  · exact g32p_row36_cosetGeneratorStep_0137 s
  · exact g32p_row36_cosetGeneratorStep_0138 s
  · exact g32p_row36_cosetGeneratorStep_0139 s
  · exact g32p_row36_cosetGeneratorStep_0140 s
  · exact g32p_row36_cosetGeneratorStep_0141 s
  · exact g32p_row36_cosetGeneratorStep_0142 s
  · exact g32p_row36_cosetGeneratorStep_0143 s

theorem g32p_row36_cosetBranchBlock_0008 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 8 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 8 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 8 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0128 s
  · exact g32p_row36_cosetBranchStep_0129 s
  · exact g32p_row36_cosetBranchStep_0130 s
  · exact g32p_row36_cosetBranchStep_0131 s
  · exact g32p_row36_cosetBranchStep_0132 s
  · exact g32p_row36_cosetBranchStep_0133 s
  · exact g32p_row36_cosetBranchStep_0134 s
  · exact g32p_row36_cosetBranchStep_0135 s
  · exact g32p_row36_cosetBranchStep_0136 s
  · exact g32p_row36_cosetBranchStep_0137 s
  · exact g32p_row36_cosetBranchStep_0138 s
  · exact g32p_row36_cosetBranchStep_0139 s
  · exact g32p_row36_cosetBranchStep_0140 s
  · exact g32p_row36_cosetBranchStep_0141 s
  · exact g32p_row36_cosetBranchStep_0142 s
  · exact g32p_row36_cosetBranchStep_0143 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0144 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 144) = g32p_row36_cosetRepresentatives 144 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0144 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 144) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 144))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 144)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0144 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 144) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 144))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 144)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0145 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 145) = g32p_row36_cosetRepresentatives 145 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0145 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 145) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 145))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 145)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0145 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 145) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 145))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 145)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0146 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 146) = g32p_row36_cosetRepresentatives 146 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0146 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 146) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 146))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 146)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0146 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 146) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 146))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 146)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0147 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 147) = g32p_row36_cosetRepresentatives 147 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0147 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 147) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 147))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 147)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0147 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 147) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 147))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 147)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0148 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 148) = g32p_row36_cosetRepresentatives 148 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0148 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 148) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 148))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 148)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0148 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 148) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 148))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 148)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0149 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 149) = g32p_row36_cosetRepresentatives 149 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0149 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 149) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 149))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 149)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0149 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 149) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 149))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 149)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0150 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 150) = g32p_row36_cosetRepresentatives 150 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0150 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 150) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 150))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 150)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0150 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 150) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 150))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 150)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0151 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 151) = g32p_row36_cosetRepresentatives 151 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0151 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 151) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 151))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 151)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0151 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 151) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 151))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 151)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0152 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 152) = g32p_row36_cosetRepresentatives 152 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0152 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 152) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 152))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 152)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0152 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 152) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 152))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 152)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0153 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 153) = g32p_row36_cosetRepresentatives 153 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0153 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 153) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 153))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 153)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0153 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 153) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 153))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 153)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0154 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 154) = g32p_row36_cosetRepresentatives 154 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0154 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 154) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 154))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 154)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0154 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 154) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 154))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 154)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0155 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 155) = g32p_row36_cosetRepresentatives 155 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0155 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 155) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 155))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 155)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0155 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 155) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 155))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 155)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0156 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 156) = g32p_row36_cosetRepresentatives 156 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0156 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 156) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 156))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 156)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0156 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 156) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 156))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 156)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0157 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 157) = g32p_row36_cosetRepresentatives 157 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0157 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 157) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 157))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 157)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0157 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 157) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 157))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 157)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0158 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 158) = g32p_row36_cosetRepresentatives 158 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0158 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 158) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 158))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 158)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0158 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 158) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 158))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 158)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0159 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 159) = g32p_row36_cosetRepresentatives 159 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0159 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 159) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 159))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 159)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0159 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 159) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 159))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 159)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0009 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 9 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 9 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0144
  · exact g32p_row36_cosetWord_0145
  · exact g32p_row36_cosetWord_0146
  · exact g32p_row36_cosetWord_0147
  · exact g32p_row36_cosetWord_0148
  · exact g32p_row36_cosetWord_0149
  · exact g32p_row36_cosetWord_0150
  · exact g32p_row36_cosetWord_0151
  · exact g32p_row36_cosetWord_0152
  · exact g32p_row36_cosetWord_0153
  · exact g32p_row36_cosetWord_0154
  · exact g32p_row36_cosetWord_0155
  · exact g32p_row36_cosetWord_0156
  · exact g32p_row36_cosetWord_0157
  · exact g32p_row36_cosetWord_0158
  · exact g32p_row36_cosetWord_0159

theorem g32p_row36_cosetGeneratorBlock_0009 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 9 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 9 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 9 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0144 s
  · exact g32p_row36_cosetGeneratorStep_0145 s
  · exact g32p_row36_cosetGeneratorStep_0146 s
  · exact g32p_row36_cosetGeneratorStep_0147 s
  · exact g32p_row36_cosetGeneratorStep_0148 s
  · exact g32p_row36_cosetGeneratorStep_0149 s
  · exact g32p_row36_cosetGeneratorStep_0150 s
  · exact g32p_row36_cosetGeneratorStep_0151 s
  · exact g32p_row36_cosetGeneratorStep_0152 s
  · exact g32p_row36_cosetGeneratorStep_0153 s
  · exact g32p_row36_cosetGeneratorStep_0154 s
  · exact g32p_row36_cosetGeneratorStep_0155 s
  · exact g32p_row36_cosetGeneratorStep_0156 s
  · exact g32p_row36_cosetGeneratorStep_0157 s
  · exact g32p_row36_cosetGeneratorStep_0158 s
  · exact g32p_row36_cosetGeneratorStep_0159 s

theorem g32p_row36_cosetBranchBlock_0009 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 9 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 9 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 9 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0144 s
  · exact g32p_row36_cosetBranchStep_0145 s
  · exact g32p_row36_cosetBranchStep_0146 s
  · exact g32p_row36_cosetBranchStep_0147 s
  · exact g32p_row36_cosetBranchStep_0148 s
  · exact g32p_row36_cosetBranchStep_0149 s
  · exact g32p_row36_cosetBranchStep_0150 s
  · exact g32p_row36_cosetBranchStep_0151 s
  · exact g32p_row36_cosetBranchStep_0152 s
  · exact g32p_row36_cosetBranchStep_0153 s
  · exact g32p_row36_cosetBranchStep_0154 s
  · exact g32p_row36_cosetBranchStep_0155 s
  · exact g32p_row36_cosetBranchStep_0156 s
  · exact g32p_row36_cosetBranchStep_0157 s
  · exact g32p_row36_cosetBranchStep_0158 s
  · exact g32p_row36_cosetBranchStep_0159 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0160 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 160) = g32p_row36_cosetRepresentatives 160 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0160 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 160) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 160))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 160)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0160 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 160) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 160))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 160)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0161 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 161) = g32p_row36_cosetRepresentatives 161 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0161 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 161) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 161))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 161)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0161 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 161) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 161))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 161)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0162 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 162) = g32p_row36_cosetRepresentatives 162 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0162 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 162) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 162))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 162)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0162 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 162) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 162))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 162)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0163 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 163) = g32p_row36_cosetRepresentatives 163 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0163 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 163) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 163))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 163)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0163 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 163) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 163))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 163)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0164 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 164) = g32p_row36_cosetRepresentatives 164 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0164 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 164) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 164))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 164)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0164 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 164) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 164))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 164)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0165 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 165) = g32p_row36_cosetRepresentatives 165 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0165 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 165) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 165))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 165)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0165 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 165) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 165))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 165)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0166 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 166) = g32p_row36_cosetRepresentatives 166 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0166 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 166) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 166))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 166)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0166 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 166) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 166))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 166)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0167 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 167) = g32p_row36_cosetRepresentatives 167 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0167 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 167) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 167))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 167)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0167 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 167) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 167))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 167)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0168 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 168) = g32p_row36_cosetRepresentatives 168 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0168 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 168) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 168))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 168)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0168 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 168) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 168))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 168)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0169 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 169) = g32p_row36_cosetRepresentatives 169 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0169 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 169) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 169))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 169)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0169 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 169) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 169))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 169)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0170 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 170) = g32p_row36_cosetRepresentatives 170 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0170 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 170) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 170))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 170)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0170 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 170) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 170))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 170)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0171 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 171) = g32p_row36_cosetRepresentatives 171 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0171 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 171) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 171))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 171)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0171 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 171) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 171))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 171)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0172 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 172) = g32p_row36_cosetRepresentatives 172 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0172 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 172) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 172))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 172)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0172 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 172) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 172))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 172)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0173 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 173) = g32p_row36_cosetRepresentatives 173 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0173 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 173) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 173))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 173)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0173 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 173) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 173))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 173)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0174 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 174) = g32p_row36_cosetRepresentatives 174 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0174 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 174) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 174))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 174)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0174 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 174) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 174))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 174)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0175 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 175) = g32p_row36_cosetRepresentatives 175 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0175 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 175) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 175))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 175)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0175 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 175) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 175))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 175)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0010 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 10 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 10 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0160
  · exact g32p_row36_cosetWord_0161
  · exact g32p_row36_cosetWord_0162
  · exact g32p_row36_cosetWord_0163
  · exact g32p_row36_cosetWord_0164
  · exact g32p_row36_cosetWord_0165
  · exact g32p_row36_cosetWord_0166
  · exact g32p_row36_cosetWord_0167
  · exact g32p_row36_cosetWord_0168
  · exact g32p_row36_cosetWord_0169
  · exact g32p_row36_cosetWord_0170
  · exact g32p_row36_cosetWord_0171
  · exact g32p_row36_cosetWord_0172
  · exact g32p_row36_cosetWord_0173
  · exact g32p_row36_cosetWord_0174
  · exact g32p_row36_cosetWord_0175

theorem g32p_row36_cosetGeneratorBlock_0010 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 10 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 10 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 10 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0160 s
  · exact g32p_row36_cosetGeneratorStep_0161 s
  · exact g32p_row36_cosetGeneratorStep_0162 s
  · exact g32p_row36_cosetGeneratorStep_0163 s
  · exact g32p_row36_cosetGeneratorStep_0164 s
  · exact g32p_row36_cosetGeneratorStep_0165 s
  · exact g32p_row36_cosetGeneratorStep_0166 s
  · exact g32p_row36_cosetGeneratorStep_0167 s
  · exact g32p_row36_cosetGeneratorStep_0168 s
  · exact g32p_row36_cosetGeneratorStep_0169 s
  · exact g32p_row36_cosetGeneratorStep_0170 s
  · exact g32p_row36_cosetGeneratorStep_0171 s
  · exact g32p_row36_cosetGeneratorStep_0172 s
  · exact g32p_row36_cosetGeneratorStep_0173 s
  · exact g32p_row36_cosetGeneratorStep_0174 s
  · exact g32p_row36_cosetGeneratorStep_0175 s

theorem g32p_row36_cosetBranchBlock_0010 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 10 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 10 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 10 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0160 s
  · exact g32p_row36_cosetBranchStep_0161 s
  · exact g32p_row36_cosetBranchStep_0162 s
  · exact g32p_row36_cosetBranchStep_0163 s
  · exact g32p_row36_cosetBranchStep_0164 s
  · exact g32p_row36_cosetBranchStep_0165 s
  · exact g32p_row36_cosetBranchStep_0166 s
  · exact g32p_row36_cosetBranchStep_0167 s
  · exact g32p_row36_cosetBranchStep_0168 s
  · exact g32p_row36_cosetBranchStep_0169 s
  · exact g32p_row36_cosetBranchStep_0170 s
  · exact g32p_row36_cosetBranchStep_0171 s
  · exact g32p_row36_cosetBranchStep_0172 s
  · exact g32p_row36_cosetBranchStep_0173 s
  · exact g32p_row36_cosetBranchStep_0174 s
  · exact g32p_row36_cosetBranchStep_0175 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0176 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 176) = g32p_row36_cosetRepresentatives 176 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0176 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 176) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 176))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 176)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0176 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 176) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 176))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 176)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0177 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 177) = g32p_row36_cosetRepresentatives 177 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0177 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 177) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 177))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 177)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0177 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 177) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 177))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 177)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0178 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 178) = g32p_row36_cosetRepresentatives 178 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0178 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 178) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 178))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 178)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0178 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 178) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 178))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 178)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0179 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 179) = g32p_row36_cosetRepresentatives 179 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0179 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 179) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 179))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 179)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0179 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 179) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 179))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 179)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0180 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 180) = g32p_row36_cosetRepresentatives 180 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0180 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 180) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 180))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 180)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0180 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 180) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 180))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 180)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0181 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 181) = g32p_row36_cosetRepresentatives 181 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0181 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 181) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 181))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 181)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0181 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 181) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 181))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 181)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0182 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 182) = g32p_row36_cosetRepresentatives 182 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0182 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 182) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 182))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 182)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0182 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 182) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 182))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 182)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0183 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 183) = g32p_row36_cosetRepresentatives 183 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0183 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 183) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 183))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 183)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0183 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 183) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 183))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 183)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0184 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 184) = g32p_row36_cosetRepresentatives 184 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0184 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 184) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 184))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 184)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0184 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 184) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 184))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 184)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0185 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 185) = g32p_row36_cosetRepresentatives 185 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0185 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 185) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 185))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 185)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0185 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 185) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 185))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 185)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0186 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 186) = g32p_row36_cosetRepresentatives 186 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0186 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 186) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 186))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 186)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0186 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 186) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 186))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 186)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0187 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 187) = g32p_row36_cosetRepresentatives 187 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0187 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 187) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 187))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 187)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0187 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 187) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 187))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 187)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0188 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 188) = g32p_row36_cosetRepresentatives 188 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0188 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 188) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 188))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 188)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0188 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 188) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 188))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 188)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0189 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 189) = g32p_row36_cosetRepresentatives 189 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0189 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 189) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 189))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 189)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0189 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 189) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 189))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 189)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0190 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 190) = g32p_row36_cosetRepresentatives 190 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0190 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 190) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 190))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 190)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0190 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 190) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 190))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 190)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0191 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 191) = g32p_row36_cosetRepresentatives 191 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0191 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 191) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 191))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 191)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0191 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 191) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 191))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 191)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0011 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 11 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 11 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0176
  · exact g32p_row36_cosetWord_0177
  · exact g32p_row36_cosetWord_0178
  · exact g32p_row36_cosetWord_0179
  · exact g32p_row36_cosetWord_0180
  · exact g32p_row36_cosetWord_0181
  · exact g32p_row36_cosetWord_0182
  · exact g32p_row36_cosetWord_0183
  · exact g32p_row36_cosetWord_0184
  · exact g32p_row36_cosetWord_0185
  · exact g32p_row36_cosetWord_0186
  · exact g32p_row36_cosetWord_0187
  · exact g32p_row36_cosetWord_0188
  · exact g32p_row36_cosetWord_0189
  · exact g32p_row36_cosetWord_0190
  · exact g32p_row36_cosetWord_0191

theorem g32p_row36_cosetGeneratorBlock_0011 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 11 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 11 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 11 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0176 s
  · exact g32p_row36_cosetGeneratorStep_0177 s
  · exact g32p_row36_cosetGeneratorStep_0178 s
  · exact g32p_row36_cosetGeneratorStep_0179 s
  · exact g32p_row36_cosetGeneratorStep_0180 s
  · exact g32p_row36_cosetGeneratorStep_0181 s
  · exact g32p_row36_cosetGeneratorStep_0182 s
  · exact g32p_row36_cosetGeneratorStep_0183 s
  · exact g32p_row36_cosetGeneratorStep_0184 s
  · exact g32p_row36_cosetGeneratorStep_0185 s
  · exact g32p_row36_cosetGeneratorStep_0186 s
  · exact g32p_row36_cosetGeneratorStep_0187 s
  · exact g32p_row36_cosetGeneratorStep_0188 s
  · exact g32p_row36_cosetGeneratorStep_0189 s
  · exact g32p_row36_cosetGeneratorStep_0190 s
  · exact g32p_row36_cosetGeneratorStep_0191 s

theorem g32p_row36_cosetBranchBlock_0011 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 11 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 11 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 11 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0176 s
  · exact g32p_row36_cosetBranchStep_0177 s
  · exact g32p_row36_cosetBranchStep_0178 s
  · exact g32p_row36_cosetBranchStep_0179 s
  · exact g32p_row36_cosetBranchStep_0180 s
  · exact g32p_row36_cosetBranchStep_0181 s
  · exact g32p_row36_cosetBranchStep_0182 s
  · exact g32p_row36_cosetBranchStep_0183 s
  · exact g32p_row36_cosetBranchStep_0184 s
  · exact g32p_row36_cosetBranchStep_0185 s
  · exact g32p_row36_cosetBranchStep_0186 s
  · exact g32p_row36_cosetBranchStep_0187 s
  · exact g32p_row36_cosetBranchStep_0188 s
  · exact g32p_row36_cosetBranchStep_0189 s
  · exact g32p_row36_cosetBranchStep_0190 s
  · exact g32p_row36_cosetBranchStep_0191 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0192 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 192) = g32p_row36_cosetRepresentatives 192 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0192 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 192) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 192))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 192)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0192 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 192) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 192))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 192)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0193 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 193) = g32p_row36_cosetRepresentatives 193 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0193 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 193) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 193))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 193)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0193 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 193) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 193))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 193)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0194 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 194) = g32p_row36_cosetRepresentatives 194 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0194 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 194) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 194))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 194)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0194 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 194) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 194))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 194)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0195 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 195) = g32p_row36_cosetRepresentatives 195 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0195 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 195) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 195))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 195)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0195 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 195) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 195))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 195)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0196 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 196) = g32p_row36_cosetRepresentatives 196 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0196 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 196) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 196))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 196)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0196 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 196) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 196))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 196)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0197 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 197) = g32p_row36_cosetRepresentatives 197 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0197 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 197) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 197))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 197)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0197 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 197) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 197))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 197)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0198 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 198) = g32p_row36_cosetRepresentatives 198 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0198 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 198) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 198))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 198)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0198 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 198) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 198))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 198)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0199 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 199) = g32p_row36_cosetRepresentatives 199 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0199 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 199) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 199))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 199)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0199 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 199) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 199))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 199)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0200 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 200) = g32p_row36_cosetRepresentatives 200 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0200 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 200) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 200))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 200)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0200 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 200) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 200))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 200)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0201 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 201) = g32p_row36_cosetRepresentatives 201 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0201 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 201) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 201))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 201)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0201 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 201) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 201))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 201)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0202 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 202) = g32p_row36_cosetRepresentatives 202 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0202 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 202) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 202))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 202)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0202 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 202) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 202))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 202)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0203 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 203) = g32p_row36_cosetRepresentatives 203 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0203 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 203) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 203))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 203)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0203 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 203) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 203))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 203)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0204 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 204) = g32p_row36_cosetRepresentatives 204 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0204 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 204) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 204))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 204)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0204 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 204) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 204))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 204)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0205 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 205) = g32p_row36_cosetRepresentatives 205 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0205 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 205) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 205))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 205)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0205 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 205) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 205))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 205)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0206 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 206) = g32p_row36_cosetRepresentatives 206 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0206 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 206) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 206))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 206)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0206 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 206) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 206))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 206)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0207 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 207) = g32p_row36_cosetRepresentatives 207 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0207 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 207) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 207))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 207)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0207 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 207) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 207))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 207)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0012 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 12 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 12 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0192
  · exact g32p_row36_cosetWord_0193
  · exact g32p_row36_cosetWord_0194
  · exact g32p_row36_cosetWord_0195
  · exact g32p_row36_cosetWord_0196
  · exact g32p_row36_cosetWord_0197
  · exact g32p_row36_cosetWord_0198
  · exact g32p_row36_cosetWord_0199
  · exact g32p_row36_cosetWord_0200
  · exact g32p_row36_cosetWord_0201
  · exact g32p_row36_cosetWord_0202
  · exact g32p_row36_cosetWord_0203
  · exact g32p_row36_cosetWord_0204
  · exact g32p_row36_cosetWord_0205
  · exact g32p_row36_cosetWord_0206
  · exact g32p_row36_cosetWord_0207

theorem g32p_row36_cosetGeneratorBlock_0012 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 12 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 12 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 12 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0192 s
  · exact g32p_row36_cosetGeneratorStep_0193 s
  · exact g32p_row36_cosetGeneratorStep_0194 s
  · exact g32p_row36_cosetGeneratorStep_0195 s
  · exact g32p_row36_cosetGeneratorStep_0196 s
  · exact g32p_row36_cosetGeneratorStep_0197 s
  · exact g32p_row36_cosetGeneratorStep_0198 s
  · exact g32p_row36_cosetGeneratorStep_0199 s
  · exact g32p_row36_cosetGeneratorStep_0200 s
  · exact g32p_row36_cosetGeneratorStep_0201 s
  · exact g32p_row36_cosetGeneratorStep_0202 s
  · exact g32p_row36_cosetGeneratorStep_0203 s
  · exact g32p_row36_cosetGeneratorStep_0204 s
  · exact g32p_row36_cosetGeneratorStep_0205 s
  · exact g32p_row36_cosetGeneratorStep_0206 s
  · exact g32p_row36_cosetGeneratorStep_0207 s

theorem g32p_row36_cosetBranchBlock_0012 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 12 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 12 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 12 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0192 s
  · exact g32p_row36_cosetBranchStep_0193 s
  · exact g32p_row36_cosetBranchStep_0194 s
  · exact g32p_row36_cosetBranchStep_0195 s
  · exact g32p_row36_cosetBranchStep_0196 s
  · exact g32p_row36_cosetBranchStep_0197 s
  · exact g32p_row36_cosetBranchStep_0198 s
  · exact g32p_row36_cosetBranchStep_0199 s
  · exact g32p_row36_cosetBranchStep_0200 s
  · exact g32p_row36_cosetBranchStep_0201 s
  · exact g32p_row36_cosetBranchStep_0202 s
  · exact g32p_row36_cosetBranchStep_0203 s
  · exact g32p_row36_cosetBranchStep_0204 s
  · exact g32p_row36_cosetBranchStep_0205 s
  · exact g32p_row36_cosetBranchStep_0206 s
  · exact g32p_row36_cosetBranchStep_0207 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0208 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 208) = g32p_row36_cosetRepresentatives 208 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0208 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 208) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 208))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 208)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0208 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 208) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 208))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 208)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0209 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 209) = g32p_row36_cosetRepresentatives 209 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0209 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 209) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 209))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 209)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0209 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 209) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 209))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 209)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0210 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 210) = g32p_row36_cosetRepresentatives 210 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0210 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 210) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 210))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 210)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0210 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 210) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 210))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 210)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0211 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 211) = g32p_row36_cosetRepresentatives 211 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0211 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 211) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 211))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 211)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0211 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 211) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 211))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 211)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0212 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 212) = g32p_row36_cosetRepresentatives 212 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0212 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 212) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 212))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 212)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0212 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 212) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 212))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 212)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0213 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 213) = g32p_row36_cosetRepresentatives 213 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0213 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 213) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 213))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 213)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0213 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 213) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 213))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 213)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0214 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 214) = g32p_row36_cosetRepresentatives 214 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0214 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 214) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 214))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 214)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0214 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 214) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 214))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 214)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0215 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 215) = g32p_row36_cosetRepresentatives 215 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0215 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 215) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 215))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 215)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0215 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 215) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 215))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 215)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0216 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 216) = g32p_row36_cosetRepresentatives 216 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0216 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 216) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 216))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 216)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0216 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 216) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 216))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 216)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0217 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 217) = g32p_row36_cosetRepresentatives 217 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0217 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 217) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 217))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 217)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0217 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 217) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 217))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 217)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0218 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 218) = g32p_row36_cosetRepresentatives 218 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0218 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 218) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 218))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 218)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0218 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 218) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 218))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 218)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0219 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 219) = g32p_row36_cosetRepresentatives 219 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0219 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 219) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 219))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 219)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0219 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 219) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 219))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 219)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0220 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 220) = g32p_row36_cosetRepresentatives 220 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0220 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 220) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 220))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 220)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0220 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 220) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 220))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 220)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0221 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 221) = g32p_row36_cosetRepresentatives 221 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0221 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 221) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 221))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 221)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0221 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 221) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 221))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 221)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0222 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 222) = g32p_row36_cosetRepresentatives 222 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0222 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 222) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 222))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 222)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0222 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 222) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 222))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 222)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0223 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 223) = g32p_row36_cosetRepresentatives 223 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0223 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 223) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 223))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 223)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0223 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 223) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 223))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 223)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0013 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 13 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 13 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0208
  · exact g32p_row36_cosetWord_0209
  · exact g32p_row36_cosetWord_0210
  · exact g32p_row36_cosetWord_0211
  · exact g32p_row36_cosetWord_0212
  · exact g32p_row36_cosetWord_0213
  · exact g32p_row36_cosetWord_0214
  · exact g32p_row36_cosetWord_0215
  · exact g32p_row36_cosetWord_0216
  · exact g32p_row36_cosetWord_0217
  · exact g32p_row36_cosetWord_0218
  · exact g32p_row36_cosetWord_0219
  · exact g32p_row36_cosetWord_0220
  · exact g32p_row36_cosetWord_0221
  · exact g32p_row36_cosetWord_0222
  · exact g32p_row36_cosetWord_0223

theorem g32p_row36_cosetGeneratorBlock_0013 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 13 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 13 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 13 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0208 s
  · exact g32p_row36_cosetGeneratorStep_0209 s
  · exact g32p_row36_cosetGeneratorStep_0210 s
  · exact g32p_row36_cosetGeneratorStep_0211 s
  · exact g32p_row36_cosetGeneratorStep_0212 s
  · exact g32p_row36_cosetGeneratorStep_0213 s
  · exact g32p_row36_cosetGeneratorStep_0214 s
  · exact g32p_row36_cosetGeneratorStep_0215 s
  · exact g32p_row36_cosetGeneratorStep_0216 s
  · exact g32p_row36_cosetGeneratorStep_0217 s
  · exact g32p_row36_cosetGeneratorStep_0218 s
  · exact g32p_row36_cosetGeneratorStep_0219 s
  · exact g32p_row36_cosetGeneratorStep_0220 s
  · exact g32p_row36_cosetGeneratorStep_0221 s
  · exact g32p_row36_cosetGeneratorStep_0222 s
  · exact g32p_row36_cosetGeneratorStep_0223 s

theorem g32p_row36_cosetBranchBlock_0013 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 13 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 13 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 13 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0208 s
  · exact g32p_row36_cosetBranchStep_0209 s
  · exact g32p_row36_cosetBranchStep_0210 s
  · exact g32p_row36_cosetBranchStep_0211 s
  · exact g32p_row36_cosetBranchStep_0212 s
  · exact g32p_row36_cosetBranchStep_0213 s
  · exact g32p_row36_cosetBranchStep_0214 s
  · exact g32p_row36_cosetBranchStep_0215 s
  · exact g32p_row36_cosetBranchStep_0216 s
  · exact g32p_row36_cosetBranchStep_0217 s
  · exact g32p_row36_cosetBranchStep_0218 s
  · exact g32p_row36_cosetBranchStep_0219 s
  · exact g32p_row36_cosetBranchStep_0220 s
  · exact g32p_row36_cosetBranchStep_0221 s
  · exact g32p_row36_cosetBranchStep_0222 s
  · exact g32p_row36_cosetBranchStep_0223 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0224 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 224) = g32p_row36_cosetRepresentatives 224 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0224 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 224) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 224))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 224)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0224 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 224) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 224))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 224)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0225 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 225) = g32p_row36_cosetRepresentatives 225 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0225 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 225) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 225))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 225)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0225 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 225) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 225))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 225)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0226 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 226) = g32p_row36_cosetRepresentatives 226 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0226 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 226) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 226))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 226)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0226 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 226) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 226))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 226)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0227 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 227) = g32p_row36_cosetRepresentatives 227 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0227 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 227) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 227))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 227)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0227 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 227) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 227))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 227)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0228 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 228) = g32p_row36_cosetRepresentatives 228 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0228 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 228) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 228))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 228)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0228 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 228) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 228))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 228)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0229 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 229) = g32p_row36_cosetRepresentatives 229 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0229 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 229) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 229))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 229)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0229 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 229) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 229))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 229)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0230 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 230) = g32p_row36_cosetRepresentatives 230 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0230 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 230) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 230))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 230)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0230 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 230) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 230))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 230)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0231 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 231) = g32p_row36_cosetRepresentatives 231 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0231 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 231) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 231))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 231)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0231 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 231) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 231))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 231)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0232 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 232) = g32p_row36_cosetRepresentatives 232 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0232 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 232) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 232))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 232)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0232 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 232) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 232))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 232)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0233 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 233) = g32p_row36_cosetRepresentatives 233 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0233 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 233) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 233))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 233)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0233 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 233) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 233))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 233)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0234 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 234) = g32p_row36_cosetRepresentatives 234 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0234 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 234) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 234))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 234)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0234 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 234) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 234))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 234)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0235 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 235) = g32p_row36_cosetRepresentatives 235 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0235 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 235) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 235))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 235)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0235 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 235) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 235))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 235)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0236 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 236) = g32p_row36_cosetRepresentatives 236 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0236 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 236) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 236))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 236)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0236 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 236) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 236))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 236)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0237 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 237) = g32p_row36_cosetRepresentatives 237 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0237 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 237) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 237))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 237)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0237 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 237) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 237))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 237)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0238 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 238) = g32p_row36_cosetRepresentatives 238 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0238 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 238) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 238))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 238)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0238 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 238) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 238))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 238)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0239 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 239) = g32p_row36_cosetRepresentatives 239 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0239 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 239) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 239))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 239)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0239 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 239) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 239))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 239)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0014 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 14 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 14 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0224
  · exact g32p_row36_cosetWord_0225
  · exact g32p_row36_cosetWord_0226
  · exact g32p_row36_cosetWord_0227
  · exact g32p_row36_cosetWord_0228
  · exact g32p_row36_cosetWord_0229
  · exact g32p_row36_cosetWord_0230
  · exact g32p_row36_cosetWord_0231
  · exact g32p_row36_cosetWord_0232
  · exact g32p_row36_cosetWord_0233
  · exact g32p_row36_cosetWord_0234
  · exact g32p_row36_cosetWord_0235
  · exact g32p_row36_cosetWord_0236
  · exact g32p_row36_cosetWord_0237
  · exact g32p_row36_cosetWord_0238
  · exact g32p_row36_cosetWord_0239

theorem g32p_row36_cosetGeneratorBlock_0014 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 14 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 14 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 14 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0224 s
  · exact g32p_row36_cosetGeneratorStep_0225 s
  · exact g32p_row36_cosetGeneratorStep_0226 s
  · exact g32p_row36_cosetGeneratorStep_0227 s
  · exact g32p_row36_cosetGeneratorStep_0228 s
  · exact g32p_row36_cosetGeneratorStep_0229 s
  · exact g32p_row36_cosetGeneratorStep_0230 s
  · exact g32p_row36_cosetGeneratorStep_0231 s
  · exact g32p_row36_cosetGeneratorStep_0232 s
  · exact g32p_row36_cosetGeneratorStep_0233 s
  · exact g32p_row36_cosetGeneratorStep_0234 s
  · exact g32p_row36_cosetGeneratorStep_0235 s
  · exact g32p_row36_cosetGeneratorStep_0236 s
  · exact g32p_row36_cosetGeneratorStep_0237 s
  · exact g32p_row36_cosetGeneratorStep_0238 s
  · exact g32p_row36_cosetGeneratorStep_0239 s

theorem g32p_row36_cosetBranchBlock_0014 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 14 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 14 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 14 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0224 s
  · exact g32p_row36_cosetBranchStep_0225 s
  · exact g32p_row36_cosetBranchStep_0226 s
  · exact g32p_row36_cosetBranchStep_0227 s
  · exact g32p_row36_cosetBranchStep_0228 s
  · exact g32p_row36_cosetBranchStep_0229 s
  · exact g32p_row36_cosetBranchStep_0230 s
  · exact g32p_row36_cosetBranchStep_0231 s
  · exact g32p_row36_cosetBranchStep_0232 s
  · exact g32p_row36_cosetBranchStep_0233 s
  · exact g32p_row36_cosetBranchStep_0234 s
  · exact g32p_row36_cosetBranchStep_0235 s
  · exact g32p_row36_cosetBranchStep_0236 s
  · exact g32p_row36_cosetBranchStep_0237 s
  · exact g32p_row36_cosetBranchStep_0238 s
  · exact g32p_row36_cosetBranchStep_0239 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0240 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 240) = g32p_row36_cosetRepresentatives 240 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0240 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 240) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 240))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 240)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0240 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 240) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 240))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 240)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0241 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 241) = g32p_row36_cosetRepresentatives 241 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0241 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 241) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 241))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 241)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0241 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 241) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 241))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 241)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0242 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 242) = g32p_row36_cosetRepresentatives 242 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0242 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 242) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 242))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 242)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0242 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 242) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 242))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 242)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0243 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 243) = g32p_row36_cosetRepresentatives 243 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0243 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 243) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 243))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 243)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0243 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 243) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 243))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 243)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0244 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 244) = g32p_row36_cosetRepresentatives 244 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0244 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 244) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 244))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 244)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0244 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 244) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 244))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 244)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0245 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 245) = g32p_row36_cosetRepresentatives 245 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0245 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 245) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 245))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 245)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0245 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 245) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 245))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 245)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0246 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 246) = g32p_row36_cosetRepresentatives 246 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0246 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 246) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 246))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 246)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0246 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 246) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 246))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 246)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0247 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 247) = g32p_row36_cosetRepresentatives 247 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0247 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 247) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 247))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 247)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0247 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 247) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 247))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 247)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0248 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 248) = g32p_row36_cosetRepresentatives 248 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0248 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 248) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 248))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 248)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0248 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 248) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 248))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 248)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0249 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 249) = g32p_row36_cosetRepresentatives 249 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0249 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 249) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 249))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 249)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0249 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 249) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 249))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 249)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0250 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 250) = g32p_row36_cosetRepresentatives 250 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0250 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 250) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 250))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 250)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0250 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 250) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 250))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 250)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0251 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 251) = g32p_row36_cosetRepresentatives 251 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0251 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 251) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 251))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 251)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0251 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 251) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 251))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 251)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0252 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 252) = g32p_row36_cosetRepresentatives 252 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0252 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 252) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 252))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 252)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0252 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 252) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 252))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 252)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0253 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 253) = g32p_row36_cosetRepresentatives 253 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0253 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 253) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 253))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 253)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0253 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 253) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 253))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 253)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0254 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 254) = g32p_row36_cosetRepresentatives 254 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0254 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 254) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 254))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 254)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0254 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 254) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 254))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 254)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0255 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 255) = g32p_row36_cosetRepresentatives 255 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0255 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 255) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 255))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 255)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0255 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 255) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 255))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 255)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0015 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 15 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 15 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0240
  · exact g32p_row36_cosetWord_0241
  · exact g32p_row36_cosetWord_0242
  · exact g32p_row36_cosetWord_0243
  · exact g32p_row36_cosetWord_0244
  · exact g32p_row36_cosetWord_0245
  · exact g32p_row36_cosetWord_0246
  · exact g32p_row36_cosetWord_0247
  · exact g32p_row36_cosetWord_0248
  · exact g32p_row36_cosetWord_0249
  · exact g32p_row36_cosetWord_0250
  · exact g32p_row36_cosetWord_0251
  · exact g32p_row36_cosetWord_0252
  · exact g32p_row36_cosetWord_0253
  · exact g32p_row36_cosetWord_0254
  · exact g32p_row36_cosetWord_0255

theorem g32p_row36_cosetGeneratorBlock_0015 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 15 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 15 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 15 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0240 s
  · exact g32p_row36_cosetGeneratorStep_0241 s
  · exact g32p_row36_cosetGeneratorStep_0242 s
  · exact g32p_row36_cosetGeneratorStep_0243 s
  · exact g32p_row36_cosetGeneratorStep_0244 s
  · exact g32p_row36_cosetGeneratorStep_0245 s
  · exact g32p_row36_cosetGeneratorStep_0246 s
  · exact g32p_row36_cosetGeneratorStep_0247 s
  · exact g32p_row36_cosetGeneratorStep_0248 s
  · exact g32p_row36_cosetGeneratorStep_0249 s
  · exact g32p_row36_cosetGeneratorStep_0250 s
  · exact g32p_row36_cosetGeneratorStep_0251 s
  · exact g32p_row36_cosetGeneratorStep_0252 s
  · exact g32p_row36_cosetGeneratorStep_0253 s
  · exact g32p_row36_cosetGeneratorStep_0254 s
  · exact g32p_row36_cosetGeneratorStep_0255 s

theorem g32p_row36_cosetBranchBlock_0015 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 15 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 15 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 15 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0240 s
  · exact g32p_row36_cosetBranchStep_0241 s
  · exact g32p_row36_cosetBranchStep_0242 s
  · exact g32p_row36_cosetBranchStep_0243 s
  · exact g32p_row36_cosetBranchStep_0244 s
  · exact g32p_row36_cosetBranchStep_0245 s
  · exact g32p_row36_cosetBranchStep_0246 s
  · exact g32p_row36_cosetBranchStep_0247 s
  · exact g32p_row36_cosetBranchStep_0248 s
  · exact g32p_row36_cosetBranchStep_0249 s
  · exact g32p_row36_cosetBranchStep_0250 s
  · exact g32p_row36_cosetBranchStep_0251 s
  · exact g32p_row36_cosetBranchStep_0252 s
  · exact g32p_row36_cosetBranchStep_0253 s
  · exact g32p_row36_cosetBranchStep_0254 s
  · exact g32p_row36_cosetBranchStep_0255 s


end HodgeLean.Foundations.Program

end
