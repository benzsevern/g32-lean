import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness02CosetData

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0000 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 0) = g32p_row02_cosetRepresentatives 0 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0000 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 0))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 0)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0000 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 0))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 0)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0001 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 1) = g32p_row02_cosetRepresentatives 1 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0001 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 1))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 1)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0001 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 1))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 1)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0002 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 2) = g32p_row02_cosetRepresentatives 2 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0002 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 2))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 2)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0002 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 2))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 2)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0003 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 3) = g32p_row02_cosetRepresentatives 3 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0003 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 3))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 3)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0003 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 3))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 3)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0004 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 4) = g32p_row02_cosetRepresentatives 4 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0004 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 4))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 4)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0004 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 4))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 4)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0005 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 5) = g32p_row02_cosetRepresentatives 5 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0005 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 5))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 5)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0005 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 5))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 5)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0006 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 6) = g32p_row02_cosetRepresentatives 6 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0006 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 6))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 6)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0006 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 6))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 6)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0007 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 7) = g32p_row02_cosetRepresentatives 7 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0007 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 7))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 7)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0007 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 7))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 7)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0008 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 8) = g32p_row02_cosetRepresentatives 8 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0008 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 8))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 8)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0008 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 8))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 8)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0009 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 9) = g32p_row02_cosetRepresentatives 9 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0009 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 9))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 9)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0009 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 9))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 9)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0010 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 10) = g32p_row02_cosetRepresentatives 10 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0010 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 10))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 10)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0010 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 10))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 10)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0011 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 11) = g32p_row02_cosetRepresentatives 11 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0011 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 11))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 11)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0011 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 11))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 11)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0012 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 12) = g32p_row02_cosetRepresentatives 12 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0012 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 12))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 12)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0012 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 12))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 12)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0013 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 13) = g32p_row02_cosetRepresentatives 13 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0013 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 13))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 13)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0013 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 13))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 13)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0014 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 14) = g32p_row02_cosetRepresentatives 14 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0014 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 14))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 14)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0014 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 14))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 14)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetWord_0015 :
    g32p_archiveIntegralWord (g32p_row02_cosetWords 15) = g32p_row02_cosetRepresentatives 15 := by
  decide +kernel

theorem g32p_row02_cosetGeneratorStep_0015 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row02_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetGeneratorNext s 15))
        (g32p_row02_groupNodes (g32p_row02_cosetGeneratorFactor s 15)) := by
  decide +kernel

theorem g32p_row02_cosetBranchStep_0015 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices s) (g32p_row02_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext s 15))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor s 15)) := by
  decide +kernel


end HodgeLean.Foundations.Program

end
