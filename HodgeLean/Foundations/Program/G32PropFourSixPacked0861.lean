import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0835

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6400 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6400) = g32p_row31_cosetRepresentatives 6400 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6400 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6400) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6400))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6400)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6400 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6400) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6400))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6400)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6401 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6401) = g32p_row31_cosetRepresentatives 6401 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6401 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6401) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6401))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6401)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6401 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6401) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6401))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6401)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6402 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6402) = g32p_row31_cosetRepresentatives 6402 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6402 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6402) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6402))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6402)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6402 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6402) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6402))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6402)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6403 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6403) = g32p_row31_cosetRepresentatives 6403 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6403 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6403) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6403))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6403)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6403 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6403) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6403))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6403)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6404 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6404) = g32p_row31_cosetRepresentatives 6404 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6404 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6404) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6404))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6404)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6404 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6404) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6404))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6404)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6405 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6405) = g32p_row31_cosetRepresentatives 6405 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6405 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6405) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6405))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6405)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6405 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6405) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6405))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6405)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6406 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6406) = g32p_row31_cosetRepresentatives 6406 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6406 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6406) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6406))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6406)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6406 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6406) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6406))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6406)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6407 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6407) = g32p_row31_cosetRepresentatives 6407 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6407 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6407) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6407))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6407)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6407 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6407) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6407))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6407)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6408 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6408) = g32p_row31_cosetRepresentatives 6408 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6408 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6408) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6408))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6408)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6408 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6408) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6408))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6408)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6409 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6409) = g32p_row31_cosetRepresentatives 6409 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6409 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6409) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6409))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6409)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6409 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6409) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6409))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6409)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6410 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6410) = g32p_row31_cosetRepresentatives 6410 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6410 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6410) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6410))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6410)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6410 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6410) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6410))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6410)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6411 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6411) = g32p_row31_cosetRepresentatives 6411 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6411 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6411) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6411))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6411)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6411 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6411) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6411))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6411)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6412 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6412) = g32p_row31_cosetRepresentatives 6412 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6412 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6412) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6412))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6412)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6412 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6412) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6412))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6412)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6413 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6413) = g32p_row31_cosetRepresentatives 6413 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6413 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6413) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6413))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6413)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6413 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6413) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6413))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6413)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6414 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6414) = g32p_row31_cosetRepresentatives 6414 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6414 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6414) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6414))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6414)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6414 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6414) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6414))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6414)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6415 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6415) = g32p_row31_cosetRepresentatives 6415 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6415 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6415) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6415))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6415)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6415 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6415) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6415))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6415)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0400 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 400 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 400 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6400
  · exact g32p_row31_cosetWord_6401
  · exact g32p_row31_cosetWord_6402
  · exact g32p_row31_cosetWord_6403
  · exact g32p_row31_cosetWord_6404
  · exact g32p_row31_cosetWord_6405
  · exact g32p_row31_cosetWord_6406
  · exact g32p_row31_cosetWord_6407
  · exact g32p_row31_cosetWord_6408
  · exact g32p_row31_cosetWord_6409
  · exact g32p_row31_cosetWord_6410
  · exact g32p_row31_cosetWord_6411
  · exact g32p_row31_cosetWord_6412
  · exact g32p_row31_cosetWord_6413
  · exact g32p_row31_cosetWord_6414
  · exact g32p_row31_cosetWord_6415

theorem g32p_row31_cosetGeneratorBlock_0400 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 400 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 400 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 400 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6400 s
  · exact g32p_row31_cosetGeneratorStep_6401 s
  · exact g32p_row31_cosetGeneratorStep_6402 s
  · exact g32p_row31_cosetGeneratorStep_6403 s
  · exact g32p_row31_cosetGeneratorStep_6404 s
  · exact g32p_row31_cosetGeneratorStep_6405 s
  · exact g32p_row31_cosetGeneratorStep_6406 s
  · exact g32p_row31_cosetGeneratorStep_6407 s
  · exact g32p_row31_cosetGeneratorStep_6408 s
  · exact g32p_row31_cosetGeneratorStep_6409 s
  · exact g32p_row31_cosetGeneratorStep_6410 s
  · exact g32p_row31_cosetGeneratorStep_6411 s
  · exact g32p_row31_cosetGeneratorStep_6412 s
  · exact g32p_row31_cosetGeneratorStep_6413 s
  · exact g32p_row31_cosetGeneratorStep_6414 s
  · exact g32p_row31_cosetGeneratorStep_6415 s

theorem g32p_row31_cosetBranchBlock_0400 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 400 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 400 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 400 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6400 s
  · exact g32p_row31_cosetBranchStep_6401 s
  · exact g32p_row31_cosetBranchStep_6402 s
  · exact g32p_row31_cosetBranchStep_6403 s
  · exact g32p_row31_cosetBranchStep_6404 s
  · exact g32p_row31_cosetBranchStep_6405 s
  · exact g32p_row31_cosetBranchStep_6406 s
  · exact g32p_row31_cosetBranchStep_6407 s
  · exact g32p_row31_cosetBranchStep_6408 s
  · exact g32p_row31_cosetBranchStep_6409 s
  · exact g32p_row31_cosetBranchStep_6410 s
  · exact g32p_row31_cosetBranchStep_6411 s
  · exact g32p_row31_cosetBranchStep_6412 s
  · exact g32p_row31_cosetBranchStep_6413 s
  · exact g32p_row31_cosetBranchStep_6414 s
  · exact g32p_row31_cosetBranchStep_6415 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6416 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6416) = g32p_row31_cosetRepresentatives 6416 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6416 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6416) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6416))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6416)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6416 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6416) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6416))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6416)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6417 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6417) = g32p_row31_cosetRepresentatives 6417 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6417 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6417) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6417))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6417)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6417 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6417) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6417))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6417)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6418 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6418) = g32p_row31_cosetRepresentatives 6418 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6418 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6418) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6418))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6418)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6418 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6418) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6418))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6418)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6419 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6419) = g32p_row31_cosetRepresentatives 6419 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6419 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6419) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6419))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6419)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6419 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6419) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6419))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6419)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6420 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6420) = g32p_row31_cosetRepresentatives 6420 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6420 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6420) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6420))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6420)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6420 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6420) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6420))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6420)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6421 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6421) = g32p_row31_cosetRepresentatives 6421 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6421 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6421) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6421))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6421)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6421 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6421) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6421))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6421)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6422 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6422) = g32p_row31_cosetRepresentatives 6422 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6422 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6422) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6422))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6422)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6422 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6422) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6422))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6422)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6423 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6423) = g32p_row31_cosetRepresentatives 6423 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6423 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6423) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6423))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6423)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6423 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6423) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6423))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6423)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6424 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6424) = g32p_row31_cosetRepresentatives 6424 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6424 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6424) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6424))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6424)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6424 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6424) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6424))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6424)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6425 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6425) = g32p_row31_cosetRepresentatives 6425 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6425 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6425) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6425))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6425)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6425 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6425) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6425))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6425)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6426 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6426) = g32p_row31_cosetRepresentatives 6426 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6426 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6426) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6426))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6426)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6426 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6426) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6426))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6426)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6427 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6427) = g32p_row31_cosetRepresentatives 6427 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6427 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6427) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6427))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6427)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6427 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6427) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6427))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6427)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6428 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6428) = g32p_row31_cosetRepresentatives 6428 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6428 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6428) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6428))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6428)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6428 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6428) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6428))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6428)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6429 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6429) = g32p_row31_cosetRepresentatives 6429 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6429 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6429) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6429))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6429)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6429 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6429) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6429))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6429)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6430 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6430) = g32p_row31_cosetRepresentatives 6430 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6430 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6430) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6430))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6430)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6430 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6430) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6430))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6430)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6431 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6431) = g32p_row31_cosetRepresentatives 6431 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6431 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6431) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6431))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6431)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6431 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6431) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6431))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6431)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0401 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 401 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 401 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6416
  · exact g32p_row31_cosetWord_6417
  · exact g32p_row31_cosetWord_6418
  · exact g32p_row31_cosetWord_6419
  · exact g32p_row31_cosetWord_6420
  · exact g32p_row31_cosetWord_6421
  · exact g32p_row31_cosetWord_6422
  · exact g32p_row31_cosetWord_6423
  · exact g32p_row31_cosetWord_6424
  · exact g32p_row31_cosetWord_6425
  · exact g32p_row31_cosetWord_6426
  · exact g32p_row31_cosetWord_6427
  · exact g32p_row31_cosetWord_6428
  · exact g32p_row31_cosetWord_6429
  · exact g32p_row31_cosetWord_6430
  · exact g32p_row31_cosetWord_6431

theorem g32p_row31_cosetGeneratorBlock_0401 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 401 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 401 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 401 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6416 s
  · exact g32p_row31_cosetGeneratorStep_6417 s
  · exact g32p_row31_cosetGeneratorStep_6418 s
  · exact g32p_row31_cosetGeneratorStep_6419 s
  · exact g32p_row31_cosetGeneratorStep_6420 s
  · exact g32p_row31_cosetGeneratorStep_6421 s
  · exact g32p_row31_cosetGeneratorStep_6422 s
  · exact g32p_row31_cosetGeneratorStep_6423 s
  · exact g32p_row31_cosetGeneratorStep_6424 s
  · exact g32p_row31_cosetGeneratorStep_6425 s
  · exact g32p_row31_cosetGeneratorStep_6426 s
  · exact g32p_row31_cosetGeneratorStep_6427 s
  · exact g32p_row31_cosetGeneratorStep_6428 s
  · exact g32p_row31_cosetGeneratorStep_6429 s
  · exact g32p_row31_cosetGeneratorStep_6430 s
  · exact g32p_row31_cosetGeneratorStep_6431 s

theorem g32p_row31_cosetBranchBlock_0401 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 401 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 401 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 401 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6416 s
  · exact g32p_row31_cosetBranchStep_6417 s
  · exact g32p_row31_cosetBranchStep_6418 s
  · exact g32p_row31_cosetBranchStep_6419 s
  · exact g32p_row31_cosetBranchStep_6420 s
  · exact g32p_row31_cosetBranchStep_6421 s
  · exact g32p_row31_cosetBranchStep_6422 s
  · exact g32p_row31_cosetBranchStep_6423 s
  · exact g32p_row31_cosetBranchStep_6424 s
  · exact g32p_row31_cosetBranchStep_6425 s
  · exact g32p_row31_cosetBranchStep_6426 s
  · exact g32p_row31_cosetBranchStep_6427 s
  · exact g32p_row31_cosetBranchStep_6428 s
  · exact g32p_row31_cosetBranchStep_6429 s
  · exact g32p_row31_cosetBranchStep_6430 s
  · exact g32p_row31_cosetBranchStep_6431 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6432 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6432) = g32p_row31_cosetRepresentatives 6432 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6432 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6432) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6432))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6432)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6432 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6432) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6432))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6432)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6433 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6433) = g32p_row31_cosetRepresentatives 6433 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6433 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6433) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6433))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6433)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6433 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6433) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6433))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6433)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6434 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6434) = g32p_row31_cosetRepresentatives 6434 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6434 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6434) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6434))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6434)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6434 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6434) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6434))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6434)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6435 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6435) = g32p_row31_cosetRepresentatives 6435 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6435 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6435) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6435))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6435)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6435 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6435) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6435))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6435)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6436 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6436) = g32p_row31_cosetRepresentatives 6436 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6436 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6436) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6436))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6436)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6436 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6436) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6436))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6436)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6437 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6437) = g32p_row31_cosetRepresentatives 6437 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6437 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6437) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6437))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6437)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6437 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6437) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6437))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6437)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6438 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6438) = g32p_row31_cosetRepresentatives 6438 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6438 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6438) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6438))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6438)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6438 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6438) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6438))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6438)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6439 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6439) = g32p_row31_cosetRepresentatives 6439 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6439 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6439) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6439))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6439)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6439 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6439) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6439))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6439)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6440 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6440) = g32p_row31_cosetRepresentatives 6440 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6440 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6440) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6440))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6440)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6440 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6440) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6440))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6440)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6441 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6441) = g32p_row31_cosetRepresentatives 6441 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6441 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6441) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6441))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6441)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6441 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6441) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6441))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6441)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6442 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6442) = g32p_row31_cosetRepresentatives 6442 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6442 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6442) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6442))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6442)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6442 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6442) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6442))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6442)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6443 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6443) = g32p_row31_cosetRepresentatives 6443 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6443 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6443) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6443))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6443)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6443 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6443) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6443))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6443)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6444 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6444) = g32p_row31_cosetRepresentatives 6444 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6444 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6444) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6444))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6444)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6444 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6444) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6444))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6444)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6445 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6445) = g32p_row31_cosetRepresentatives 6445 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6445 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6445) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6445))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6445)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6445 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6445) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6445))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6445)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6446 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6446) = g32p_row31_cosetRepresentatives 6446 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6446 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6446) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6446))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6446)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6446 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6446) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6446))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6446)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6447 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6447) = g32p_row31_cosetRepresentatives 6447 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6447 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6447) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6447))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6447)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6447 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6447) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6447))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6447)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0402 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 402 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 402 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6432
  · exact g32p_row31_cosetWord_6433
  · exact g32p_row31_cosetWord_6434
  · exact g32p_row31_cosetWord_6435
  · exact g32p_row31_cosetWord_6436
  · exact g32p_row31_cosetWord_6437
  · exact g32p_row31_cosetWord_6438
  · exact g32p_row31_cosetWord_6439
  · exact g32p_row31_cosetWord_6440
  · exact g32p_row31_cosetWord_6441
  · exact g32p_row31_cosetWord_6442
  · exact g32p_row31_cosetWord_6443
  · exact g32p_row31_cosetWord_6444
  · exact g32p_row31_cosetWord_6445
  · exact g32p_row31_cosetWord_6446
  · exact g32p_row31_cosetWord_6447

theorem g32p_row31_cosetGeneratorBlock_0402 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 402 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 402 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 402 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6432 s
  · exact g32p_row31_cosetGeneratorStep_6433 s
  · exact g32p_row31_cosetGeneratorStep_6434 s
  · exact g32p_row31_cosetGeneratorStep_6435 s
  · exact g32p_row31_cosetGeneratorStep_6436 s
  · exact g32p_row31_cosetGeneratorStep_6437 s
  · exact g32p_row31_cosetGeneratorStep_6438 s
  · exact g32p_row31_cosetGeneratorStep_6439 s
  · exact g32p_row31_cosetGeneratorStep_6440 s
  · exact g32p_row31_cosetGeneratorStep_6441 s
  · exact g32p_row31_cosetGeneratorStep_6442 s
  · exact g32p_row31_cosetGeneratorStep_6443 s
  · exact g32p_row31_cosetGeneratorStep_6444 s
  · exact g32p_row31_cosetGeneratorStep_6445 s
  · exact g32p_row31_cosetGeneratorStep_6446 s
  · exact g32p_row31_cosetGeneratorStep_6447 s

theorem g32p_row31_cosetBranchBlock_0402 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 402 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 402 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 402 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6432 s
  · exact g32p_row31_cosetBranchStep_6433 s
  · exact g32p_row31_cosetBranchStep_6434 s
  · exact g32p_row31_cosetBranchStep_6435 s
  · exact g32p_row31_cosetBranchStep_6436 s
  · exact g32p_row31_cosetBranchStep_6437 s
  · exact g32p_row31_cosetBranchStep_6438 s
  · exact g32p_row31_cosetBranchStep_6439 s
  · exact g32p_row31_cosetBranchStep_6440 s
  · exact g32p_row31_cosetBranchStep_6441 s
  · exact g32p_row31_cosetBranchStep_6442 s
  · exact g32p_row31_cosetBranchStep_6443 s
  · exact g32p_row31_cosetBranchStep_6444 s
  · exact g32p_row31_cosetBranchStep_6445 s
  · exact g32p_row31_cosetBranchStep_6446 s
  · exact g32p_row31_cosetBranchStep_6447 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6448 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6448) = g32p_row31_cosetRepresentatives 6448 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6448 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6448) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6448))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6448)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6448 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6448) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6448))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6448)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6449 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6449) = g32p_row31_cosetRepresentatives 6449 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6449 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6449) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6449))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6449)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6449 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6449) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6449))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6449)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6450 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6450) = g32p_row31_cosetRepresentatives 6450 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6450 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6450) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6450))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6450)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6450 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6450) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6450))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6450)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6451 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6451) = g32p_row31_cosetRepresentatives 6451 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6451 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6451) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6451))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6451)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6451 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6451) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6451))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6451)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6452 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6452) = g32p_row31_cosetRepresentatives 6452 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6452 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6452) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6452))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6452)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6452 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6452) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6452))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6452)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6453 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6453) = g32p_row31_cosetRepresentatives 6453 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6453 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6453) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6453))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6453)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6453 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6453) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6453))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6453)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6454 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6454) = g32p_row31_cosetRepresentatives 6454 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6454 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6454) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6454))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6454)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6454 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6454) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6454))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6454)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6455 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6455) = g32p_row31_cosetRepresentatives 6455 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6455 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6455) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6455))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6455)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6455 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6455) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6455))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6455)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6456 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6456) = g32p_row31_cosetRepresentatives 6456 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6456 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6456) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6456))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6456)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6456 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6456) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6456))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6456)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6457 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6457) = g32p_row31_cosetRepresentatives 6457 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6457 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6457) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6457))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6457)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6457 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6457) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6457))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6457)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6458 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6458) = g32p_row31_cosetRepresentatives 6458 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6458 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6458) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6458))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6458)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6458 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6458) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6458))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6458)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6459 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6459) = g32p_row31_cosetRepresentatives 6459 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6459 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6459) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6459))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6459)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6459 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6459) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6459))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6459)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6460 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6460) = g32p_row31_cosetRepresentatives 6460 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6460 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6460) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6460))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6460)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6460 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6460) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6460))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6460)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6461 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6461) = g32p_row31_cosetRepresentatives 6461 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6461 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6461) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6461))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6461)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6461 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6461) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6461))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6461)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6462 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6462) = g32p_row31_cosetRepresentatives 6462 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6462 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6462) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6462))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6462)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6462 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6462) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6462))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6462)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6463 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6463) = g32p_row31_cosetRepresentatives 6463 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6463 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6463) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6463))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6463)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6463 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6463) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6463))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6463)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0403 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 403 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 403 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6448
  · exact g32p_row31_cosetWord_6449
  · exact g32p_row31_cosetWord_6450
  · exact g32p_row31_cosetWord_6451
  · exact g32p_row31_cosetWord_6452
  · exact g32p_row31_cosetWord_6453
  · exact g32p_row31_cosetWord_6454
  · exact g32p_row31_cosetWord_6455
  · exact g32p_row31_cosetWord_6456
  · exact g32p_row31_cosetWord_6457
  · exact g32p_row31_cosetWord_6458
  · exact g32p_row31_cosetWord_6459
  · exact g32p_row31_cosetWord_6460
  · exact g32p_row31_cosetWord_6461
  · exact g32p_row31_cosetWord_6462
  · exact g32p_row31_cosetWord_6463

theorem g32p_row31_cosetGeneratorBlock_0403 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 403 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 403 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 403 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6448 s
  · exact g32p_row31_cosetGeneratorStep_6449 s
  · exact g32p_row31_cosetGeneratorStep_6450 s
  · exact g32p_row31_cosetGeneratorStep_6451 s
  · exact g32p_row31_cosetGeneratorStep_6452 s
  · exact g32p_row31_cosetGeneratorStep_6453 s
  · exact g32p_row31_cosetGeneratorStep_6454 s
  · exact g32p_row31_cosetGeneratorStep_6455 s
  · exact g32p_row31_cosetGeneratorStep_6456 s
  · exact g32p_row31_cosetGeneratorStep_6457 s
  · exact g32p_row31_cosetGeneratorStep_6458 s
  · exact g32p_row31_cosetGeneratorStep_6459 s
  · exact g32p_row31_cosetGeneratorStep_6460 s
  · exact g32p_row31_cosetGeneratorStep_6461 s
  · exact g32p_row31_cosetGeneratorStep_6462 s
  · exact g32p_row31_cosetGeneratorStep_6463 s

theorem g32p_row31_cosetBranchBlock_0403 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 403 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 403 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 403 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6448 s
  · exact g32p_row31_cosetBranchStep_6449 s
  · exact g32p_row31_cosetBranchStep_6450 s
  · exact g32p_row31_cosetBranchStep_6451 s
  · exact g32p_row31_cosetBranchStep_6452 s
  · exact g32p_row31_cosetBranchStep_6453 s
  · exact g32p_row31_cosetBranchStep_6454 s
  · exact g32p_row31_cosetBranchStep_6455 s
  · exact g32p_row31_cosetBranchStep_6456 s
  · exact g32p_row31_cosetBranchStep_6457 s
  · exact g32p_row31_cosetBranchStep_6458 s
  · exact g32p_row31_cosetBranchStep_6459 s
  · exact g32p_row31_cosetBranchStep_6460 s
  · exact g32p_row31_cosetBranchStep_6461 s
  · exact g32p_row31_cosetBranchStep_6462 s
  · exact g32p_row31_cosetBranchStep_6463 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6464 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6464) = g32p_row31_cosetRepresentatives 6464 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6464 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6464) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6464))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6464)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6464 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6464) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6464))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6464)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6465 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6465) = g32p_row31_cosetRepresentatives 6465 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6465 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6465) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6465))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6465)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6465 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6465) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6465))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6465)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6466 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6466) = g32p_row31_cosetRepresentatives 6466 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6466 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6466) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6466))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6466)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6466 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6466) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6466))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6466)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6467 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6467) = g32p_row31_cosetRepresentatives 6467 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6467 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6467) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6467))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6467)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6467 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6467) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6467))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6467)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6468 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6468) = g32p_row31_cosetRepresentatives 6468 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6468 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6468) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6468))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6468)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6468 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6468) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6468))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6468)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6469 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6469) = g32p_row31_cosetRepresentatives 6469 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6469 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6469) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6469))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6469)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6469 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6469) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6469))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6469)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6470 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6470) = g32p_row31_cosetRepresentatives 6470 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6470 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6470) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6470))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6470)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6470 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6470) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6470))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6470)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6471 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6471) = g32p_row31_cosetRepresentatives 6471 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6471 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6471) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6471))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6471)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6471 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6471) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6471))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6471)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6472 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6472) = g32p_row31_cosetRepresentatives 6472 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6472 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6472) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6472))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6472)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6472 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6472) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6472))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6472)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6473 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6473) = g32p_row31_cosetRepresentatives 6473 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6473 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6473) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6473))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6473)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6473 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6473) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6473))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6473)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6474 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6474) = g32p_row31_cosetRepresentatives 6474 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6474 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6474) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6474))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6474)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6474 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6474) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6474))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6474)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6475 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6475) = g32p_row31_cosetRepresentatives 6475 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6475 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6475) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6475))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6475)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6475 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6475) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6475))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6475)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6476 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6476) = g32p_row31_cosetRepresentatives 6476 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6476 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6476) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6476))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6476)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6476 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6476) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6476))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6476)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6477 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6477) = g32p_row31_cosetRepresentatives 6477 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6477 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6477) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6477))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6477)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6477 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6477) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6477))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6477)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6478 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6478) = g32p_row31_cosetRepresentatives 6478 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6478 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6478) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6478))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6478)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6478 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6478) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6478))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6478)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6479 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6479) = g32p_row31_cosetRepresentatives 6479 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6479 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6479) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6479))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6479)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6479 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6479) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6479))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6479)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0404 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 404 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 404 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6464
  · exact g32p_row31_cosetWord_6465
  · exact g32p_row31_cosetWord_6466
  · exact g32p_row31_cosetWord_6467
  · exact g32p_row31_cosetWord_6468
  · exact g32p_row31_cosetWord_6469
  · exact g32p_row31_cosetWord_6470
  · exact g32p_row31_cosetWord_6471
  · exact g32p_row31_cosetWord_6472
  · exact g32p_row31_cosetWord_6473
  · exact g32p_row31_cosetWord_6474
  · exact g32p_row31_cosetWord_6475
  · exact g32p_row31_cosetWord_6476
  · exact g32p_row31_cosetWord_6477
  · exact g32p_row31_cosetWord_6478
  · exact g32p_row31_cosetWord_6479

theorem g32p_row31_cosetGeneratorBlock_0404 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 404 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 404 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 404 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6464 s
  · exact g32p_row31_cosetGeneratorStep_6465 s
  · exact g32p_row31_cosetGeneratorStep_6466 s
  · exact g32p_row31_cosetGeneratorStep_6467 s
  · exact g32p_row31_cosetGeneratorStep_6468 s
  · exact g32p_row31_cosetGeneratorStep_6469 s
  · exact g32p_row31_cosetGeneratorStep_6470 s
  · exact g32p_row31_cosetGeneratorStep_6471 s
  · exact g32p_row31_cosetGeneratorStep_6472 s
  · exact g32p_row31_cosetGeneratorStep_6473 s
  · exact g32p_row31_cosetGeneratorStep_6474 s
  · exact g32p_row31_cosetGeneratorStep_6475 s
  · exact g32p_row31_cosetGeneratorStep_6476 s
  · exact g32p_row31_cosetGeneratorStep_6477 s
  · exact g32p_row31_cosetGeneratorStep_6478 s
  · exact g32p_row31_cosetGeneratorStep_6479 s

theorem g32p_row31_cosetBranchBlock_0404 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 404 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 404 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 404 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6464 s
  · exact g32p_row31_cosetBranchStep_6465 s
  · exact g32p_row31_cosetBranchStep_6466 s
  · exact g32p_row31_cosetBranchStep_6467 s
  · exact g32p_row31_cosetBranchStep_6468 s
  · exact g32p_row31_cosetBranchStep_6469 s
  · exact g32p_row31_cosetBranchStep_6470 s
  · exact g32p_row31_cosetBranchStep_6471 s
  · exact g32p_row31_cosetBranchStep_6472 s
  · exact g32p_row31_cosetBranchStep_6473 s
  · exact g32p_row31_cosetBranchStep_6474 s
  · exact g32p_row31_cosetBranchStep_6475 s
  · exact g32p_row31_cosetBranchStep_6476 s
  · exact g32p_row31_cosetBranchStep_6477 s
  · exact g32p_row31_cosetBranchStep_6478 s
  · exact g32p_row31_cosetBranchStep_6479 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6480 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6480) = g32p_row31_cosetRepresentatives 6480 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6480 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6480) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6480))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6480)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6480 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6480) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6480))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6480)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6481 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6481) = g32p_row31_cosetRepresentatives 6481 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6481 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6481) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6481))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6481)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6481 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6481) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6481))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6481)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6482 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6482) = g32p_row31_cosetRepresentatives 6482 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6482 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6482) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6482))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6482)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6482 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6482) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6482))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6482)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6483 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6483) = g32p_row31_cosetRepresentatives 6483 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6483 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6483) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6483))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6483)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6483 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6483) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6483))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6483)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6484 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6484) = g32p_row31_cosetRepresentatives 6484 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6484 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6484) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6484))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6484)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6484 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6484) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6484))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6484)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6485 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6485) = g32p_row31_cosetRepresentatives 6485 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6485 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6485) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6485))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6485)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6485 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6485) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6485))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6485)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6486 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6486) = g32p_row31_cosetRepresentatives 6486 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6486 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6486) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6486))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6486)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6486 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6486) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6486))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6486)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6487 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6487) = g32p_row31_cosetRepresentatives 6487 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6487 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6487) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6487))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6487)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6487 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6487) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6487))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6487)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6488 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6488) = g32p_row31_cosetRepresentatives 6488 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6488 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6488) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6488))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6488)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6488 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6488) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6488))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6488)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6489 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6489) = g32p_row31_cosetRepresentatives 6489 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6489 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6489) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6489))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6489)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6489 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6489) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6489))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6489)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6490 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6490) = g32p_row31_cosetRepresentatives 6490 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6490 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6490) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6490))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6490)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6490 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6490) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6490))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6490)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6491 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6491) = g32p_row31_cosetRepresentatives 6491 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6491 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6491) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6491))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6491)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6491 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6491) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6491))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6491)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6492 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6492) = g32p_row31_cosetRepresentatives 6492 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6492 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6492) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6492))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6492)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6492 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6492) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6492))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6492)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6493 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6493) = g32p_row31_cosetRepresentatives 6493 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6493 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6493) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6493))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6493)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6493 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6493) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6493))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6493)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6494 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6494) = g32p_row31_cosetRepresentatives 6494 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6494 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6494) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6494))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6494)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6494 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6494) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6494))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6494)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6495 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6495) = g32p_row31_cosetRepresentatives 6495 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6495 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6495) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6495))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6495)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6495 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6495) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6495))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6495)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0405 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 405 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 405 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6480
  · exact g32p_row31_cosetWord_6481
  · exact g32p_row31_cosetWord_6482
  · exact g32p_row31_cosetWord_6483
  · exact g32p_row31_cosetWord_6484
  · exact g32p_row31_cosetWord_6485
  · exact g32p_row31_cosetWord_6486
  · exact g32p_row31_cosetWord_6487
  · exact g32p_row31_cosetWord_6488
  · exact g32p_row31_cosetWord_6489
  · exact g32p_row31_cosetWord_6490
  · exact g32p_row31_cosetWord_6491
  · exact g32p_row31_cosetWord_6492
  · exact g32p_row31_cosetWord_6493
  · exact g32p_row31_cosetWord_6494
  · exact g32p_row31_cosetWord_6495

theorem g32p_row31_cosetGeneratorBlock_0405 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 405 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 405 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 405 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6480 s
  · exact g32p_row31_cosetGeneratorStep_6481 s
  · exact g32p_row31_cosetGeneratorStep_6482 s
  · exact g32p_row31_cosetGeneratorStep_6483 s
  · exact g32p_row31_cosetGeneratorStep_6484 s
  · exact g32p_row31_cosetGeneratorStep_6485 s
  · exact g32p_row31_cosetGeneratorStep_6486 s
  · exact g32p_row31_cosetGeneratorStep_6487 s
  · exact g32p_row31_cosetGeneratorStep_6488 s
  · exact g32p_row31_cosetGeneratorStep_6489 s
  · exact g32p_row31_cosetGeneratorStep_6490 s
  · exact g32p_row31_cosetGeneratorStep_6491 s
  · exact g32p_row31_cosetGeneratorStep_6492 s
  · exact g32p_row31_cosetGeneratorStep_6493 s
  · exact g32p_row31_cosetGeneratorStep_6494 s
  · exact g32p_row31_cosetGeneratorStep_6495 s

theorem g32p_row31_cosetBranchBlock_0405 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 405 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 405 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 405 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6480 s
  · exact g32p_row31_cosetBranchStep_6481 s
  · exact g32p_row31_cosetBranchStep_6482 s
  · exact g32p_row31_cosetBranchStep_6483 s
  · exact g32p_row31_cosetBranchStep_6484 s
  · exact g32p_row31_cosetBranchStep_6485 s
  · exact g32p_row31_cosetBranchStep_6486 s
  · exact g32p_row31_cosetBranchStep_6487 s
  · exact g32p_row31_cosetBranchStep_6488 s
  · exact g32p_row31_cosetBranchStep_6489 s
  · exact g32p_row31_cosetBranchStep_6490 s
  · exact g32p_row31_cosetBranchStep_6491 s
  · exact g32p_row31_cosetBranchStep_6492 s
  · exact g32p_row31_cosetBranchStep_6493 s
  · exact g32p_row31_cosetBranchStep_6494 s
  · exact g32p_row31_cosetBranchStep_6495 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6496 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6496) = g32p_row31_cosetRepresentatives 6496 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6496 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6496) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6496))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6496)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6496 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6496) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6496))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6496)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6497 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6497) = g32p_row31_cosetRepresentatives 6497 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6497 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6497) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6497))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6497)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6497 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6497) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6497))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6497)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6498 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6498) = g32p_row31_cosetRepresentatives 6498 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6498 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6498) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6498))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6498)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6498 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6498) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6498))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6498)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6499 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6499) = g32p_row31_cosetRepresentatives 6499 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6499 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6499) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6499))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6499)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6499 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6499) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6499))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6499)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6500 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6500) = g32p_row31_cosetRepresentatives 6500 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6500 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6500) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6500))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6500)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6500 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6500) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6500))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6500)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6501 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6501) = g32p_row31_cosetRepresentatives 6501 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6501 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6501) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6501))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6501)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6501 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6501) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6501))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6501)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6502 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6502) = g32p_row31_cosetRepresentatives 6502 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6502 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6502) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6502))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6502)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6502 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6502) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6502))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6502)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6503 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6503) = g32p_row31_cosetRepresentatives 6503 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6503 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6503) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6503))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6503)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6503 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6503) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6503))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6503)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6504 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6504) = g32p_row31_cosetRepresentatives 6504 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6504 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6504) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6504))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6504)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6504 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6504) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6504))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6504)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6505 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6505) = g32p_row31_cosetRepresentatives 6505 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6505 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6505) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6505))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6505)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6505 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6505) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6505))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6505)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6506 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6506) = g32p_row31_cosetRepresentatives 6506 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6506 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6506) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6506))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6506)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6506 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6506) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6506))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6506)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6507 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6507) = g32p_row31_cosetRepresentatives 6507 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6507 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6507) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6507))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6507)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6507 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6507) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6507))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6507)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6508 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6508) = g32p_row31_cosetRepresentatives 6508 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6508 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6508) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6508))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6508)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6508 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6508) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6508))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6508)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6509 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6509) = g32p_row31_cosetRepresentatives 6509 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6509 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6509) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6509))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6509)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6509 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6509) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6509))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6509)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6510 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6510) = g32p_row31_cosetRepresentatives 6510 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6510 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6510) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6510))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6510)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6510 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6510) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6510))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6510)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6511 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6511) = g32p_row31_cosetRepresentatives 6511 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6511 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6511) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6511))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6511)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6511 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6511) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6511))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6511)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0406 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 406 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 406 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6496
  · exact g32p_row31_cosetWord_6497
  · exact g32p_row31_cosetWord_6498
  · exact g32p_row31_cosetWord_6499
  · exact g32p_row31_cosetWord_6500
  · exact g32p_row31_cosetWord_6501
  · exact g32p_row31_cosetWord_6502
  · exact g32p_row31_cosetWord_6503
  · exact g32p_row31_cosetWord_6504
  · exact g32p_row31_cosetWord_6505
  · exact g32p_row31_cosetWord_6506
  · exact g32p_row31_cosetWord_6507
  · exact g32p_row31_cosetWord_6508
  · exact g32p_row31_cosetWord_6509
  · exact g32p_row31_cosetWord_6510
  · exact g32p_row31_cosetWord_6511

theorem g32p_row31_cosetGeneratorBlock_0406 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 406 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 406 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 406 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6496 s
  · exact g32p_row31_cosetGeneratorStep_6497 s
  · exact g32p_row31_cosetGeneratorStep_6498 s
  · exact g32p_row31_cosetGeneratorStep_6499 s
  · exact g32p_row31_cosetGeneratorStep_6500 s
  · exact g32p_row31_cosetGeneratorStep_6501 s
  · exact g32p_row31_cosetGeneratorStep_6502 s
  · exact g32p_row31_cosetGeneratorStep_6503 s
  · exact g32p_row31_cosetGeneratorStep_6504 s
  · exact g32p_row31_cosetGeneratorStep_6505 s
  · exact g32p_row31_cosetGeneratorStep_6506 s
  · exact g32p_row31_cosetGeneratorStep_6507 s
  · exact g32p_row31_cosetGeneratorStep_6508 s
  · exact g32p_row31_cosetGeneratorStep_6509 s
  · exact g32p_row31_cosetGeneratorStep_6510 s
  · exact g32p_row31_cosetGeneratorStep_6511 s

theorem g32p_row31_cosetBranchBlock_0406 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 406 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 406 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 406 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6496 s
  · exact g32p_row31_cosetBranchStep_6497 s
  · exact g32p_row31_cosetBranchStep_6498 s
  · exact g32p_row31_cosetBranchStep_6499 s
  · exact g32p_row31_cosetBranchStep_6500 s
  · exact g32p_row31_cosetBranchStep_6501 s
  · exact g32p_row31_cosetBranchStep_6502 s
  · exact g32p_row31_cosetBranchStep_6503 s
  · exact g32p_row31_cosetBranchStep_6504 s
  · exact g32p_row31_cosetBranchStep_6505 s
  · exact g32p_row31_cosetBranchStep_6506 s
  · exact g32p_row31_cosetBranchStep_6507 s
  · exact g32p_row31_cosetBranchStep_6508 s
  · exact g32p_row31_cosetBranchStep_6509 s
  · exact g32p_row31_cosetBranchStep_6510 s
  · exact g32p_row31_cosetBranchStep_6511 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6512 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6512) = g32p_row31_cosetRepresentatives 6512 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6512 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6512) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6512))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6512)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6512 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6512) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6512))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6512)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6513 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6513) = g32p_row31_cosetRepresentatives 6513 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6513 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6513) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6513))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6513)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6513 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6513) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6513))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6513)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6514 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6514) = g32p_row31_cosetRepresentatives 6514 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6514 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6514) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6514))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6514)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6514 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6514) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6514))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6514)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6515 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6515) = g32p_row31_cosetRepresentatives 6515 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6515 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6515) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6515))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6515)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6515 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6515) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6515))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6515)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6516 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6516) = g32p_row31_cosetRepresentatives 6516 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6516 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6516) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6516))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6516)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6516 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6516) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6516))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6516)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6517 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6517) = g32p_row31_cosetRepresentatives 6517 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6517 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6517) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6517))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6517)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6517 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6517) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6517))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6517)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6518 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6518) = g32p_row31_cosetRepresentatives 6518 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6518 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6518) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6518))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6518)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6518 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6518) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6518))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6518)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6519 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6519) = g32p_row31_cosetRepresentatives 6519 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6519 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6519) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6519))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6519)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6519 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6519) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6519))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6519)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6520 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6520) = g32p_row31_cosetRepresentatives 6520 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6520 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6520) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6520))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6520)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6520 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6520) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6520))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6520)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6521 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6521) = g32p_row31_cosetRepresentatives 6521 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6521 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6521) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6521))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6521)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6521 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6521) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6521))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6521)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6522 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6522) = g32p_row31_cosetRepresentatives 6522 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6522 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6522) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6522))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6522)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6522 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6522) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6522))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6522)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6523 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6523) = g32p_row31_cosetRepresentatives 6523 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6523 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6523) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6523))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6523)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6523 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6523) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6523))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6523)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6524 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6524) = g32p_row31_cosetRepresentatives 6524 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6524 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6524) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6524))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6524)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6524 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6524) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6524))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6524)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6525 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6525) = g32p_row31_cosetRepresentatives 6525 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6525 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6525) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6525))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6525)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6525 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6525) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6525))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6525)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6526 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6526) = g32p_row31_cosetRepresentatives 6526 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6526 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6526) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6526))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6526)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6526 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6526) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6526))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6526)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6527 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6527) = g32p_row31_cosetRepresentatives 6527 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6527 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6527) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6527))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6527)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6527 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6527) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6527))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6527)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0407 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 407 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 407 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6512
  · exact g32p_row31_cosetWord_6513
  · exact g32p_row31_cosetWord_6514
  · exact g32p_row31_cosetWord_6515
  · exact g32p_row31_cosetWord_6516
  · exact g32p_row31_cosetWord_6517
  · exact g32p_row31_cosetWord_6518
  · exact g32p_row31_cosetWord_6519
  · exact g32p_row31_cosetWord_6520
  · exact g32p_row31_cosetWord_6521
  · exact g32p_row31_cosetWord_6522
  · exact g32p_row31_cosetWord_6523
  · exact g32p_row31_cosetWord_6524
  · exact g32p_row31_cosetWord_6525
  · exact g32p_row31_cosetWord_6526
  · exact g32p_row31_cosetWord_6527

theorem g32p_row31_cosetGeneratorBlock_0407 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 407 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 407 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 407 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6512 s
  · exact g32p_row31_cosetGeneratorStep_6513 s
  · exact g32p_row31_cosetGeneratorStep_6514 s
  · exact g32p_row31_cosetGeneratorStep_6515 s
  · exact g32p_row31_cosetGeneratorStep_6516 s
  · exact g32p_row31_cosetGeneratorStep_6517 s
  · exact g32p_row31_cosetGeneratorStep_6518 s
  · exact g32p_row31_cosetGeneratorStep_6519 s
  · exact g32p_row31_cosetGeneratorStep_6520 s
  · exact g32p_row31_cosetGeneratorStep_6521 s
  · exact g32p_row31_cosetGeneratorStep_6522 s
  · exact g32p_row31_cosetGeneratorStep_6523 s
  · exact g32p_row31_cosetGeneratorStep_6524 s
  · exact g32p_row31_cosetGeneratorStep_6525 s
  · exact g32p_row31_cosetGeneratorStep_6526 s
  · exact g32p_row31_cosetGeneratorStep_6527 s

theorem g32p_row31_cosetBranchBlock_0407 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 407 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 407 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 407 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6512 s
  · exact g32p_row31_cosetBranchStep_6513 s
  · exact g32p_row31_cosetBranchStep_6514 s
  · exact g32p_row31_cosetBranchStep_6515 s
  · exact g32p_row31_cosetBranchStep_6516 s
  · exact g32p_row31_cosetBranchStep_6517 s
  · exact g32p_row31_cosetBranchStep_6518 s
  · exact g32p_row31_cosetBranchStep_6519 s
  · exact g32p_row31_cosetBranchStep_6520 s
  · exact g32p_row31_cosetBranchStep_6521 s
  · exact g32p_row31_cosetBranchStep_6522 s
  · exact g32p_row31_cosetBranchStep_6523 s
  · exact g32p_row31_cosetBranchStep_6524 s
  · exact g32p_row31_cosetBranchStep_6525 s
  · exact g32p_row31_cosetBranchStep_6526 s
  · exact g32p_row31_cosetBranchStep_6527 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6528 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6528) = g32p_row31_cosetRepresentatives 6528 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6528 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6528) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6528))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6528)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6528 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6528) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6528))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6528)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6529 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6529) = g32p_row31_cosetRepresentatives 6529 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6529 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6529) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6529))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6529)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6529 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6529) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6529))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6529)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6530 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6530) = g32p_row31_cosetRepresentatives 6530 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6530 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6530) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6530))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6530)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6530 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6530) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6530))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6530)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6531 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6531) = g32p_row31_cosetRepresentatives 6531 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6531 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6531) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6531))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6531)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6531 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6531) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6531))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6531)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6532 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6532) = g32p_row31_cosetRepresentatives 6532 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6532 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6532) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6532))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6532)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6532 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6532) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6532))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6532)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6533 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6533) = g32p_row31_cosetRepresentatives 6533 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6533 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6533) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6533))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6533)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6533 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6533) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6533))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6533)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6534 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6534) = g32p_row31_cosetRepresentatives 6534 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6534 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6534) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6534))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6534)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6534 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6534) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6534))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6534)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6535 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6535) = g32p_row31_cosetRepresentatives 6535 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6535 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6535) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6535))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6535)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6535 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6535) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6535))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6535)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6536 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6536) = g32p_row31_cosetRepresentatives 6536 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6536 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6536) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6536))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6536)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6536 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6536) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6536))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6536)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6537 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6537) = g32p_row31_cosetRepresentatives 6537 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6537 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6537) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6537))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6537)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6537 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6537) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6537))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6537)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6538 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6538) = g32p_row31_cosetRepresentatives 6538 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6538 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6538) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6538))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6538)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6538 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6538) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6538))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6538)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6539 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6539) = g32p_row31_cosetRepresentatives 6539 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6539 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6539) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6539))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6539)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6539 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6539) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6539))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6539)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6540 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6540) = g32p_row31_cosetRepresentatives 6540 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6540 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6540) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6540))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6540)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6540 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6540) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6540))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6540)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6541 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6541) = g32p_row31_cosetRepresentatives 6541 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6541 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6541) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6541))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6541)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6541 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6541) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6541))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6541)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6542 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6542) = g32p_row31_cosetRepresentatives 6542 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6542 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6542) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6542))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6542)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6542 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6542) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6542))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6542)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6543 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6543) = g32p_row31_cosetRepresentatives 6543 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6543 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6543) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6543))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6543)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6543 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6543) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6543))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6543)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0408 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 408 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 408 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6528
  · exact g32p_row31_cosetWord_6529
  · exact g32p_row31_cosetWord_6530
  · exact g32p_row31_cosetWord_6531
  · exact g32p_row31_cosetWord_6532
  · exact g32p_row31_cosetWord_6533
  · exact g32p_row31_cosetWord_6534
  · exact g32p_row31_cosetWord_6535
  · exact g32p_row31_cosetWord_6536
  · exact g32p_row31_cosetWord_6537
  · exact g32p_row31_cosetWord_6538
  · exact g32p_row31_cosetWord_6539
  · exact g32p_row31_cosetWord_6540
  · exact g32p_row31_cosetWord_6541
  · exact g32p_row31_cosetWord_6542
  · exact g32p_row31_cosetWord_6543

theorem g32p_row31_cosetGeneratorBlock_0408 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 408 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 408 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 408 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6528 s
  · exact g32p_row31_cosetGeneratorStep_6529 s
  · exact g32p_row31_cosetGeneratorStep_6530 s
  · exact g32p_row31_cosetGeneratorStep_6531 s
  · exact g32p_row31_cosetGeneratorStep_6532 s
  · exact g32p_row31_cosetGeneratorStep_6533 s
  · exact g32p_row31_cosetGeneratorStep_6534 s
  · exact g32p_row31_cosetGeneratorStep_6535 s
  · exact g32p_row31_cosetGeneratorStep_6536 s
  · exact g32p_row31_cosetGeneratorStep_6537 s
  · exact g32p_row31_cosetGeneratorStep_6538 s
  · exact g32p_row31_cosetGeneratorStep_6539 s
  · exact g32p_row31_cosetGeneratorStep_6540 s
  · exact g32p_row31_cosetGeneratorStep_6541 s
  · exact g32p_row31_cosetGeneratorStep_6542 s
  · exact g32p_row31_cosetGeneratorStep_6543 s

theorem g32p_row31_cosetBranchBlock_0408 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 408 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 408 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 408 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6528 s
  · exact g32p_row31_cosetBranchStep_6529 s
  · exact g32p_row31_cosetBranchStep_6530 s
  · exact g32p_row31_cosetBranchStep_6531 s
  · exact g32p_row31_cosetBranchStep_6532 s
  · exact g32p_row31_cosetBranchStep_6533 s
  · exact g32p_row31_cosetBranchStep_6534 s
  · exact g32p_row31_cosetBranchStep_6535 s
  · exact g32p_row31_cosetBranchStep_6536 s
  · exact g32p_row31_cosetBranchStep_6537 s
  · exact g32p_row31_cosetBranchStep_6538 s
  · exact g32p_row31_cosetBranchStep_6539 s
  · exact g32p_row31_cosetBranchStep_6540 s
  · exact g32p_row31_cosetBranchStep_6541 s
  · exact g32p_row31_cosetBranchStep_6542 s
  · exact g32p_row31_cosetBranchStep_6543 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6544 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6544) = g32p_row31_cosetRepresentatives 6544 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6544 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6544) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6544))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6544)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6544 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6544) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6544))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6544)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6545 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6545) = g32p_row31_cosetRepresentatives 6545 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6545 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6545) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6545))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6545)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6545 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6545) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6545))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6545)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6546 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6546) = g32p_row31_cosetRepresentatives 6546 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6546 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6546) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6546))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6546)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6546 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6546) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6546))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6546)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6547 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6547) = g32p_row31_cosetRepresentatives 6547 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6547 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6547) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6547))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6547)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6547 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6547) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6547))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6547)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6548 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6548) = g32p_row31_cosetRepresentatives 6548 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6548 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6548) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6548))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6548)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6548 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6548) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6548))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6548)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6549 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6549) = g32p_row31_cosetRepresentatives 6549 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6549 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6549) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6549))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6549)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6549 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6549) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6549))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6549)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6550 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6550) = g32p_row31_cosetRepresentatives 6550 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6550 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6550) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6550))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6550)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6550 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6550) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6550))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6550)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6551 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6551) = g32p_row31_cosetRepresentatives 6551 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6551 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6551) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6551))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6551)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6551 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6551) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6551))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6551)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6552 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6552) = g32p_row31_cosetRepresentatives 6552 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6552 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6552) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6552))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6552)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6552 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6552) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6552))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6552)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6553 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6553) = g32p_row31_cosetRepresentatives 6553 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6553 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6553) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6553))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6553)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6553 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6553) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6553))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6553)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6554 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6554) = g32p_row31_cosetRepresentatives 6554 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6554 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6554) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6554))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6554)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6554 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6554) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6554))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6554)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6555 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6555) = g32p_row31_cosetRepresentatives 6555 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6555 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6555) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6555))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6555)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6555 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6555) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6555))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6555)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6556 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6556) = g32p_row31_cosetRepresentatives 6556 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6556 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6556) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6556))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6556)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6556 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6556) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6556))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6556)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6557 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6557) = g32p_row31_cosetRepresentatives 6557 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6557 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6557) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6557))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6557)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6557 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6557) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6557))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6557)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6558 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6558) = g32p_row31_cosetRepresentatives 6558 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6558 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6558) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6558))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6558)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6558 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6558) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6558))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6558)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6559 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6559) = g32p_row31_cosetRepresentatives 6559 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6559 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6559) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6559))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6559)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6559 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6559) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6559))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6559)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0409 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 409 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 409 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6544
  · exact g32p_row31_cosetWord_6545
  · exact g32p_row31_cosetWord_6546
  · exact g32p_row31_cosetWord_6547
  · exact g32p_row31_cosetWord_6548
  · exact g32p_row31_cosetWord_6549
  · exact g32p_row31_cosetWord_6550
  · exact g32p_row31_cosetWord_6551
  · exact g32p_row31_cosetWord_6552
  · exact g32p_row31_cosetWord_6553
  · exact g32p_row31_cosetWord_6554
  · exact g32p_row31_cosetWord_6555
  · exact g32p_row31_cosetWord_6556
  · exact g32p_row31_cosetWord_6557
  · exact g32p_row31_cosetWord_6558
  · exact g32p_row31_cosetWord_6559

theorem g32p_row31_cosetGeneratorBlock_0409 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 409 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 409 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 409 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6544 s
  · exact g32p_row31_cosetGeneratorStep_6545 s
  · exact g32p_row31_cosetGeneratorStep_6546 s
  · exact g32p_row31_cosetGeneratorStep_6547 s
  · exact g32p_row31_cosetGeneratorStep_6548 s
  · exact g32p_row31_cosetGeneratorStep_6549 s
  · exact g32p_row31_cosetGeneratorStep_6550 s
  · exact g32p_row31_cosetGeneratorStep_6551 s
  · exact g32p_row31_cosetGeneratorStep_6552 s
  · exact g32p_row31_cosetGeneratorStep_6553 s
  · exact g32p_row31_cosetGeneratorStep_6554 s
  · exact g32p_row31_cosetGeneratorStep_6555 s
  · exact g32p_row31_cosetGeneratorStep_6556 s
  · exact g32p_row31_cosetGeneratorStep_6557 s
  · exact g32p_row31_cosetGeneratorStep_6558 s
  · exact g32p_row31_cosetGeneratorStep_6559 s

theorem g32p_row31_cosetBranchBlock_0409 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 409 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 409 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 409 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6544 s
  · exact g32p_row31_cosetBranchStep_6545 s
  · exact g32p_row31_cosetBranchStep_6546 s
  · exact g32p_row31_cosetBranchStep_6547 s
  · exact g32p_row31_cosetBranchStep_6548 s
  · exact g32p_row31_cosetBranchStep_6549 s
  · exact g32p_row31_cosetBranchStep_6550 s
  · exact g32p_row31_cosetBranchStep_6551 s
  · exact g32p_row31_cosetBranchStep_6552 s
  · exact g32p_row31_cosetBranchStep_6553 s
  · exact g32p_row31_cosetBranchStep_6554 s
  · exact g32p_row31_cosetBranchStep_6555 s
  · exact g32p_row31_cosetBranchStep_6556 s
  · exact g32p_row31_cosetBranchStep_6557 s
  · exact g32p_row31_cosetBranchStep_6558 s
  · exact g32p_row31_cosetBranchStep_6559 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6560 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6560) = g32p_row31_cosetRepresentatives 6560 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6560 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6560) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6560))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6560)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6560 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6560) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6560))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6560)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6561 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6561) = g32p_row31_cosetRepresentatives 6561 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6561 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6561) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6561))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6561)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6561 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6561) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6561))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6561)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6562 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6562) = g32p_row31_cosetRepresentatives 6562 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6562 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6562) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6562))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6562)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6562 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6562) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6562))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6562)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6563 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6563) = g32p_row31_cosetRepresentatives 6563 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6563 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6563) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6563))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6563)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6563 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6563) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6563))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6563)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6564 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6564) = g32p_row31_cosetRepresentatives 6564 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6564 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6564) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6564))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6564)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6564 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6564) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6564))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6564)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6565 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6565) = g32p_row31_cosetRepresentatives 6565 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6565 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6565) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6565))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6565)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6565 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6565) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6565))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6565)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6566 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6566) = g32p_row31_cosetRepresentatives 6566 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6566 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6566) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6566))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6566)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6566 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6566) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6566))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6566)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6567 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6567) = g32p_row31_cosetRepresentatives 6567 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6567 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6567) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6567))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6567)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6567 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6567) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6567))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6567)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6568 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6568) = g32p_row31_cosetRepresentatives 6568 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6568 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6568) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6568))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6568)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6568 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6568) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6568))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6568)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6569 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6569) = g32p_row31_cosetRepresentatives 6569 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6569 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6569) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6569))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6569)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6569 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6569) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6569))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6569)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6570 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6570) = g32p_row31_cosetRepresentatives 6570 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6570 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6570) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6570))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6570)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6570 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6570) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6570))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6570)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6571 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6571) = g32p_row31_cosetRepresentatives 6571 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6571 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6571) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6571))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6571)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6571 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6571) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6571))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6571)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6572 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6572) = g32p_row31_cosetRepresentatives 6572 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6572 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6572) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6572))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6572)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6572 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6572) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6572))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6572)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6573 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6573) = g32p_row31_cosetRepresentatives 6573 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6573 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6573) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6573))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6573)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6573 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6573) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6573))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6573)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6574 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6574) = g32p_row31_cosetRepresentatives 6574 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6574 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6574) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6574))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6574)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6574 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6574) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6574))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6574)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6575 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6575) = g32p_row31_cosetRepresentatives 6575 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6575 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6575) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6575))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6575)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6575 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6575) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6575))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6575)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0410 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 410 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 410 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6560
  · exact g32p_row31_cosetWord_6561
  · exact g32p_row31_cosetWord_6562
  · exact g32p_row31_cosetWord_6563
  · exact g32p_row31_cosetWord_6564
  · exact g32p_row31_cosetWord_6565
  · exact g32p_row31_cosetWord_6566
  · exact g32p_row31_cosetWord_6567
  · exact g32p_row31_cosetWord_6568
  · exact g32p_row31_cosetWord_6569
  · exact g32p_row31_cosetWord_6570
  · exact g32p_row31_cosetWord_6571
  · exact g32p_row31_cosetWord_6572
  · exact g32p_row31_cosetWord_6573
  · exact g32p_row31_cosetWord_6574
  · exact g32p_row31_cosetWord_6575

theorem g32p_row31_cosetGeneratorBlock_0410 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 410 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 410 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 410 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6560 s
  · exact g32p_row31_cosetGeneratorStep_6561 s
  · exact g32p_row31_cosetGeneratorStep_6562 s
  · exact g32p_row31_cosetGeneratorStep_6563 s
  · exact g32p_row31_cosetGeneratorStep_6564 s
  · exact g32p_row31_cosetGeneratorStep_6565 s
  · exact g32p_row31_cosetGeneratorStep_6566 s
  · exact g32p_row31_cosetGeneratorStep_6567 s
  · exact g32p_row31_cosetGeneratorStep_6568 s
  · exact g32p_row31_cosetGeneratorStep_6569 s
  · exact g32p_row31_cosetGeneratorStep_6570 s
  · exact g32p_row31_cosetGeneratorStep_6571 s
  · exact g32p_row31_cosetGeneratorStep_6572 s
  · exact g32p_row31_cosetGeneratorStep_6573 s
  · exact g32p_row31_cosetGeneratorStep_6574 s
  · exact g32p_row31_cosetGeneratorStep_6575 s

theorem g32p_row31_cosetBranchBlock_0410 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 410 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 410 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 410 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6560 s
  · exact g32p_row31_cosetBranchStep_6561 s
  · exact g32p_row31_cosetBranchStep_6562 s
  · exact g32p_row31_cosetBranchStep_6563 s
  · exact g32p_row31_cosetBranchStep_6564 s
  · exact g32p_row31_cosetBranchStep_6565 s
  · exact g32p_row31_cosetBranchStep_6566 s
  · exact g32p_row31_cosetBranchStep_6567 s
  · exact g32p_row31_cosetBranchStep_6568 s
  · exact g32p_row31_cosetBranchStep_6569 s
  · exact g32p_row31_cosetBranchStep_6570 s
  · exact g32p_row31_cosetBranchStep_6571 s
  · exact g32p_row31_cosetBranchStep_6572 s
  · exact g32p_row31_cosetBranchStep_6573 s
  · exact g32p_row31_cosetBranchStep_6574 s
  · exact g32p_row31_cosetBranchStep_6575 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6576 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6576) = g32p_row31_cosetRepresentatives 6576 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6576 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6576) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6576))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6576)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6576 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6576) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6576))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6576)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6577 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6577) = g32p_row31_cosetRepresentatives 6577 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6577 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6577) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6577))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6577)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6577 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6577) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6577))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6577)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6578 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6578) = g32p_row31_cosetRepresentatives 6578 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6578 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6578) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6578))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6578)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6578 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6578) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6578))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6578)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6579 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6579) = g32p_row31_cosetRepresentatives 6579 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6579 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6579) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6579))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6579)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6579 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6579) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6579))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6579)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6580 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6580) = g32p_row31_cosetRepresentatives 6580 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6580 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6580) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6580))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6580)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6580 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6580) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6580))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6580)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6581 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6581) = g32p_row31_cosetRepresentatives 6581 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6581 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6581) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6581))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6581)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6581 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6581) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6581))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6581)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6582 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6582) = g32p_row31_cosetRepresentatives 6582 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6582 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6582) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6582))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6582)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6582 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6582) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6582))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6582)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6583 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6583) = g32p_row31_cosetRepresentatives 6583 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6583 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6583) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6583))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6583)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6583 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6583) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6583))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6583)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6584 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6584) = g32p_row31_cosetRepresentatives 6584 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6584 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6584) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6584))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6584)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6584 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6584) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6584))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6584)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6585 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6585) = g32p_row31_cosetRepresentatives 6585 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6585 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6585) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6585))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6585)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6585 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6585) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6585))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6585)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6586 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6586) = g32p_row31_cosetRepresentatives 6586 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6586 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6586) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6586))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6586)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6586 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6586) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6586))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6586)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6587 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6587) = g32p_row31_cosetRepresentatives 6587 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6587 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6587) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6587))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6587)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6587 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6587) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6587))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6587)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6588 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6588) = g32p_row31_cosetRepresentatives 6588 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6588 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6588) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6588))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6588)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6588 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6588) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6588))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6588)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6589 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6589) = g32p_row31_cosetRepresentatives 6589 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6589 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6589) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6589))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6589)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6589 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6589) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6589))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6589)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6590 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6590) = g32p_row31_cosetRepresentatives 6590 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6590 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6590) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6590))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6590)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6590 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6590) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6590))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6590)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6591 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6591) = g32p_row31_cosetRepresentatives 6591 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6591 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6591) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6591))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6591)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6591 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6591) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6591))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6591)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0411 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 411 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 411 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6576
  · exact g32p_row31_cosetWord_6577
  · exact g32p_row31_cosetWord_6578
  · exact g32p_row31_cosetWord_6579
  · exact g32p_row31_cosetWord_6580
  · exact g32p_row31_cosetWord_6581
  · exact g32p_row31_cosetWord_6582
  · exact g32p_row31_cosetWord_6583
  · exact g32p_row31_cosetWord_6584
  · exact g32p_row31_cosetWord_6585
  · exact g32p_row31_cosetWord_6586
  · exact g32p_row31_cosetWord_6587
  · exact g32p_row31_cosetWord_6588
  · exact g32p_row31_cosetWord_6589
  · exact g32p_row31_cosetWord_6590
  · exact g32p_row31_cosetWord_6591

theorem g32p_row31_cosetGeneratorBlock_0411 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 411 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 411 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 411 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6576 s
  · exact g32p_row31_cosetGeneratorStep_6577 s
  · exact g32p_row31_cosetGeneratorStep_6578 s
  · exact g32p_row31_cosetGeneratorStep_6579 s
  · exact g32p_row31_cosetGeneratorStep_6580 s
  · exact g32p_row31_cosetGeneratorStep_6581 s
  · exact g32p_row31_cosetGeneratorStep_6582 s
  · exact g32p_row31_cosetGeneratorStep_6583 s
  · exact g32p_row31_cosetGeneratorStep_6584 s
  · exact g32p_row31_cosetGeneratorStep_6585 s
  · exact g32p_row31_cosetGeneratorStep_6586 s
  · exact g32p_row31_cosetGeneratorStep_6587 s
  · exact g32p_row31_cosetGeneratorStep_6588 s
  · exact g32p_row31_cosetGeneratorStep_6589 s
  · exact g32p_row31_cosetGeneratorStep_6590 s
  · exact g32p_row31_cosetGeneratorStep_6591 s

theorem g32p_row31_cosetBranchBlock_0411 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 411 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 411 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 411 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6576 s
  · exact g32p_row31_cosetBranchStep_6577 s
  · exact g32p_row31_cosetBranchStep_6578 s
  · exact g32p_row31_cosetBranchStep_6579 s
  · exact g32p_row31_cosetBranchStep_6580 s
  · exact g32p_row31_cosetBranchStep_6581 s
  · exact g32p_row31_cosetBranchStep_6582 s
  · exact g32p_row31_cosetBranchStep_6583 s
  · exact g32p_row31_cosetBranchStep_6584 s
  · exact g32p_row31_cosetBranchStep_6585 s
  · exact g32p_row31_cosetBranchStep_6586 s
  · exact g32p_row31_cosetBranchStep_6587 s
  · exact g32p_row31_cosetBranchStep_6588 s
  · exact g32p_row31_cosetBranchStep_6589 s
  · exact g32p_row31_cosetBranchStep_6590 s
  · exact g32p_row31_cosetBranchStep_6591 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6592 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6592) = g32p_row31_cosetRepresentatives 6592 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6592 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6592) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6592))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6592)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6592 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6592) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6592))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6592)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6593 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6593) = g32p_row31_cosetRepresentatives 6593 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6593 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6593) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6593))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6593)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6593 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6593) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6593))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6593)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6594 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6594) = g32p_row31_cosetRepresentatives 6594 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6594 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6594) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6594))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6594)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6594 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6594) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6594))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6594)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6595 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6595) = g32p_row31_cosetRepresentatives 6595 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6595 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6595) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6595))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6595)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6595 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6595) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6595))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6595)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6596 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6596) = g32p_row31_cosetRepresentatives 6596 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6596 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6596) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6596))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6596)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6596 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6596) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6596))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6596)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6597 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6597) = g32p_row31_cosetRepresentatives 6597 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6597 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6597) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6597))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6597)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6597 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6597) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6597))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6597)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6598 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6598) = g32p_row31_cosetRepresentatives 6598 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6598 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6598) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6598))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6598)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6598 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6598) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6598))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6598)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6599 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6599) = g32p_row31_cosetRepresentatives 6599 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6599 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6599) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6599))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6599)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6599 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6599) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6599))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6599)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6600 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6600) = g32p_row31_cosetRepresentatives 6600 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6600 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6600) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6600))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6600)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6600 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6600) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6600))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6600)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6601 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6601) = g32p_row31_cosetRepresentatives 6601 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6601 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6601) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6601))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6601)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6601 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6601) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6601))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6601)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6602 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6602) = g32p_row31_cosetRepresentatives 6602 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6602 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6602) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6602))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6602)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6602 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6602) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6602))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6602)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6603 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6603) = g32p_row31_cosetRepresentatives 6603 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6603 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6603) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6603))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6603)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6603 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6603) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6603))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6603)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6604 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6604) = g32p_row31_cosetRepresentatives 6604 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6604 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6604) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6604))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6604)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6604 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6604) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6604))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6604)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6605 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6605) = g32p_row31_cosetRepresentatives 6605 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6605 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6605) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6605))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6605)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6605 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6605) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6605))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6605)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6606 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6606) = g32p_row31_cosetRepresentatives 6606 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6606 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6606) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6606))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6606)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6606 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6606) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6606))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6606)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6607 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6607) = g32p_row31_cosetRepresentatives 6607 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6607 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6607) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6607))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6607)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6607 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6607) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6607))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6607)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0412 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 412 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 412 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6592
  · exact g32p_row31_cosetWord_6593
  · exact g32p_row31_cosetWord_6594
  · exact g32p_row31_cosetWord_6595
  · exact g32p_row31_cosetWord_6596
  · exact g32p_row31_cosetWord_6597
  · exact g32p_row31_cosetWord_6598
  · exact g32p_row31_cosetWord_6599
  · exact g32p_row31_cosetWord_6600
  · exact g32p_row31_cosetWord_6601
  · exact g32p_row31_cosetWord_6602
  · exact g32p_row31_cosetWord_6603
  · exact g32p_row31_cosetWord_6604
  · exact g32p_row31_cosetWord_6605
  · exact g32p_row31_cosetWord_6606
  · exact g32p_row31_cosetWord_6607

theorem g32p_row31_cosetGeneratorBlock_0412 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 412 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 412 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 412 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6592 s
  · exact g32p_row31_cosetGeneratorStep_6593 s
  · exact g32p_row31_cosetGeneratorStep_6594 s
  · exact g32p_row31_cosetGeneratorStep_6595 s
  · exact g32p_row31_cosetGeneratorStep_6596 s
  · exact g32p_row31_cosetGeneratorStep_6597 s
  · exact g32p_row31_cosetGeneratorStep_6598 s
  · exact g32p_row31_cosetGeneratorStep_6599 s
  · exact g32p_row31_cosetGeneratorStep_6600 s
  · exact g32p_row31_cosetGeneratorStep_6601 s
  · exact g32p_row31_cosetGeneratorStep_6602 s
  · exact g32p_row31_cosetGeneratorStep_6603 s
  · exact g32p_row31_cosetGeneratorStep_6604 s
  · exact g32p_row31_cosetGeneratorStep_6605 s
  · exact g32p_row31_cosetGeneratorStep_6606 s
  · exact g32p_row31_cosetGeneratorStep_6607 s

theorem g32p_row31_cosetBranchBlock_0412 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 412 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 412 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 412 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6592 s
  · exact g32p_row31_cosetBranchStep_6593 s
  · exact g32p_row31_cosetBranchStep_6594 s
  · exact g32p_row31_cosetBranchStep_6595 s
  · exact g32p_row31_cosetBranchStep_6596 s
  · exact g32p_row31_cosetBranchStep_6597 s
  · exact g32p_row31_cosetBranchStep_6598 s
  · exact g32p_row31_cosetBranchStep_6599 s
  · exact g32p_row31_cosetBranchStep_6600 s
  · exact g32p_row31_cosetBranchStep_6601 s
  · exact g32p_row31_cosetBranchStep_6602 s
  · exact g32p_row31_cosetBranchStep_6603 s
  · exact g32p_row31_cosetBranchStep_6604 s
  · exact g32p_row31_cosetBranchStep_6605 s
  · exact g32p_row31_cosetBranchStep_6606 s
  · exact g32p_row31_cosetBranchStep_6607 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6608 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6608) = g32p_row31_cosetRepresentatives 6608 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6608 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6608) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6608))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6608)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6608 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6608) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6608))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6608)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6609 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6609) = g32p_row31_cosetRepresentatives 6609 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6609 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6609) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6609))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6609)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6609 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6609) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6609))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6609)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6610 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6610) = g32p_row31_cosetRepresentatives 6610 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6610 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6610) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6610))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6610)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6610 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6610) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6610))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6610)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6611 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6611) = g32p_row31_cosetRepresentatives 6611 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6611 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6611) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6611))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6611)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6611 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6611) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6611))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6611)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6612 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6612) = g32p_row31_cosetRepresentatives 6612 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6612 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6612) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6612))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6612)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6612 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6612) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6612))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6612)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6613 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6613) = g32p_row31_cosetRepresentatives 6613 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6613 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6613) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6613))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6613)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6613 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6613) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6613))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6613)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6614 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6614) = g32p_row31_cosetRepresentatives 6614 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6614 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6614) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6614))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6614)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6614 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6614) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6614))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6614)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6615 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6615) = g32p_row31_cosetRepresentatives 6615 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6615 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6615) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6615))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6615)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6615 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6615) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6615))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6615)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6616 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6616) = g32p_row31_cosetRepresentatives 6616 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6616 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6616) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6616))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6616)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6616 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6616) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6616))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6616)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6617 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6617) = g32p_row31_cosetRepresentatives 6617 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6617 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6617) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6617))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6617)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6617 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6617) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6617))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6617)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6618 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6618) = g32p_row31_cosetRepresentatives 6618 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6618 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6618) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6618))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6618)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6618 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6618) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6618))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6618)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6619 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6619) = g32p_row31_cosetRepresentatives 6619 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6619 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6619) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6619))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6619)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6619 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6619) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6619))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6619)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6620 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6620) = g32p_row31_cosetRepresentatives 6620 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6620 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6620) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6620))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6620)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6620 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6620) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6620))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6620)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6621 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6621) = g32p_row31_cosetRepresentatives 6621 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6621 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6621) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6621))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6621)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6621 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6621) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6621))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6621)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6622 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6622) = g32p_row31_cosetRepresentatives 6622 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6622 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6622) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6622))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6622)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6622 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6622) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6622))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6622)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6623 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6623) = g32p_row31_cosetRepresentatives 6623 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6623 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6623) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6623))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6623)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6623 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6623) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6623))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6623)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0413 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 413 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 413 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6608
  · exact g32p_row31_cosetWord_6609
  · exact g32p_row31_cosetWord_6610
  · exact g32p_row31_cosetWord_6611
  · exact g32p_row31_cosetWord_6612
  · exact g32p_row31_cosetWord_6613
  · exact g32p_row31_cosetWord_6614
  · exact g32p_row31_cosetWord_6615
  · exact g32p_row31_cosetWord_6616
  · exact g32p_row31_cosetWord_6617
  · exact g32p_row31_cosetWord_6618
  · exact g32p_row31_cosetWord_6619
  · exact g32p_row31_cosetWord_6620
  · exact g32p_row31_cosetWord_6621
  · exact g32p_row31_cosetWord_6622
  · exact g32p_row31_cosetWord_6623

theorem g32p_row31_cosetGeneratorBlock_0413 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 413 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 413 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 413 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6608 s
  · exact g32p_row31_cosetGeneratorStep_6609 s
  · exact g32p_row31_cosetGeneratorStep_6610 s
  · exact g32p_row31_cosetGeneratorStep_6611 s
  · exact g32p_row31_cosetGeneratorStep_6612 s
  · exact g32p_row31_cosetGeneratorStep_6613 s
  · exact g32p_row31_cosetGeneratorStep_6614 s
  · exact g32p_row31_cosetGeneratorStep_6615 s
  · exact g32p_row31_cosetGeneratorStep_6616 s
  · exact g32p_row31_cosetGeneratorStep_6617 s
  · exact g32p_row31_cosetGeneratorStep_6618 s
  · exact g32p_row31_cosetGeneratorStep_6619 s
  · exact g32p_row31_cosetGeneratorStep_6620 s
  · exact g32p_row31_cosetGeneratorStep_6621 s
  · exact g32p_row31_cosetGeneratorStep_6622 s
  · exact g32p_row31_cosetGeneratorStep_6623 s

theorem g32p_row31_cosetBranchBlock_0413 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 413 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 413 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 413 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6608 s
  · exact g32p_row31_cosetBranchStep_6609 s
  · exact g32p_row31_cosetBranchStep_6610 s
  · exact g32p_row31_cosetBranchStep_6611 s
  · exact g32p_row31_cosetBranchStep_6612 s
  · exact g32p_row31_cosetBranchStep_6613 s
  · exact g32p_row31_cosetBranchStep_6614 s
  · exact g32p_row31_cosetBranchStep_6615 s
  · exact g32p_row31_cosetBranchStep_6616 s
  · exact g32p_row31_cosetBranchStep_6617 s
  · exact g32p_row31_cosetBranchStep_6618 s
  · exact g32p_row31_cosetBranchStep_6619 s
  · exact g32p_row31_cosetBranchStep_6620 s
  · exact g32p_row31_cosetBranchStep_6621 s
  · exact g32p_row31_cosetBranchStep_6622 s
  · exact g32p_row31_cosetBranchStep_6623 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6624 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6624) = g32p_row31_cosetRepresentatives 6624 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6624 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6624) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6624))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6624)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6624 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6624) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6624))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6624)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6625 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6625) = g32p_row31_cosetRepresentatives 6625 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6625 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6625) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6625))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6625)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6625 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6625) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6625))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6625)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6626 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6626) = g32p_row31_cosetRepresentatives 6626 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6626 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6626) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6626))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6626)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6626 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6626) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6626))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6626)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6627 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6627) = g32p_row31_cosetRepresentatives 6627 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6627 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6627) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6627))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6627)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6627 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6627) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6627))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6627)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6628 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6628) = g32p_row31_cosetRepresentatives 6628 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6628 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6628) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6628))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6628)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6628 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6628) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6628))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6628)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6629 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6629) = g32p_row31_cosetRepresentatives 6629 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6629 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6629) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6629))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6629)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6629 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6629) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6629))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6629)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6630 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6630) = g32p_row31_cosetRepresentatives 6630 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6630 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6630) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6630))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6630)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6630 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6630) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6630))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6630)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6631 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6631) = g32p_row31_cosetRepresentatives 6631 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6631 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6631) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6631))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6631)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6631 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6631) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6631))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6631)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6632 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6632) = g32p_row31_cosetRepresentatives 6632 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6632 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6632) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6632))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6632)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6632 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6632) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6632))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6632)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6633 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6633) = g32p_row31_cosetRepresentatives 6633 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6633 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6633) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6633))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6633)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6633 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6633) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6633))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6633)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6634 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6634) = g32p_row31_cosetRepresentatives 6634 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6634 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6634) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6634))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6634)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6634 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6634) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6634))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6634)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6635 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6635) = g32p_row31_cosetRepresentatives 6635 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6635 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6635) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6635))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6635)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6635 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6635) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6635))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6635)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6636 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6636) = g32p_row31_cosetRepresentatives 6636 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6636 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6636) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6636))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6636)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6636 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6636) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6636))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6636)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6637 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6637) = g32p_row31_cosetRepresentatives 6637 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6637 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6637) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6637))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6637)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6637 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6637) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6637))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6637)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6638 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6638) = g32p_row31_cosetRepresentatives 6638 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6638 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6638) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6638))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6638)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6638 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6638) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6638))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6638)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6639 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6639) = g32p_row31_cosetRepresentatives 6639 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6639 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6639) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6639))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6639)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6639 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6639) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6639))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6639)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0414 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 414 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 414 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6624
  · exact g32p_row31_cosetWord_6625
  · exact g32p_row31_cosetWord_6626
  · exact g32p_row31_cosetWord_6627
  · exact g32p_row31_cosetWord_6628
  · exact g32p_row31_cosetWord_6629
  · exact g32p_row31_cosetWord_6630
  · exact g32p_row31_cosetWord_6631
  · exact g32p_row31_cosetWord_6632
  · exact g32p_row31_cosetWord_6633
  · exact g32p_row31_cosetWord_6634
  · exact g32p_row31_cosetWord_6635
  · exact g32p_row31_cosetWord_6636
  · exact g32p_row31_cosetWord_6637
  · exact g32p_row31_cosetWord_6638
  · exact g32p_row31_cosetWord_6639

theorem g32p_row31_cosetGeneratorBlock_0414 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 414 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 414 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 414 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6624 s
  · exact g32p_row31_cosetGeneratorStep_6625 s
  · exact g32p_row31_cosetGeneratorStep_6626 s
  · exact g32p_row31_cosetGeneratorStep_6627 s
  · exact g32p_row31_cosetGeneratorStep_6628 s
  · exact g32p_row31_cosetGeneratorStep_6629 s
  · exact g32p_row31_cosetGeneratorStep_6630 s
  · exact g32p_row31_cosetGeneratorStep_6631 s
  · exact g32p_row31_cosetGeneratorStep_6632 s
  · exact g32p_row31_cosetGeneratorStep_6633 s
  · exact g32p_row31_cosetGeneratorStep_6634 s
  · exact g32p_row31_cosetGeneratorStep_6635 s
  · exact g32p_row31_cosetGeneratorStep_6636 s
  · exact g32p_row31_cosetGeneratorStep_6637 s
  · exact g32p_row31_cosetGeneratorStep_6638 s
  · exact g32p_row31_cosetGeneratorStep_6639 s

theorem g32p_row31_cosetBranchBlock_0414 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 414 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 414 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 414 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6624 s
  · exact g32p_row31_cosetBranchStep_6625 s
  · exact g32p_row31_cosetBranchStep_6626 s
  · exact g32p_row31_cosetBranchStep_6627 s
  · exact g32p_row31_cosetBranchStep_6628 s
  · exact g32p_row31_cosetBranchStep_6629 s
  · exact g32p_row31_cosetBranchStep_6630 s
  · exact g32p_row31_cosetBranchStep_6631 s
  · exact g32p_row31_cosetBranchStep_6632 s
  · exact g32p_row31_cosetBranchStep_6633 s
  · exact g32p_row31_cosetBranchStep_6634 s
  · exact g32p_row31_cosetBranchStep_6635 s
  · exact g32p_row31_cosetBranchStep_6636 s
  · exact g32p_row31_cosetBranchStep_6637 s
  · exact g32p_row31_cosetBranchStep_6638 s
  · exact g32p_row31_cosetBranchStep_6639 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6640 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6640) = g32p_row31_cosetRepresentatives 6640 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6640 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6640) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6640))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6640)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6640 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6640) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6640))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6640)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6641 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6641) = g32p_row31_cosetRepresentatives 6641 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6641 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6641) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6641))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6641)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6641 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6641) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6641))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6641)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6642 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6642) = g32p_row31_cosetRepresentatives 6642 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6642 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6642) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6642))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6642)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6642 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6642) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6642))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6642)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6643 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6643) = g32p_row31_cosetRepresentatives 6643 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6643 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6643) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6643))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6643)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6643 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6643) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6643))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6643)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6644 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6644) = g32p_row31_cosetRepresentatives 6644 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6644 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6644) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6644))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6644)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6644 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6644) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6644))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6644)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6645 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6645) = g32p_row31_cosetRepresentatives 6645 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6645 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6645) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6645))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6645)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6645 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6645) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6645))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6645)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6646 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6646) = g32p_row31_cosetRepresentatives 6646 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6646 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6646) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6646))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6646)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6646 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6646) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6646))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6646)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6647 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6647) = g32p_row31_cosetRepresentatives 6647 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6647 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6647) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6647))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6647)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6647 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6647) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6647))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6647)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6648 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6648) = g32p_row31_cosetRepresentatives 6648 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6648 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6648) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6648))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6648)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6648 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6648) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6648))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6648)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6649 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6649) = g32p_row31_cosetRepresentatives 6649 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6649 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6649) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6649))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6649)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6649 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6649) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6649))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6649)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6650 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6650) = g32p_row31_cosetRepresentatives 6650 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6650 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6650) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6650))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6650)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6650 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6650) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6650))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6650)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6651 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6651) = g32p_row31_cosetRepresentatives 6651 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6651 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6651) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6651))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6651)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6651 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6651) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6651))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6651)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6652 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6652) = g32p_row31_cosetRepresentatives 6652 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6652 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6652) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6652))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6652)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6652 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6652) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6652))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6652)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6653 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6653) = g32p_row31_cosetRepresentatives 6653 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6653 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6653) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6653))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6653)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6653 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6653) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6653))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6653)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6654 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6654) = g32p_row31_cosetRepresentatives 6654 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6654 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6654) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6654))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6654)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6654 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6654) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6654))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6654)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6655 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6655) = g32p_row31_cosetRepresentatives 6655 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6655 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6655) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6655))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6655)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6655 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6655) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6655))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6655)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0415 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 415 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 415 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6640
  · exact g32p_row31_cosetWord_6641
  · exact g32p_row31_cosetWord_6642
  · exact g32p_row31_cosetWord_6643
  · exact g32p_row31_cosetWord_6644
  · exact g32p_row31_cosetWord_6645
  · exact g32p_row31_cosetWord_6646
  · exact g32p_row31_cosetWord_6647
  · exact g32p_row31_cosetWord_6648
  · exact g32p_row31_cosetWord_6649
  · exact g32p_row31_cosetWord_6650
  · exact g32p_row31_cosetWord_6651
  · exact g32p_row31_cosetWord_6652
  · exact g32p_row31_cosetWord_6653
  · exact g32p_row31_cosetWord_6654
  · exact g32p_row31_cosetWord_6655

theorem g32p_row31_cosetGeneratorBlock_0415 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 415 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 415 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 415 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6640 s
  · exact g32p_row31_cosetGeneratorStep_6641 s
  · exact g32p_row31_cosetGeneratorStep_6642 s
  · exact g32p_row31_cosetGeneratorStep_6643 s
  · exact g32p_row31_cosetGeneratorStep_6644 s
  · exact g32p_row31_cosetGeneratorStep_6645 s
  · exact g32p_row31_cosetGeneratorStep_6646 s
  · exact g32p_row31_cosetGeneratorStep_6647 s
  · exact g32p_row31_cosetGeneratorStep_6648 s
  · exact g32p_row31_cosetGeneratorStep_6649 s
  · exact g32p_row31_cosetGeneratorStep_6650 s
  · exact g32p_row31_cosetGeneratorStep_6651 s
  · exact g32p_row31_cosetGeneratorStep_6652 s
  · exact g32p_row31_cosetGeneratorStep_6653 s
  · exact g32p_row31_cosetGeneratorStep_6654 s
  · exact g32p_row31_cosetGeneratorStep_6655 s

theorem g32p_row31_cosetBranchBlock_0415 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 415 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 415 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 415 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6640 s
  · exact g32p_row31_cosetBranchStep_6641 s
  · exact g32p_row31_cosetBranchStep_6642 s
  · exact g32p_row31_cosetBranchStep_6643 s
  · exact g32p_row31_cosetBranchStep_6644 s
  · exact g32p_row31_cosetBranchStep_6645 s
  · exact g32p_row31_cosetBranchStep_6646 s
  · exact g32p_row31_cosetBranchStep_6647 s
  · exact g32p_row31_cosetBranchStep_6648 s
  · exact g32p_row31_cosetBranchStep_6649 s
  · exact g32p_row31_cosetBranchStep_6650 s
  · exact g32p_row31_cosetBranchStep_6651 s
  · exact g32p_row31_cosetBranchStep_6652 s
  · exact g32p_row31_cosetBranchStep_6653 s
  · exact g32p_row31_cosetBranchStep_6654 s
  · exact g32p_row31_cosetBranchStep_6655 s


end HodgeLean.Foundations.Program

end
