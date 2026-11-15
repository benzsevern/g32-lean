import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness51CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked1016
import HodgeLean.Foundations.Program.G32PropFourSixPacked1017
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow51
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0512 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 512) = g32p_row51_cosetRepresentatives 512 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0512 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 512) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 512))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 512)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0512 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 512) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 512))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 512)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0513 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 513) = g32p_row51_cosetRepresentatives 513 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0513 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 513) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 513))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 513)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0513 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 513) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 513))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 513)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0514 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 514) = g32p_row51_cosetRepresentatives 514 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0514 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 514) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 514))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 514)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0514 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 514) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 514))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 514)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0515 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 515) = g32p_row51_cosetRepresentatives 515 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0515 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 515) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 515))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 515)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0515 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 515) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 515))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 515)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0516 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 516) = g32p_row51_cosetRepresentatives 516 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0516 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 516) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 516))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 516)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0516 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 516) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 516))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 516)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0517 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 517) = g32p_row51_cosetRepresentatives 517 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0517 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 517) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 517))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 517)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0517 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 517) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 517))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 517)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0518 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 518) = g32p_row51_cosetRepresentatives 518 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0518 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 518) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 518))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 518)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0518 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 518) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 518))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 518)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0519 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 519) = g32p_row51_cosetRepresentatives 519 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0519 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 519) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 519))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 519)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0519 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 519) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 519))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 519)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0520 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 520) = g32p_row51_cosetRepresentatives 520 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0520 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 520) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 520))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 520)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0520 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 520) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 520))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 520)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0521 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 521) = g32p_row51_cosetRepresentatives 521 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0521 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 521) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 521))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 521)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0521 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 521) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 521))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 521)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0522 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 522) = g32p_row51_cosetRepresentatives 522 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0522 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 522) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 522))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 522)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0522 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 522) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 522))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 522)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0523 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 523) = g32p_row51_cosetRepresentatives 523 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0523 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 523) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 523))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 523)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0523 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 523) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 523))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 523)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0524 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 524) = g32p_row51_cosetRepresentatives 524 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0524 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 524) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 524))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 524)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0524 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 524) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 524))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 524)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0525 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 525) = g32p_row51_cosetRepresentatives 525 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0525 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 525) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 525))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 525)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0525 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 525) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 525))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 525)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0526 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 526) = g32p_row51_cosetRepresentatives 526 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0526 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 526) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 526))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 526)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0526 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 526) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 526))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 526)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0527 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 527) = g32p_row51_cosetRepresentatives 527 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0527 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 527) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 527))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 527)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0527 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 527) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 527))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 527)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0032 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 32 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 32 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0512
  · exact g32p_row51_cosetWord_0513
  · exact g32p_row51_cosetWord_0514
  · exact g32p_row51_cosetWord_0515
  · exact g32p_row51_cosetWord_0516
  · exact g32p_row51_cosetWord_0517
  · exact g32p_row51_cosetWord_0518
  · exact g32p_row51_cosetWord_0519
  · exact g32p_row51_cosetWord_0520
  · exact g32p_row51_cosetWord_0521
  · exact g32p_row51_cosetWord_0522
  · exact g32p_row51_cosetWord_0523
  · exact g32p_row51_cosetWord_0524
  · exact g32p_row51_cosetWord_0525
  · exact g32p_row51_cosetWord_0526
  · exact g32p_row51_cosetWord_0527

theorem g32p_row51_cosetGeneratorBlock_0032 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 32 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 32 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 32 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0512 s
  · exact g32p_row51_cosetGeneratorStep_0513 s
  · exact g32p_row51_cosetGeneratorStep_0514 s
  · exact g32p_row51_cosetGeneratorStep_0515 s
  · exact g32p_row51_cosetGeneratorStep_0516 s
  · exact g32p_row51_cosetGeneratorStep_0517 s
  · exact g32p_row51_cosetGeneratorStep_0518 s
  · exact g32p_row51_cosetGeneratorStep_0519 s
  · exact g32p_row51_cosetGeneratorStep_0520 s
  · exact g32p_row51_cosetGeneratorStep_0521 s
  · exact g32p_row51_cosetGeneratorStep_0522 s
  · exact g32p_row51_cosetGeneratorStep_0523 s
  · exact g32p_row51_cosetGeneratorStep_0524 s
  · exact g32p_row51_cosetGeneratorStep_0525 s
  · exact g32p_row51_cosetGeneratorStep_0526 s
  · exact g32p_row51_cosetGeneratorStep_0527 s

theorem g32p_row51_cosetBranchBlock_0032 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 32 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 32 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 32 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0512 s
  · exact g32p_row51_cosetBranchStep_0513 s
  · exact g32p_row51_cosetBranchStep_0514 s
  · exact g32p_row51_cosetBranchStep_0515 s
  · exact g32p_row51_cosetBranchStep_0516 s
  · exact g32p_row51_cosetBranchStep_0517 s
  · exact g32p_row51_cosetBranchStep_0518 s
  · exact g32p_row51_cosetBranchStep_0519 s
  · exact g32p_row51_cosetBranchStep_0520 s
  · exact g32p_row51_cosetBranchStep_0521 s
  · exact g32p_row51_cosetBranchStep_0522 s
  · exact g32p_row51_cosetBranchStep_0523 s
  · exact g32p_row51_cosetBranchStep_0524 s
  · exact g32p_row51_cosetBranchStep_0525 s
  · exact g32p_row51_cosetBranchStep_0526 s
  · exact g32p_row51_cosetBranchStep_0527 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0528 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 528) = g32p_row51_cosetRepresentatives 528 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0528 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 528) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 528))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 528)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0528 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 528) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 528))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 528)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0529 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 529) = g32p_row51_cosetRepresentatives 529 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0529 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 529) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 529))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 529)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0529 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 529) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 529))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 529)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0530 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 530) = g32p_row51_cosetRepresentatives 530 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0530 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 530) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 530))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 530)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0530 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 530) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 530))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 530)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0531 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 531) = g32p_row51_cosetRepresentatives 531 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0531 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 531) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 531))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 531)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0531 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 531) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 531))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 531)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0532 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 532) = g32p_row51_cosetRepresentatives 532 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0532 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 532) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 532))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 532)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0532 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 532) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 532))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 532)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0533 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 533) = g32p_row51_cosetRepresentatives 533 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0533 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 533) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 533))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 533)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0533 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 533) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 533))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 533)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0534 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 534) = g32p_row51_cosetRepresentatives 534 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0534 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 534) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 534))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 534)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0534 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 534) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 534))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 534)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0535 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 535) = g32p_row51_cosetRepresentatives 535 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0535 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 535) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 535))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 535)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0535 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 535) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 535))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 535)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0536 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 536) = g32p_row51_cosetRepresentatives 536 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0536 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 536) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 536))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 536)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0536 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 536) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 536))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 536)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0537 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 537) = g32p_row51_cosetRepresentatives 537 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0537 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 537) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 537))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 537)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0537 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 537) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 537))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 537)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0538 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 538) = g32p_row51_cosetRepresentatives 538 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0538 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 538) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 538))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 538)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0538 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 538) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 538))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 538)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0539 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 539) = g32p_row51_cosetRepresentatives 539 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0539 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 539) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 539))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 539)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0539 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 539) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 539))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 539)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0540 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 540) = g32p_row51_cosetRepresentatives 540 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0540 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 540) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 540))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 540)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0540 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 540) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 540))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 540)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0541 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 541) = g32p_row51_cosetRepresentatives 541 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0541 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 541) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 541))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 541)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0541 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 541) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 541))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 541)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0542 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 542) = g32p_row51_cosetRepresentatives 542 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0542 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 542) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 542))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 542)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0542 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 542) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 542))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 542)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0543 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 543) = g32p_row51_cosetRepresentatives 543 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0543 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 543) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 543))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 543)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0543 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 543) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 543))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 543)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0033 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 33 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 33 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0528
  · exact g32p_row51_cosetWord_0529
  · exact g32p_row51_cosetWord_0530
  · exact g32p_row51_cosetWord_0531
  · exact g32p_row51_cosetWord_0532
  · exact g32p_row51_cosetWord_0533
  · exact g32p_row51_cosetWord_0534
  · exact g32p_row51_cosetWord_0535
  · exact g32p_row51_cosetWord_0536
  · exact g32p_row51_cosetWord_0537
  · exact g32p_row51_cosetWord_0538
  · exact g32p_row51_cosetWord_0539
  · exact g32p_row51_cosetWord_0540
  · exact g32p_row51_cosetWord_0541
  · exact g32p_row51_cosetWord_0542
  · exact g32p_row51_cosetWord_0543

theorem g32p_row51_cosetGeneratorBlock_0033 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 33 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 33 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 33 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0528 s
  · exact g32p_row51_cosetGeneratorStep_0529 s
  · exact g32p_row51_cosetGeneratorStep_0530 s
  · exact g32p_row51_cosetGeneratorStep_0531 s
  · exact g32p_row51_cosetGeneratorStep_0532 s
  · exact g32p_row51_cosetGeneratorStep_0533 s
  · exact g32p_row51_cosetGeneratorStep_0534 s
  · exact g32p_row51_cosetGeneratorStep_0535 s
  · exact g32p_row51_cosetGeneratorStep_0536 s
  · exact g32p_row51_cosetGeneratorStep_0537 s
  · exact g32p_row51_cosetGeneratorStep_0538 s
  · exact g32p_row51_cosetGeneratorStep_0539 s
  · exact g32p_row51_cosetGeneratorStep_0540 s
  · exact g32p_row51_cosetGeneratorStep_0541 s
  · exact g32p_row51_cosetGeneratorStep_0542 s
  · exact g32p_row51_cosetGeneratorStep_0543 s

theorem g32p_row51_cosetBranchBlock_0033 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 33 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 33 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 33 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0528 s
  · exact g32p_row51_cosetBranchStep_0529 s
  · exact g32p_row51_cosetBranchStep_0530 s
  · exact g32p_row51_cosetBranchStep_0531 s
  · exact g32p_row51_cosetBranchStep_0532 s
  · exact g32p_row51_cosetBranchStep_0533 s
  · exact g32p_row51_cosetBranchStep_0534 s
  · exact g32p_row51_cosetBranchStep_0535 s
  · exact g32p_row51_cosetBranchStep_0536 s
  · exact g32p_row51_cosetBranchStep_0537 s
  · exact g32p_row51_cosetBranchStep_0538 s
  · exact g32p_row51_cosetBranchStep_0539 s
  · exact g32p_row51_cosetBranchStep_0540 s
  · exact g32p_row51_cosetBranchStep_0541 s
  · exact g32p_row51_cosetBranchStep_0542 s
  · exact g32p_row51_cosetBranchStep_0543 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0544 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 544) = g32p_row51_cosetRepresentatives 544 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0544 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 544) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 544))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 544)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0544 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 544) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 544))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 544)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0545 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 545) = g32p_row51_cosetRepresentatives 545 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0545 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 545) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 545))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 545)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0545 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 545) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 545))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 545)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0546 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 546) = g32p_row51_cosetRepresentatives 546 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0546 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 546) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 546))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 546)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0546 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 546) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 546))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 546)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0547 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 547) = g32p_row51_cosetRepresentatives 547 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0547 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 547) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 547))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 547)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0547 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 547) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 547))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 547)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0548 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 548) = g32p_row51_cosetRepresentatives 548 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0548 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 548) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 548))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 548)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0548 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 548) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 548))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 548)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0549 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 549) = g32p_row51_cosetRepresentatives 549 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0549 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 549) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 549))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 549)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0549 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 549) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 549))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 549)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0550 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 550) = g32p_row51_cosetRepresentatives 550 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0550 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 550) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 550))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 550)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0550 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 550) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 550))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 550)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0551 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 551) = g32p_row51_cosetRepresentatives 551 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0551 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 551) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 551))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 551)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0551 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 551) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 551))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 551)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0552 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 552) = g32p_row51_cosetRepresentatives 552 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0552 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 552) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 552))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 552)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0552 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 552) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 552))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 552)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0553 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 553) = g32p_row51_cosetRepresentatives 553 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0553 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 553) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 553))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 553)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0553 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 553) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 553))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 553)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0554 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 554) = g32p_row51_cosetRepresentatives 554 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0554 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 554) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 554))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 554)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0554 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 554) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 554))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 554)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0555 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 555) = g32p_row51_cosetRepresentatives 555 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0555 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 555) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 555))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 555)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0555 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 555) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 555))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 555)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0556 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 556) = g32p_row51_cosetRepresentatives 556 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0556 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 556) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 556))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 556)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0556 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 556) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 556))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 556)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0557 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 557) = g32p_row51_cosetRepresentatives 557 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0557 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 557) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 557))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 557)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0557 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 557) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 557))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 557)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0558 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 558) = g32p_row51_cosetRepresentatives 558 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0558 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 558) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 558))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 558)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0558 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 558) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 558))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 558)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0559 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 559) = g32p_row51_cosetRepresentatives 559 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0559 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 559) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 559))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 559)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0559 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 559) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 559))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 559)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0034 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 34 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 34 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0544
  · exact g32p_row51_cosetWord_0545
  · exact g32p_row51_cosetWord_0546
  · exact g32p_row51_cosetWord_0547
  · exact g32p_row51_cosetWord_0548
  · exact g32p_row51_cosetWord_0549
  · exact g32p_row51_cosetWord_0550
  · exact g32p_row51_cosetWord_0551
  · exact g32p_row51_cosetWord_0552
  · exact g32p_row51_cosetWord_0553
  · exact g32p_row51_cosetWord_0554
  · exact g32p_row51_cosetWord_0555
  · exact g32p_row51_cosetWord_0556
  · exact g32p_row51_cosetWord_0557
  · exact g32p_row51_cosetWord_0558
  · exact g32p_row51_cosetWord_0559

theorem g32p_row51_cosetGeneratorBlock_0034 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 34 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 34 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 34 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0544 s
  · exact g32p_row51_cosetGeneratorStep_0545 s
  · exact g32p_row51_cosetGeneratorStep_0546 s
  · exact g32p_row51_cosetGeneratorStep_0547 s
  · exact g32p_row51_cosetGeneratorStep_0548 s
  · exact g32p_row51_cosetGeneratorStep_0549 s
  · exact g32p_row51_cosetGeneratorStep_0550 s
  · exact g32p_row51_cosetGeneratorStep_0551 s
  · exact g32p_row51_cosetGeneratorStep_0552 s
  · exact g32p_row51_cosetGeneratorStep_0553 s
  · exact g32p_row51_cosetGeneratorStep_0554 s
  · exact g32p_row51_cosetGeneratorStep_0555 s
  · exact g32p_row51_cosetGeneratorStep_0556 s
  · exact g32p_row51_cosetGeneratorStep_0557 s
  · exact g32p_row51_cosetGeneratorStep_0558 s
  · exact g32p_row51_cosetGeneratorStep_0559 s

theorem g32p_row51_cosetBranchBlock_0034 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 34 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 34 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 34 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0544 s
  · exact g32p_row51_cosetBranchStep_0545 s
  · exact g32p_row51_cosetBranchStep_0546 s
  · exact g32p_row51_cosetBranchStep_0547 s
  · exact g32p_row51_cosetBranchStep_0548 s
  · exact g32p_row51_cosetBranchStep_0549 s
  · exact g32p_row51_cosetBranchStep_0550 s
  · exact g32p_row51_cosetBranchStep_0551 s
  · exact g32p_row51_cosetBranchStep_0552 s
  · exact g32p_row51_cosetBranchStep_0553 s
  · exact g32p_row51_cosetBranchStep_0554 s
  · exact g32p_row51_cosetBranchStep_0555 s
  · exact g32p_row51_cosetBranchStep_0556 s
  · exact g32p_row51_cosetBranchStep_0557 s
  · exact g32p_row51_cosetBranchStep_0558 s
  · exact g32p_row51_cosetBranchStep_0559 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0560 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 560) = g32p_row51_cosetRepresentatives 560 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0560 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 560) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 560))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 560)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0560 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 560) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 560))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 560)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0561 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 561) = g32p_row51_cosetRepresentatives 561 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0561 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 561) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 561))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 561)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0561 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 561) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 561))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 561)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0562 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 562) = g32p_row51_cosetRepresentatives 562 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0562 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 562) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 562))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 562)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0562 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 562) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 562))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 562)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0563 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 563) = g32p_row51_cosetRepresentatives 563 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0563 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 563) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 563))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 563)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0563 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 563) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 563))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 563)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0564 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 564) = g32p_row51_cosetRepresentatives 564 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0564 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 564) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 564))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 564)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0564 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 564) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 564))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 564)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0565 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 565) = g32p_row51_cosetRepresentatives 565 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0565 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 565) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 565))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 565)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0565 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 565) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 565))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 565)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0566 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 566) = g32p_row51_cosetRepresentatives 566 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0566 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 566) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 566))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 566)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0566 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 566) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 566))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 566)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0567 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 567) = g32p_row51_cosetRepresentatives 567 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0567 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 567) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 567))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 567)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0567 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 567) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 567))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 567)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0568 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 568) = g32p_row51_cosetRepresentatives 568 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0568 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 568) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 568))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 568)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0568 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 568) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 568))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 568)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0569 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 569) = g32p_row51_cosetRepresentatives 569 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0569 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 569) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 569))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 569)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0569 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 569) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 569))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 569)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0570 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 570) = g32p_row51_cosetRepresentatives 570 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0570 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 570) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 570))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 570)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0570 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 570) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 570))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 570)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0571 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 571) = g32p_row51_cosetRepresentatives 571 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0571 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 571) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 571))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 571)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0571 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 571) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 571))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 571)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0572 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 572) = g32p_row51_cosetRepresentatives 572 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0572 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 572) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 572))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 572)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0572 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 572) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 572))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 572)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0573 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 573) = g32p_row51_cosetRepresentatives 573 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0573 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 573) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 573))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 573)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0573 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 573) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 573))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 573)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0574 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 574) = g32p_row51_cosetRepresentatives 574 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0574 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 574) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 574))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 574)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0574 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 574) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 574))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 574)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0575 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 575) = g32p_row51_cosetRepresentatives 575 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0575 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 575) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 575))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 575)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0575 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 575) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 575))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 575)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0035 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 35 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 35 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0560
  · exact g32p_row51_cosetWord_0561
  · exact g32p_row51_cosetWord_0562
  · exact g32p_row51_cosetWord_0563
  · exact g32p_row51_cosetWord_0564
  · exact g32p_row51_cosetWord_0565
  · exact g32p_row51_cosetWord_0566
  · exact g32p_row51_cosetWord_0567
  · exact g32p_row51_cosetWord_0568
  · exact g32p_row51_cosetWord_0569
  · exact g32p_row51_cosetWord_0570
  · exact g32p_row51_cosetWord_0571
  · exact g32p_row51_cosetWord_0572
  · exact g32p_row51_cosetWord_0573
  · exact g32p_row51_cosetWord_0574
  · exact g32p_row51_cosetWord_0575

theorem g32p_row51_cosetGeneratorBlock_0035 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 35 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 35 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 35 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0560 s
  · exact g32p_row51_cosetGeneratorStep_0561 s
  · exact g32p_row51_cosetGeneratorStep_0562 s
  · exact g32p_row51_cosetGeneratorStep_0563 s
  · exact g32p_row51_cosetGeneratorStep_0564 s
  · exact g32p_row51_cosetGeneratorStep_0565 s
  · exact g32p_row51_cosetGeneratorStep_0566 s
  · exact g32p_row51_cosetGeneratorStep_0567 s
  · exact g32p_row51_cosetGeneratorStep_0568 s
  · exact g32p_row51_cosetGeneratorStep_0569 s
  · exact g32p_row51_cosetGeneratorStep_0570 s
  · exact g32p_row51_cosetGeneratorStep_0571 s
  · exact g32p_row51_cosetGeneratorStep_0572 s
  · exact g32p_row51_cosetGeneratorStep_0573 s
  · exact g32p_row51_cosetGeneratorStep_0574 s
  · exact g32p_row51_cosetGeneratorStep_0575 s

theorem g32p_row51_cosetBranchBlock_0035 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 35 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 35 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 35 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0560 s
  · exact g32p_row51_cosetBranchStep_0561 s
  · exact g32p_row51_cosetBranchStep_0562 s
  · exact g32p_row51_cosetBranchStep_0563 s
  · exact g32p_row51_cosetBranchStep_0564 s
  · exact g32p_row51_cosetBranchStep_0565 s
  · exact g32p_row51_cosetBranchStep_0566 s
  · exact g32p_row51_cosetBranchStep_0567 s
  · exact g32p_row51_cosetBranchStep_0568 s
  · exact g32p_row51_cosetBranchStep_0569 s
  · exact g32p_row51_cosetBranchStep_0570 s
  · exact g32p_row51_cosetBranchStep_0571 s
  · exact g32p_row51_cosetBranchStep_0572 s
  · exact g32p_row51_cosetBranchStep_0573 s
  · exact g32p_row51_cosetBranchStep_0574 s
  · exact g32p_row51_cosetBranchStep_0575 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0576 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 576) = g32p_row51_cosetRepresentatives 576 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0576 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 576) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 576))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 576)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0576 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 576) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 576))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 576)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0577 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 577) = g32p_row51_cosetRepresentatives 577 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0577 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 577) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 577))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 577)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0577 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 577) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 577))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 577)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0578 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 578) = g32p_row51_cosetRepresentatives 578 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0578 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 578) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 578))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 578)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0578 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 578) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 578))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 578)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0579 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 579) = g32p_row51_cosetRepresentatives 579 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0579 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 579) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 579))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 579)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0579 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 579) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 579))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 579)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0580 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 580) = g32p_row51_cosetRepresentatives 580 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0580 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 580) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 580))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 580)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0580 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 580) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 580))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 580)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0581 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 581) = g32p_row51_cosetRepresentatives 581 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0581 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 581) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 581))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 581)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0581 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 581) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 581))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 581)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0582 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 582) = g32p_row51_cosetRepresentatives 582 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0582 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 582) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 582))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 582)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0582 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 582) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 582))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 582)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0583 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 583) = g32p_row51_cosetRepresentatives 583 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0583 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 583) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 583))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 583)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0583 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 583) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 583))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 583)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0584 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 584) = g32p_row51_cosetRepresentatives 584 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0584 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 584) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 584))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 584)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0584 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 584) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 584))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 584)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0585 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 585) = g32p_row51_cosetRepresentatives 585 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0585 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 585) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 585))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 585)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0585 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 585) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 585))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 585)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0586 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 586) = g32p_row51_cosetRepresentatives 586 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0586 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 586) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 586))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 586)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0586 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 586) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 586))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 586)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0587 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 587) = g32p_row51_cosetRepresentatives 587 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0587 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 587) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 587))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 587)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0587 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 587) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 587))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 587)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0588 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 588) = g32p_row51_cosetRepresentatives 588 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0588 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 588) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 588))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 588)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0588 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 588) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 588))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 588)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0589 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 589) = g32p_row51_cosetRepresentatives 589 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0589 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 589) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 589))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 589)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0589 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 589) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 589))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 589)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0590 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 590) = g32p_row51_cosetRepresentatives 590 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0590 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 590) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 590))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 590)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0590 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 590) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 590))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 590)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0591 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 591) = g32p_row51_cosetRepresentatives 591 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0591 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 591) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 591))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 591)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0591 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 591) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 591))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 591)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0036 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 36 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 36 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0576
  · exact g32p_row51_cosetWord_0577
  · exact g32p_row51_cosetWord_0578
  · exact g32p_row51_cosetWord_0579
  · exact g32p_row51_cosetWord_0580
  · exact g32p_row51_cosetWord_0581
  · exact g32p_row51_cosetWord_0582
  · exact g32p_row51_cosetWord_0583
  · exact g32p_row51_cosetWord_0584
  · exact g32p_row51_cosetWord_0585
  · exact g32p_row51_cosetWord_0586
  · exact g32p_row51_cosetWord_0587
  · exact g32p_row51_cosetWord_0588
  · exact g32p_row51_cosetWord_0589
  · exact g32p_row51_cosetWord_0590
  · exact g32p_row51_cosetWord_0591

theorem g32p_row51_cosetGeneratorBlock_0036 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 36 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 36 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 36 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0576 s
  · exact g32p_row51_cosetGeneratorStep_0577 s
  · exact g32p_row51_cosetGeneratorStep_0578 s
  · exact g32p_row51_cosetGeneratorStep_0579 s
  · exact g32p_row51_cosetGeneratorStep_0580 s
  · exact g32p_row51_cosetGeneratorStep_0581 s
  · exact g32p_row51_cosetGeneratorStep_0582 s
  · exact g32p_row51_cosetGeneratorStep_0583 s
  · exact g32p_row51_cosetGeneratorStep_0584 s
  · exact g32p_row51_cosetGeneratorStep_0585 s
  · exact g32p_row51_cosetGeneratorStep_0586 s
  · exact g32p_row51_cosetGeneratorStep_0587 s
  · exact g32p_row51_cosetGeneratorStep_0588 s
  · exact g32p_row51_cosetGeneratorStep_0589 s
  · exact g32p_row51_cosetGeneratorStep_0590 s
  · exact g32p_row51_cosetGeneratorStep_0591 s

theorem g32p_row51_cosetBranchBlock_0036 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 36 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 36 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 36 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0576 s
  · exact g32p_row51_cosetBranchStep_0577 s
  · exact g32p_row51_cosetBranchStep_0578 s
  · exact g32p_row51_cosetBranchStep_0579 s
  · exact g32p_row51_cosetBranchStep_0580 s
  · exact g32p_row51_cosetBranchStep_0581 s
  · exact g32p_row51_cosetBranchStep_0582 s
  · exact g32p_row51_cosetBranchStep_0583 s
  · exact g32p_row51_cosetBranchStep_0584 s
  · exact g32p_row51_cosetBranchStep_0585 s
  · exact g32p_row51_cosetBranchStep_0586 s
  · exact g32p_row51_cosetBranchStep_0587 s
  · exact g32p_row51_cosetBranchStep_0588 s
  · exact g32p_row51_cosetBranchStep_0589 s
  · exact g32p_row51_cosetBranchStep_0590 s
  · exact g32p_row51_cosetBranchStep_0591 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0592 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 592) = g32p_row51_cosetRepresentatives 592 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0592 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 592) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 592))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 592)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0592 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 592) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 592))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 592)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0593 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 593) = g32p_row51_cosetRepresentatives 593 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0593 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 593) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 593))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 593)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0593 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 593) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 593))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 593)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0594 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 594) = g32p_row51_cosetRepresentatives 594 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0594 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 594) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 594))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 594)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0594 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 594) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 594))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 594)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0595 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 595) = g32p_row51_cosetRepresentatives 595 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0595 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 595) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 595))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 595)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0595 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 595) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 595))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 595)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0596 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 596) = g32p_row51_cosetRepresentatives 596 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0596 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 596) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 596))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 596)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0596 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 596) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 596))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 596)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0597 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 597) = g32p_row51_cosetRepresentatives 597 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0597 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 597) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 597))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 597)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0597 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 597) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 597))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 597)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0598 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 598) = g32p_row51_cosetRepresentatives 598 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0598 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 598) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 598))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 598)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0598 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 598) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 598))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 598)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0599 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 599) = g32p_row51_cosetRepresentatives 599 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0599 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 599) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 599))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 599)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0599 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 599) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 599))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 599)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0600 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 600) = g32p_row51_cosetRepresentatives 600 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0600 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 600) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 600))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 600)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0600 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 600) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 600))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 600)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0601 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 601) = g32p_row51_cosetRepresentatives 601 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0601 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 601) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 601))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 601)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0601 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 601) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 601))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 601)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0602 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 602) = g32p_row51_cosetRepresentatives 602 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0602 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 602) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 602))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 602)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0602 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 602) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 602))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 602)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0603 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 603) = g32p_row51_cosetRepresentatives 603 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0603 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 603) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 603))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 603)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0603 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 603) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 603))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 603)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0604 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 604) = g32p_row51_cosetRepresentatives 604 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0604 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 604) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 604))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 604)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0604 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 604) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 604))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 604)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0605 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 605) = g32p_row51_cosetRepresentatives 605 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0605 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 605) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 605))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 605)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0605 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 605) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 605))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 605)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0606 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 606) = g32p_row51_cosetRepresentatives 606 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0606 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 606) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 606))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 606)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0606 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 606) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 606))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 606)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0607 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 607) = g32p_row51_cosetRepresentatives 607 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0607 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 607) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 607))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 607)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0607 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 607) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 607))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 607)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0037 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 37 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 37 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0592
  · exact g32p_row51_cosetWord_0593
  · exact g32p_row51_cosetWord_0594
  · exact g32p_row51_cosetWord_0595
  · exact g32p_row51_cosetWord_0596
  · exact g32p_row51_cosetWord_0597
  · exact g32p_row51_cosetWord_0598
  · exact g32p_row51_cosetWord_0599
  · exact g32p_row51_cosetWord_0600
  · exact g32p_row51_cosetWord_0601
  · exact g32p_row51_cosetWord_0602
  · exact g32p_row51_cosetWord_0603
  · exact g32p_row51_cosetWord_0604
  · exact g32p_row51_cosetWord_0605
  · exact g32p_row51_cosetWord_0606
  · exact g32p_row51_cosetWord_0607

theorem g32p_row51_cosetGeneratorBlock_0037 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 37 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 37 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 37 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0592 s
  · exact g32p_row51_cosetGeneratorStep_0593 s
  · exact g32p_row51_cosetGeneratorStep_0594 s
  · exact g32p_row51_cosetGeneratorStep_0595 s
  · exact g32p_row51_cosetGeneratorStep_0596 s
  · exact g32p_row51_cosetGeneratorStep_0597 s
  · exact g32p_row51_cosetGeneratorStep_0598 s
  · exact g32p_row51_cosetGeneratorStep_0599 s
  · exact g32p_row51_cosetGeneratorStep_0600 s
  · exact g32p_row51_cosetGeneratorStep_0601 s
  · exact g32p_row51_cosetGeneratorStep_0602 s
  · exact g32p_row51_cosetGeneratorStep_0603 s
  · exact g32p_row51_cosetGeneratorStep_0604 s
  · exact g32p_row51_cosetGeneratorStep_0605 s
  · exact g32p_row51_cosetGeneratorStep_0606 s
  · exact g32p_row51_cosetGeneratorStep_0607 s

theorem g32p_row51_cosetBranchBlock_0037 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 37 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 37 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 37 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0592 s
  · exact g32p_row51_cosetBranchStep_0593 s
  · exact g32p_row51_cosetBranchStep_0594 s
  · exact g32p_row51_cosetBranchStep_0595 s
  · exact g32p_row51_cosetBranchStep_0596 s
  · exact g32p_row51_cosetBranchStep_0597 s
  · exact g32p_row51_cosetBranchStep_0598 s
  · exact g32p_row51_cosetBranchStep_0599 s
  · exact g32p_row51_cosetBranchStep_0600 s
  · exact g32p_row51_cosetBranchStep_0601 s
  · exact g32p_row51_cosetBranchStep_0602 s
  · exact g32p_row51_cosetBranchStep_0603 s
  · exact g32p_row51_cosetBranchStep_0604 s
  · exact g32p_row51_cosetBranchStep_0605 s
  · exact g32p_row51_cosetBranchStep_0606 s
  · exact g32p_row51_cosetBranchStep_0607 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0608 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 608) = g32p_row51_cosetRepresentatives 608 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0608 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 608) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 608))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 608)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0608 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 608) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 608))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 608)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0609 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 609) = g32p_row51_cosetRepresentatives 609 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0609 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 609) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 609))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 609)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0609 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 609) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 609))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 609)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0610 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 610) = g32p_row51_cosetRepresentatives 610 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0610 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 610) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 610))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 610)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0610 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 610) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 610))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 610)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0611 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 611) = g32p_row51_cosetRepresentatives 611 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0611 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 611) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 611))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 611)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0611 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 611) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 611))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 611)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0612 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 612) = g32p_row51_cosetRepresentatives 612 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0612 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 612) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 612))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 612)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0612 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 612) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 612))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 612)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0613 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 613) = g32p_row51_cosetRepresentatives 613 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0613 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 613) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 613))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 613)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0613 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 613) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 613))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 613)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0614 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 614) = g32p_row51_cosetRepresentatives 614 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0614 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 614) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 614))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 614)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0614 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 614) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 614))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 614)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0615 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 615) = g32p_row51_cosetRepresentatives 615 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0615 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 615) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 615))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 615)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0615 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 615) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 615))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 615)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0616 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 616) = g32p_row51_cosetRepresentatives 616 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0616 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 616) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 616))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 616)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0616 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 616) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 616))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 616)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0617 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 617) = g32p_row51_cosetRepresentatives 617 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0617 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 617) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 617))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 617)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0617 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 617) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 617))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 617)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0618 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 618) = g32p_row51_cosetRepresentatives 618 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0618 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 618) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 618))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 618)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0618 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 618) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 618))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 618)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0619 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 619) = g32p_row51_cosetRepresentatives 619 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0619 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 619) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 619))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 619)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0619 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 619) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 619))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 619)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0620 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 620) = g32p_row51_cosetRepresentatives 620 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0620 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 620) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 620))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 620)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0620 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 620) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 620))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 620)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0621 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 621) = g32p_row51_cosetRepresentatives 621 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0621 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 621) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 621))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 621)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0621 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 621) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 621))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 621)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0622 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 622) = g32p_row51_cosetRepresentatives 622 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0622 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 622) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 622))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 622)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0622 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 622) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 622))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 622)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0623 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 623) = g32p_row51_cosetRepresentatives 623 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0623 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 623) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 623))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 623)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0623 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 623) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 623))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 623)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0038 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 38 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 38 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0608
  · exact g32p_row51_cosetWord_0609
  · exact g32p_row51_cosetWord_0610
  · exact g32p_row51_cosetWord_0611
  · exact g32p_row51_cosetWord_0612
  · exact g32p_row51_cosetWord_0613
  · exact g32p_row51_cosetWord_0614
  · exact g32p_row51_cosetWord_0615
  · exact g32p_row51_cosetWord_0616
  · exact g32p_row51_cosetWord_0617
  · exact g32p_row51_cosetWord_0618
  · exact g32p_row51_cosetWord_0619
  · exact g32p_row51_cosetWord_0620
  · exact g32p_row51_cosetWord_0621
  · exact g32p_row51_cosetWord_0622
  · exact g32p_row51_cosetWord_0623

theorem g32p_row51_cosetGeneratorBlock_0038 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 38 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 38 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 38 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0608 s
  · exact g32p_row51_cosetGeneratorStep_0609 s
  · exact g32p_row51_cosetGeneratorStep_0610 s
  · exact g32p_row51_cosetGeneratorStep_0611 s
  · exact g32p_row51_cosetGeneratorStep_0612 s
  · exact g32p_row51_cosetGeneratorStep_0613 s
  · exact g32p_row51_cosetGeneratorStep_0614 s
  · exact g32p_row51_cosetGeneratorStep_0615 s
  · exact g32p_row51_cosetGeneratorStep_0616 s
  · exact g32p_row51_cosetGeneratorStep_0617 s
  · exact g32p_row51_cosetGeneratorStep_0618 s
  · exact g32p_row51_cosetGeneratorStep_0619 s
  · exact g32p_row51_cosetGeneratorStep_0620 s
  · exact g32p_row51_cosetGeneratorStep_0621 s
  · exact g32p_row51_cosetGeneratorStep_0622 s
  · exact g32p_row51_cosetGeneratorStep_0623 s

theorem g32p_row51_cosetBranchBlock_0038 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 38 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 38 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 38 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0608 s
  · exact g32p_row51_cosetBranchStep_0609 s
  · exact g32p_row51_cosetBranchStep_0610 s
  · exact g32p_row51_cosetBranchStep_0611 s
  · exact g32p_row51_cosetBranchStep_0612 s
  · exact g32p_row51_cosetBranchStep_0613 s
  · exact g32p_row51_cosetBranchStep_0614 s
  · exact g32p_row51_cosetBranchStep_0615 s
  · exact g32p_row51_cosetBranchStep_0616 s
  · exact g32p_row51_cosetBranchStep_0617 s
  · exact g32p_row51_cosetBranchStep_0618 s
  · exact g32p_row51_cosetBranchStep_0619 s
  · exact g32p_row51_cosetBranchStep_0620 s
  · exact g32p_row51_cosetBranchStep_0621 s
  · exact g32p_row51_cosetBranchStep_0622 s
  · exact g32p_row51_cosetBranchStep_0623 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0624 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 624) = g32p_row51_cosetRepresentatives 624 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0624 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 624) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 624))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 624)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0624 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 624) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 624))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 624)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0625 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 625) = g32p_row51_cosetRepresentatives 625 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0625 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 625) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 625))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 625)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0625 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 625) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 625))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 625)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0626 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 626) = g32p_row51_cosetRepresentatives 626 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0626 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 626) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 626))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 626)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0626 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 626) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 626))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 626)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0627 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 627) = g32p_row51_cosetRepresentatives 627 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0627 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 627) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 627))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 627)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0627 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 627) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 627))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 627)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0628 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 628) = g32p_row51_cosetRepresentatives 628 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0628 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 628) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 628))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 628)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0628 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 628) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 628))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 628)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0629 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 629) = g32p_row51_cosetRepresentatives 629 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0629 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 629) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 629))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 629)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0629 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 629) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 629))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 629)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0630 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 630) = g32p_row51_cosetRepresentatives 630 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0630 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 630) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 630))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 630)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0630 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 630) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 630))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 630)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0631 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 631) = g32p_row51_cosetRepresentatives 631 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0631 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 631) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 631))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 631)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0631 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 631) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 631))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 631)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0632 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 632) = g32p_row51_cosetRepresentatives 632 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0632 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 632) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 632))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 632)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0632 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 632) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 632))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 632)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0633 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 633) = g32p_row51_cosetRepresentatives 633 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0633 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 633) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 633))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 633)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0633 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 633) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 633))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 633)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0634 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 634) = g32p_row51_cosetRepresentatives 634 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0634 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 634) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 634))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 634)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0634 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 634) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 634))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 634)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0635 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 635) = g32p_row51_cosetRepresentatives 635 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0635 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 635) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 635))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 635)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0635 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 635) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 635))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 635)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0636 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 636) = g32p_row51_cosetRepresentatives 636 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0636 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 636) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 636))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 636)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0636 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 636) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 636))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 636)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0637 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 637) = g32p_row51_cosetRepresentatives 637 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0637 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 637) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 637))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 637)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0637 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 637) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 637))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 637)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0638 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 638) = g32p_row51_cosetRepresentatives 638 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0638 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 638) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 638))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 638)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0638 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 638) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 638))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 638)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0639 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 639) = g32p_row51_cosetRepresentatives 639 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0639 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 639) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 639))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 639)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0639 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 639) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 639))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 639)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0039 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 39 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 39 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0624
  · exact g32p_row51_cosetWord_0625
  · exact g32p_row51_cosetWord_0626
  · exact g32p_row51_cosetWord_0627
  · exact g32p_row51_cosetWord_0628
  · exact g32p_row51_cosetWord_0629
  · exact g32p_row51_cosetWord_0630
  · exact g32p_row51_cosetWord_0631
  · exact g32p_row51_cosetWord_0632
  · exact g32p_row51_cosetWord_0633
  · exact g32p_row51_cosetWord_0634
  · exact g32p_row51_cosetWord_0635
  · exact g32p_row51_cosetWord_0636
  · exact g32p_row51_cosetWord_0637
  · exact g32p_row51_cosetWord_0638
  · exact g32p_row51_cosetWord_0639

theorem g32p_row51_cosetGeneratorBlock_0039 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 39 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 39 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 39 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0624 s
  · exact g32p_row51_cosetGeneratorStep_0625 s
  · exact g32p_row51_cosetGeneratorStep_0626 s
  · exact g32p_row51_cosetGeneratorStep_0627 s
  · exact g32p_row51_cosetGeneratorStep_0628 s
  · exact g32p_row51_cosetGeneratorStep_0629 s
  · exact g32p_row51_cosetGeneratorStep_0630 s
  · exact g32p_row51_cosetGeneratorStep_0631 s
  · exact g32p_row51_cosetGeneratorStep_0632 s
  · exact g32p_row51_cosetGeneratorStep_0633 s
  · exact g32p_row51_cosetGeneratorStep_0634 s
  · exact g32p_row51_cosetGeneratorStep_0635 s
  · exact g32p_row51_cosetGeneratorStep_0636 s
  · exact g32p_row51_cosetGeneratorStep_0637 s
  · exact g32p_row51_cosetGeneratorStep_0638 s
  · exact g32p_row51_cosetGeneratorStep_0639 s

theorem g32p_row51_cosetBranchBlock_0039 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 39 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 39 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 39 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0624 s
  · exact g32p_row51_cosetBranchStep_0625 s
  · exact g32p_row51_cosetBranchStep_0626 s
  · exact g32p_row51_cosetBranchStep_0627 s
  · exact g32p_row51_cosetBranchStep_0628 s
  · exact g32p_row51_cosetBranchStep_0629 s
  · exact g32p_row51_cosetBranchStep_0630 s
  · exact g32p_row51_cosetBranchStep_0631 s
  · exact g32p_row51_cosetBranchStep_0632 s
  · exact g32p_row51_cosetBranchStep_0633 s
  · exact g32p_row51_cosetBranchStep_0634 s
  · exact g32p_row51_cosetBranchStep_0635 s
  · exact g32p_row51_cosetBranchStep_0636 s
  · exact g32p_row51_cosetBranchStep_0637 s
  · exact g32p_row51_cosetBranchStep_0638 s
  · exact g32p_row51_cosetBranchStep_0639 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0640 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 640) = g32p_row51_cosetRepresentatives 640 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0640 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 640) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 640))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 640)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0640 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 640) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 640))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 640)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0641 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 641) = g32p_row51_cosetRepresentatives 641 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0641 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 641) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 641))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 641)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0641 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 641) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 641))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 641)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0642 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 642) = g32p_row51_cosetRepresentatives 642 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0642 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 642) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 642))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 642)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0642 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 642) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 642))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 642)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0643 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 643) = g32p_row51_cosetRepresentatives 643 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0643 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 643) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 643))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 643)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0643 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 643) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 643))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 643)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0644 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 644) = g32p_row51_cosetRepresentatives 644 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0644 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 644) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 644))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 644)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0644 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 644) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 644))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 644)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0645 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 645) = g32p_row51_cosetRepresentatives 645 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0645 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 645) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 645))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 645)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0645 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 645) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 645))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 645)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0646 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 646) = g32p_row51_cosetRepresentatives 646 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0646 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 646) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 646))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 646)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0646 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 646) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 646))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 646)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0647 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 647) = g32p_row51_cosetRepresentatives 647 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0647 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 647) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 647))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 647)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0647 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 647) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 647))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 647)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0648 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 648) = g32p_row51_cosetRepresentatives 648 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0648 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 648) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 648))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 648)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0648 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 648) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 648))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 648)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0649 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 649) = g32p_row51_cosetRepresentatives 649 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0649 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 649) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 649))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 649)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0649 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 649) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 649))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 649)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0650 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 650) = g32p_row51_cosetRepresentatives 650 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0650 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 650) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 650))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 650)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0650 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 650) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 650))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 650)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0651 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 651) = g32p_row51_cosetRepresentatives 651 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0651 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 651) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 651))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 651)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0651 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 651) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 651))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 651)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0652 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 652) = g32p_row51_cosetRepresentatives 652 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0652 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 652) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 652))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 652)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0652 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 652) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 652))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 652)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0653 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 653) = g32p_row51_cosetRepresentatives 653 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0653 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 653) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 653))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 653)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0653 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 653) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 653))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 653)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0654 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 654) = g32p_row51_cosetRepresentatives 654 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0654 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 654) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 654))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 654)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0654 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 654) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 654))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 654)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0655 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 655) = g32p_row51_cosetRepresentatives 655 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0655 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 655) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 655))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 655)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0655 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 655) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 655))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 655)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0040 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 40 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 40 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0640
  · exact g32p_row51_cosetWord_0641
  · exact g32p_row51_cosetWord_0642
  · exact g32p_row51_cosetWord_0643
  · exact g32p_row51_cosetWord_0644
  · exact g32p_row51_cosetWord_0645
  · exact g32p_row51_cosetWord_0646
  · exact g32p_row51_cosetWord_0647
  · exact g32p_row51_cosetWord_0648
  · exact g32p_row51_cosetWord_0649
  · exact g32p_row51_cosetWord_0650
  · exact g32p_row51_cosetWord_0651
  · exact g32p_row51_cosetWord_0652
  · exact g32p_row51_cosetWord_0653
  · exact g32p_row51_cosetWord_0654
  · exact g32p_row51_cosetWord_0655

theorem g32p_row51_cosetGeneratorBlock_0040 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 40 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 40 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 40 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0640 s
  · exact g32p_row51_cosetGeneratorStep_0641 s
  · exact g32p_row51_cosetGeneratorStep_0642 s
  · exact g32p_row51_cosetGeneratorStep_0643 s
  · exact g32p_row51_cosetGeneratorStep_0644 s
  · exact g32p_row51_cosetGeneratorStep_0645 s
  · exact g32p_row51_cosetGeneratorStep_0646 s
  · exact g32p_row51_cosetGeneratorStep_0647 s
  · exact g32p_row51_cosetGeneratorStep_0648 s
  · exact g32p_row51_cosetGeneratorStep_0649 s
  · exact g32p_row51_cosetGeneratorStep_0650 s
  · exact g32p_row51_cosetGeneratorStep_0651 s
  · exact g32p_row51_cosetGeneratorStep_0652 s
  · exact g32p_row51_cosetGeneratorStep_0653 s
  · exact g32p_row51_cosetGeneratorStep_0654 s
  · exact g32p_row51_cosetGeneratorStep_0655 s

theorem g32p_row51_cosetBranchBlock_0040 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 40 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 40 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 40 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0640 s
  · exact g32p_row51_cosetBranchStep_0641 s
  · exact g32p_row51_cosetBranchStep_0642 s
  · exact g32p_row51_cosetBranchStep_0643 s
  · exact g32p_row51_cosetBranchStep_0644 s
  · exact g32p_row51_cosetBranchStep_0645 s
  · exact g32p_row51_cosetBranchStep_0646 s
  · exact g32p_row51_cosetBranchStep_0647 s
  · exact g32p_row51_cosetBranchStep_0648 s
  · exact g32p_row51_cosetBranchStep_0649 s
  · exact g32p_row51_cosetBranchStep_0650 s
  · exact g32p_row51_cosetBranchStep_0651 s
  · exact g32p_row51_cosetBranchStep_0652 s
  · exact g32p_row51_cosetBranchStep_0653 s
  · exact g32p_row51_cosetBranchStep_0654 s
  · exact g32p_row51_cosetBranchStep_0655 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0656 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 656) = g32p_row51_cosetRepresentatives 656 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0656 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 656) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 656))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 656)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0656 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 656) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 656))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 656)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0657 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 657) = g32p_row51_cosetRepresentatives 657 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0657 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 657) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 657))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 657)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0657 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 657) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 657))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 657)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0658 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 658) = g32p_row51_cosetRepresentatives 658 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0658 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 658) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 658))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 658)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0658 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 658) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 658))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 658)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0659 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 659) = g32p_row51_cosetRepresentatives 659 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0659 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 659) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 659))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 659)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0659 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 659) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 659))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 659)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0660 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 660) = g32p_row51_cosetRepresentatives 660 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0660 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 660) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 660))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 660)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0660 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 660) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 660))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 660)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0661 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 661) = g32p_row51_cosetRepresentatives 661 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0661 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 661) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 661))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 661)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0661 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 661) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 661))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 661)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0662 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 662) = g32p_row51_cosetRepresentatives 662 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0662 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 662) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 662))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 662)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0662 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 662) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 662))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 662)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0663 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 663) = g32p_row51_cosetRepresentatives 663 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0663 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 663) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 663))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 663)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0663 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 663) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 663))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 663)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0664 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 664) = g32p_row51_cosetRepresentatives 664 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0664 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 664) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 664))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 664)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0664 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 664) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 664))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 664)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0665 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 665) = g32p_row51_cosetRepresentatives 665 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0665 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 665) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 665))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 665)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0665 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 665) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 665))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 665)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0666 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 666) = g32p_row51_cosetRepresentatives 666 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0666 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 666) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 666))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 666)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0666 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 666) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 666))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 666)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0667 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 667) = g32p_row51_cosetRepresentatives 667 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0667 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 667) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 667))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 667)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0667 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 667) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 667))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 667)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0668 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 668) = g32p_row51_cosetRepresentatives 668 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0668 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 668) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 668))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 668)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0668 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 668) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 668))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 668)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0669 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 669) = g32p_row51_cosetRepresentatives 669 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0669 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 669) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 669))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 669)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0669 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 669) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 669))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 669)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0670 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 670) = g32p_row51_cosetRepresentatives 670 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0670 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 670) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 670))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 670)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0670 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 670) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 670))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 670)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0671 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 671) = g32p_row51_cosetRepresentatives 671 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0671 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 671) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 671))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 671)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0671 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 671) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 671))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 671)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0041 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 41 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 41 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0656
  · exact g32p_row51_cosetWord_0657
  · exact g32p_row51_cosetWord_0658
  · exact g32p_row51_cosetWord_0659
  · exact g32p_row51_cosetWord_0660
  · exact g32p_row51_cosetWord_0661
  · exact g32p_row51_cosetWord_0662
  · exact g32p_row51_cosetWord_0663
  · exact g32p_row51_cosetWord_0664
  · exact g32p_row51_cosetWord_0665
  · exact g32p_row51_cosetWord_0666
  · exact g32p_row51_cosetWord_0667
  · exact g32p_row51_cosetWord_0668
  · exact g32p_row51_cosetWord_0669
  · exact g32p_row51_cosetWord_0670
  · exact g32p_row51_cosetWord_0671

theorem g32p_row51_cosetGeneratorBlock_0041 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 41 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 41 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 41 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0656 s
  · exact g32p_row51_cosetGeneratorStep_0657 s
  · exact g32p_row51_cosetGeneratorStep_0658 s
  · exact g32p_row51_cosetGeneratorStep_0659 s
  · exact g32p_row51_cosetGeneratorStep_0660 s
  · exact g32p_row51_cosetGeneratorStep_0661 s
  · exact g32p_row51_cosetGeneratorStep_0662 s
  · exact g32p_row51_cosetGeneratorStep_0663 s
  · exact g32p_row51_cosetGeneratorStep_0664 s
  · exact g32p_row51_cosetGeneratorStep_0665 s
  · exact g32p_row51_cosetGeneratorStep_0666 s
  · exact g32p_row51_cosetGeneratorStep_0667 s
  · exact g32p_row51_cosetGeneratorStep_0668 s
  · exact g32p_row51_cosetGeneratorStep_0669 s
  · exact g32p_row51_cosetGeneratorStep_0670 s
  · exact g32p_row51_cosetGeneratorStep_0671 s

theorem g32p_row51_cosetBranchBlock_0041 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 41 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 41 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 41 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0656 s
  · exact g32p_row51_cosetBranchStep_0657 s
  · exact g32p_row51_cosetBranchStep_0658 s
  · exact g32p_row51_cosetBranchStep_0659 s
  · exact g32p_row51_cosetBranchStep_0660 s
  · exact g32p_row51_cosetBranchStep_0661 s
  · exact g32p_row51_cosetBranchStep_0662 s
  · exact g32p_row51_cosetBranchStep_0663 s
  · exact g32p_row51_cosetBranchStep_0664 s
  · exact g32p_row51_cosetBranchStep_0665 s
  · exact g32p_row51_cosetBranchStep_0666 s
  · exact g32p_row51_cosetBranchStep_0667 s
  · exact g32p_row51_cosetBranchStep_0668 s
  · exact g32p_row51_cosetBranchStep_0669 s
  · exact g32p_row51_cosetBranchStep_0670 s
  · exact g32p_row51_cosetBranchStep_0671 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0672 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 672) = g32p_row51_cosetRepresentatives 672 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0672 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 672) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 672))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 672)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0672 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 672) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 672))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 672)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0673 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 673) = g32p_row51_cosetRepresentatives 673 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0673 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 673) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 673))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 673)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0673 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 673) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 673))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 673)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0674 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 674) = g32p_row51_cosetRepresentatives 674 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0674 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 674) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 674))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 674)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0674 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 674) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 674))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 674)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0675 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 675) = g32p_row51_cosetRepresentatives 675 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0675 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 675) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 675))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 675)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0675 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 675) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 675))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 675)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0676 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 676) = g32p_row51_cosetRepresentatives 676 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0676 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 676) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 676))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 676)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0676 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 676) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 676))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 676)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0677 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 677) = g32p_row51_cosetRepresentatives 677 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0677 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 677) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 677))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 677)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0677 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 677) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 677))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 677)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0678 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 678) = g32p_row51_cosetRepresentatives 678 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0678 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 678) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 678))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 678)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0678 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 678) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 678))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 678)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0679 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 679) = g32p_row51_cosetRepresentatives 679 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0679 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 679) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 679))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 679)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0679 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 679) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 679))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 679)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0680 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 680) = g32p_row51_cosetRepresentatives 680 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0680 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 680) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 680))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 680)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0680 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 680) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 680))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 680)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0681 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 681) = g32p_row51_cosetRepresentatives 681 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0681 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 681) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 681))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 681)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0681 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 681) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 681))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 681)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0682 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 682) = g32p_row51_cosetRepresentatives 682 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0682 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 682) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 682))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 682)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0682 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 682) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 682))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 682)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0683 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 683) = g32p_row51_cosetRepresentatives 683 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0683 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 683) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 683))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 683)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0683 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 683) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 683))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 683)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0684 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 684) = g32p_row51_cosetRepresentatives 684 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0684 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 684) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 684))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 684)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0684 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 684) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 684))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 684)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0685 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 685) = g32p_row51_cosetRepresentatives 685 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0685 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 685) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 685))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 685)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0685 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 685) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 685))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 685)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0686 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 686) = g32p_row51_cosetRepresentatives 686 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0686 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 686) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 686))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 686)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0686 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 686) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 686))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 686)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0687 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 687) = g32p_row51_cosetRepresentatives 687 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0687 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 687) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 687))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 687)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0687 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 687) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 687))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 687)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0042 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 42 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 42 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0672
  · exact g32p_row51_cosetWord_0673
  · exact g32p_row51_cosetWord_0674
  · exact g32p_row51_cosetWord_0675
  · exact g32p_row51_cosetWord_0676
  · exact g32p_row51_cosetWord_0677
  · exact g32p_row51_cosetWord_0678
  · exact g32p_row51_cosetWord_0679
  · exact g32p_row51_cosetWord_0680
  · exact g32p_row51_cosetWord_0681
  · exact g32p_row51_cosetWord_0682
  · exact g32p_row51_cosetWord_0683
  · exact g32p_row51_cosetWord_0684
  · exact g32p_row51_cosetWord_0685
  · exact g32p_row51_cosetWord_0686
  · exact g32p_row51_cosetWord_0687

theorem g32p_row51_cosetGeneratorBlock_0042 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 42 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 42 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 42 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0672 s
  · exact g32p_row51_cosetGeneratorStep_0673 s
  · exact g32p_row51_cosetGeneratorStep_0674 s
  · exact g32p_row51_cosetGeneratorStep_0675 s
  · exact g32p_row51_cosetGeneratorStep_0676 s
  · exact g32p_row51_cosetGeneratorStep_0677 s
  · exact g32p_row51_cosetGeneratorStep_0678 s
  · exact g32p_row51_cosetGeneratorStep_0679 s
  · exact g32p_row51_cosetGeneratorStep_0680 s
  · exact g32p_row51_cosetGeneratorStep_0681 s
  · exact g32p_row51_cosetGeneratorStep_0682 s
  · exact g32p_row51_cosetGeneratorStep_0683 s
  · exact g32p_row51_cosetGeneratorStep_0684 s
  · exact g32p_row51_cosetGeneratorStep_0685 s
  · exact g32p_row51_cosetGeneratorStep_0686 s
  · exact g32p_row51_cosetGeneratorStep_0687 s

theorem g32p_row51_cosetBranchBlock_0042 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 42 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 42 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 42 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0672 s
  · exact g32p_row51_cosetBranchStep_0673 s
  · exact g32p_row51_cosetBranchStep_0674 s
  · exact g32p_row51_cosetBranchStep_0675 s
  · exact g32p_row51_cosetBranchStep_0676 s
  · exact g32p_row51_cosetBranchStep_0677 s
  · exact g32p_row51_cosetBranchStep_0678 s
  · exact g32p_row51_cosetBranchStep_0679 s
  · exact g32p_row51_cosetBranchStep_0680 s
  · exact g32p_row51_cosetBranchStep_0681 s
  · exact g32p_row51_cosetBranchStep_0682 s
  · exact g32p_row51_cosetBranchStep_0683 s
  · exact g32p_row51_cosetBranchStep_0684 s
  · exact g32p_row51_cosetBranchStep_0685 s
  · exact g32p_row51_cosetBranchStep_0686 s
  · exact g32p_row51_cosetBranchStep_0687 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0688 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 688) = g32p_row51_cosetRepresentatives 688 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0688 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 688) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 688))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 688)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0688 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 688) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 688))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 688)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0689 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 689) = g32p_row51_cosetRepresentatives 689 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0689 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 689) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 689))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 689)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0689 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 689) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 689))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 689)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0690 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 690) = g32p_row51_cosetRepresentatives 690 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0690 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 690) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 690))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 690)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0690 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 690) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 690))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 690)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0691 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 691) = g32p_row51_cosetRepresentatives 691 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0691 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 691) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 691))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 691)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0691 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 691) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 691))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 691)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0692 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 692) = g32p_row51_cosetRepresentatives 692 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0692 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 692) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 692))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 692)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0692 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 692) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 692))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 692)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0693 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 693) = g32p_row51_cosetRepresentatives 693 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0693 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 693) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 693))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 693)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0693 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 693) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 693))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 693)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0694 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 694) = g32p_row51_cosetRepresentatives 694 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0694 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 694) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 694))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 694)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0694 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 694) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 694))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 694)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0695 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 695) = g32p_row51_cosetRepresentatives 695 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0695 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 695) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 695))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 695)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0695 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 695) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 695))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 695)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0696 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 696) = g32p_row51_cosetRepresentatives 696 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0696 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 696) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 696))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 696)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0696 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 696) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 696))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 696)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0697 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 697) = g32p_row51_cosetRepresentatives 697 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0697 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 697) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 697))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 697)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0697 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 697) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 697))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 697)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0698 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 698) = g32p_row51_cosetRepresentatives 698 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0698 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 698) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 698))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 698)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0698 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 698) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 698))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 698)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0699 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 699) = g32p_row51_cosetRepresentatives 699 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0699 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 699) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 699))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 699)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0699 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 699) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 699))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 699)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0700 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 700) = g32p_row51_cosetRepresentatives 700 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0700 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 700) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 700))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 700)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0700 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 700) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 700))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 700)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0701 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 701) = g32p_row51_cosetRepresentatives 701 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0701 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 701) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 701))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 701)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0701 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 701) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 701))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 701)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0702 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 702) = g32p_row51_cosetRepresentatives 702 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0702 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 702) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 702))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 702)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0702 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 702) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 702))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 702)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0703 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 703) = g32p_row51_cosetRepresentatives 703 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0703 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 703) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 703))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 703)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0703 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 703) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 703))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 703)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0043 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 43 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 43 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0688
  · exact g32p_row51_cosetWord_0689
  · exact g32p_row51_cosetWord_0690
  · exact g32p_row51_cosetWord_0691
  · exact g32p_row51_cosetWord_0692
  · exact g32p_row51_cosetWord_0693
  · exact g32p_row51_cosetWord_0694
  · exact g32p_row51_cosetWord_0695
  · exact g32p_row51_cosetWord_0696
  · exact g32p_row51_cosetWord_0697
  · exact g32p_row51_cosetWord_0698
  · exact g32p_row51_cosetWord_0699
  · exact g32p_row51_cosetWord_0700
  · exact g32p_row51_cosetWord_0701
  · exact g32p_row51_cosetWord_0702
  · exact g32p_row51_cosetWord_0703

theorem g32p_row51_cosetGeneratorBlock_0043 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 43 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 43 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 43 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0688 s
  · exact g32p_row51_cosetGeneratorStep_0689 s
  · exact g32p_row51_cosetGeneratorStep_0690 s
  · exact g32p_row51_cosetGeneratorStep_0691 s
  · exact g32p_row51_cosetGeneratorStep_0692 s
  · exact g32p_row51_cosetGeneratorStep_0693 s
  · exact g32p_row51_cosetGeneratorStep_0694 s
  · exact g32p_row51_cosetGeneratorStep_0695 s
  · exact g32p_row51_cosetGeneratorStep_0696 s
  · exact g32p_row51_cosetGeneratorStep_0697 s
  · exact g32p_row51_cosetGeneratorStep_0698 s
  · exact g32p_row51_cosetGeneratorStep_0699 s
  · exact g32p_row51_cosetGeneratorStep_0700 s
  · exact g32p_row51_cosetGeneratorStep_0701 s
  · exact g32p_row51_cosetGeneratorStep_0702 s
  · exact g32p_row51_cosetGeneratorStep_0703 s

theorem g32p_row51_cosetBranchBlock_0043 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 43 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 43 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 43 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0688 s
  · exact g32p_row51_cosetBranchStep_0689 s
  · exact g32p_row51_cosetBranchStep_0690 s
  · exact g32p_row51_cosetBranchStep_0691 s
  · exact g32p_row51_cosetBranchStep_0692 s
  · exact g32p_row51_cosetBranchStep_0693 s
  · exact g32p_row51_cosetBranchStep_0694 s
  · exact g32p_row51_cosetBranchStep_0695 s
  · exact g32p_row51_cosetBranchStep_0696 s
  · exact g32p_row51_cosetBranchStep_0697 s
  · exact g32p_row51_cosetBranchStep_0698 s
  · exact g32p_row51_cosetBranchStep_0699 s
  · exact g32p_row51_cosetBranchStep_0700 s
  · exact g32p_row51_cosetBranchStep_0701 s
  · exact g32p_row51_cosetBranchStep_0702 s
  · exact g32p_row51_cosetBranchStep_0703 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetWord_0704 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 704) = g32p_row51_cosetRepresentatives 704 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0704 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 704) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 704))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 704)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0704 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 704) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 704))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 704)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0705 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 705) = g32p_row51_cosetRepresentatives 705 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0705 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 705) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 705))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 705)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0705 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 705) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 705))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 705)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0706 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 706) = g32p_row51_cosetRepresentatives 706 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0706 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 706) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 706))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 706)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0706 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 706) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 706))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 706)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0707 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 707) = g32p_row51_cosetRepresentatives 707 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0707 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 707) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 707))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 707)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0707 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 707) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 707))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 707)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0708 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 708) = g32p_row51_cosetRepresentatives 708 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0708 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 708) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 708))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 708)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0708 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 708) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 708))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 708)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0709 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 709) = g32p_row51_cosetRepresentatives 709 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0709 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 709) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 709))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 709)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0709 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 709) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 709))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 709)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0710 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 710) = g32p_row51_cosetRepresentatives 710 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0710 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 710) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 710))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 710)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0710 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 710) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 710))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 710)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0711 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 711) = g32p_row51_cosetRepresentatives 711 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0711 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 711) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 711))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 711)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0711 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 711) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 711))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 711)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0712 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 712) = g32p_row51_cosetRepresentatives 712 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0712 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 712) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 712))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 712)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0712 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 712) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 712))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 712)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0713 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 713) = g32p_row51_cosetRepresentatives 713 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0713 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 713) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 713))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 713)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0713 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 713) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 713))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 713)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0714 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 714) = g32p_row51_cosetRepresentatives 714 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0714 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 714) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 714))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 714)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0714 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 714) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 714))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 714)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0715 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 715) = g32p_row51_cosetRepresentatives 715 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0715 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 715) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 715))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 715)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0715 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 715) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 715))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 715)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0716 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 716) = g32p_row51_cosetRepresentatives 716 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0716 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 716) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 716))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 716)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0716 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 716) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 716))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 716)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0717 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 717) = g32p_row51_cosetRepresentatives 717 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0717 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 717) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 717))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 717)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0717 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 717) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 717))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 717)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0718 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 718) = g32p_row51_cosetRepresentatives 718 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0718 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 718) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 718))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 718)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0718 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 718) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 718))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 718)) := by
  decide +kernel

theorem g32p_row51_cosetWord_0719 :
    g32p_archiveIntegralWord (g32p_row51_cosetWords 719) = g32p_row51_cosetRepresentatives 719 := by
  decide +kernel

theorem g32p_row51_cosetGeneratorStep_0719 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives 719) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s 719))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s 719)) := by
  decide +kernel

theorem g32p_row51_cosetBranchStep_0719 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives 719) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s 719))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s 719)) := by
  decide +kernel

theorem g32p_row51_cosetWordBlock_0044 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords (g32p_finBlockIndex 720 44 r)) = g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 44 r) := by
  fin_cases r
  · exact g32p_row51_cosetWord_0704
  · exact g32p_row51_cosetWord_0705
  · exact g32p_row51_cosetWord_0706
  · exact g32p_row51_cosetWord_0707
  · exact g32p_row51_cosetWord_0708
  · exact g32p_row51_cosetWord_0709
  · exact g32p_row51_cosetWord_0710
  · exact g32p_row51_cosetWord_0711
  · exact g32p_row51_cosetWord_0712
  · exact g32p_row51_cosetWord_0713
  · exact g32p_row51_cosetWord_0714
  · exact g32p_row51_cosetWord_0715
  · exact g32p_row51_cosetWord_0716
  · exact g32p_row51_cosetWord_0717
  · exact g32p_row51_cosetWord_0718
  · exact g32p_row51_cosetWord_0719

theorem g32p_row51_cosetGeneratorBlock_0044 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 44 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s (g32p_finBlockIndex 720 44 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s (g32p_finBlockIndex 720 44 r))) := by
  fin_cases r
  · exact g32p_row51_cosetGeneratorStep_0704 s
  · exact g32p_row51_cosetGeneratorStep_0705 s
  · exact g32p_row51_cosetGeneratorStep_0706 s
  · exact g32p_row51_cosetGeneratorStep_0707 s
  · exact g32p_row51_cosetGeneratorStep_0708 s
  · exact g32p_row51_cosetGeneratorStep_0709 s
  · exact g32p_row51_cosetGeneratorStep_0710 s
  · exact g32p_row51_cosetGeneratorStep_0711 s
  · exact g32p_row51_cosetGeneratorStep_0712 s
  · exact g32p_row51_cosetGeneratorStep_0713 s
  · exact g32p_row51_cosetGeneratorStep_0714 s
  · exact g32p_row51_cosetGeneratorStep_0715 s
  · exact g32p_row51_cosetGeneratorStep_0716 s
  · exact g32p_row51_cosetGeneratorStep_0717 s
  · exact g32p_row51_cosetGeneratorStep_0718 s
  · exact g32p_row51_cosetGeneratorStep_0719 s

theorem g32p_row51_cosetBranchBlock_0044 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices s) (g32p_row51_cosetRepresentatives (g32p_finBlockIndex 720 44 r)) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetBranchNext s (g32p_finBlockIndex 720 44 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetBranchFactor s (g32p_finBlockIndex 720 44 r))) := by
  fin_cases r
  · exact g32p_row51_cosetBranchStep_0704 s
  · exact g32p_row51_cosetBranchStep_0705 s
  · exact g32p_row51_cosetBranchStep_0706 s
  · exact g32p_row51_cosetBranchStep_0707 s
  · exact g32p_row51_cosetBranchStep_0708 s
  · exact g32p_row51_cosetBranchStep_0709 s
  · exact g32p_row51_cosetBranchStep_0710 s
  · exact g32p_row51_cosetBranchStep_0711 s
  · exact g32p_row51_cosetBranchStep_0712 s
  · exact g32p_row51_cosetBranchStep_0713 s
  · exact g32p_row51_cosetBranchStep_0714 s
  · exact g32p_row51_cosetBranchStep_0715 s
  · exact g32p_row51_cosetBranchStep_0716 s
  · exact g32p_row51_cosetBranchStep_0717 s
  · exact g32p_row51_cosetBranchStep_0718 s
  · exact g32p_row51_cosetBranchStep_0719 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row51_cosetWord (i : Fin 720) :
    g32p_archiveIntegralWord (g32p_row51_cosetWords i) = g32p_row51_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row51_cosetWordBlock_0000
  · exact g32p_row51_cosetWordBlock_0001
  · exact g32p_row51_cosetWordBlock_0002
  · exact g32p_row51_cosetWordBlock_0003
  · exact g32p_row51_cosetWordBlock_0004
  · exact g32p_row51_cosetWordBlock_0005
  · exact g32p_row51_cosetWordBlock_0006
  · exact g32p_row51_cosetWordBlock_0007
  · exact g32p_row51_cosetWordBlock_0008
  · exact g32p_row51_cosetWordBlock_0009
  · exact g32p_row51_cosetWordBlock_0010
  · exact g32p_row51_cosetWordBlock_0011
  · exact g32p_row51_cosetWordBlock_0012
  · exact g32p_row51_cosetWordBlock_0013
  · exact g32p_row51_cosetWordBlock_0014
  · exact g32p_row51_cosetWordBlock_0015
  · exact g32p_row51_cosetWordBlock_0016
  · exact g32p_row51_cosetWordBlock_0017
  · exact g32p_row51_cosetWordBlock_0018
  · exact g32p_row51_cosetWordBlock_0019
  · exact g32p_row51_cosetWordBlock_0020
  · exact g32p_row51_cosetWordBlock_0021
  · exact g32p_row51_cosetWordBlock_0022
  · exact g32p_row51_cosetWordBlock_0023
  · exact g32p_row51_cosetWordBlock_0024
  · exact g32p_row51_cosetWordBlock_0025
  · exact g32p_row51_cosetWordBlock_0026
  · exact g32p_row51_cosetWordBlock_0027
  · exact g32p_row51_cosetWordBlock_0028
  · exact g32p_row51_cosetWordBlock_0029
  · exact g32p_row51_cosetWordBlock_0030
  · exact g32p_row51_cosetWordBlock_0031
  · exact g32p_row51_cosetWordBlock_0032
  · exact g32p_row51_cosetWordBlock_0033
  · exact g32p_row51_cosetWordBlock_0034
  · exact g32p_row51_cosetWordBlock_0035
  · exact g32p_row51_cosetWordBlock_0036
  · exact g32p_row51_cosetWordBlock_0037
  · exact g32p_row51_cosetWordBlock_0038
  · exact g32p_row51_cosetWordBlock_0039
  · exact g32p_row51_cosetWordBlock_0040
  · exact g32p_row51_cosetWordBlock_0041
  · exact g32p_row51_cosetWordBlock_0042
  · exact g32p_row51_cosetWordBlock_0043
  · exact g32p_row51_cosetWordBlock_0044


def g32p_row51_cosetActualRepresentatives (i : Fin 720) : g32p_G := g32p_archiveWord (g32p_row51_cosetWords i)

theorem g32p_row51_cosetActualRepresentatives_map (i : Fin 720) :
    b4b_toMatrix (g32p_row51_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row51_cosetRepresentatives i)) := by
  rw [g32p_row51_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row51_cosetWord]

theorem g32p_row51_cosetGeneratorStep (s : Fin 4) (i : Fin 720) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row51_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetGeneratorNext s i))
        (g32p_row51_groupNodes (g32p_row51_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row51_cosetGeneratorBlock_0000 s
  · exact g32p_row51_cosetGeneratorBlock_0001 s
  · exact g32p_row51_cosetGeneratorBlock_0002 s
  · exact g32p_row51_cosetGeneratorBlock_0003 s
  · exact g32p_row51_cosetGeneratorBlock_0004 s
  · exact g32p_row51_cosetGeneratorBlock_0005 s
  · exact g32p_row51_cosetGeneratorBlock_0006 s
  · exact g32p_row51_cosetGeneratorBlock_0007 s
  · exact g32p_row51_cosetGeneratorBlock_0008 s
  · exact g32p_row51_cosetGeneratorBlock_0009 s
  · exact g32p_row51_cosetGeneratorBlock_0010 s
  · exact g32p_row51_cosetGeneratorBlock_0011 s
  · exact g32p_row51_cosetGeneratorBlock_0012 s
  · exact g32p_row51_cosetGeneratorBlock_0013 s
  · exact g32p_row51_cosetGeneratorBlock_0014 s
  · exact g32p_row51_cosetGeneratorBlock_0015 s
  · exact g32p_row51_cosetGeneratorBlock_0016 s
  · exact g32p_row51_cosetGeneratorBlock_0017 s
  · exact g32p_row51_cosetGeneratorBlock_0018 s
  · exact g32p_row51_cosetGeneratorBlock_0019 s
  · exact g32p_row51_cosetGeneratorBlock_0020 s
  · exact g32p_row51_cosetGeneratorBlock_0021 s
  · exact g32p_row51_cosetGeneratorBlock_0022 s
  · exact g32p_row51_cosetGeneratorBlock_0023 s
  · exact g32p_row51_cosetGeneratorBlock_0024 s
  · exact g32p_row51_cosetGeneratorBlock_0025 s
  · exact g32p_row51_cosetGeneratorBlock_0026 s
  · exact g32p_row51_cosetGeneratorBlock_0027 s
  · exact g32p_row51_cosetGeneratorBlock_0028 s
  · exact g32p_row51_cosetGeneratorBlock_0029 s
  · exact g32p_row51_cosetGeneratorBlock_0030 s
  · exact g32p_row51_cosetGeneratorBlock_0031 s
  · exact g32p_row51_cosetGeneratorBlock_0032 s
  · exact g32p_row51_cosetGeneratorBlock_0033 s
  · exact g32p_row51_cosetGeneratorBlock_0034 s
  · exact g32p_row51_cosetGeneratorBlock_0035 s
  · exact g32p_row51_cosetGeneratorBlock_0036 s
  · exact g32p_row51_cosetGeneratorBlock_0037 s
  · exact g32p_row51_cosetGeneratorBlock_0038 s
  · exact g32p_row51_cosetGeneratorBlock_0039 s
  · exact g32p_row51_cosetGeneratorBlock_0040 s
  · exact g32p_row51_cosetGeneratorBlock_0041 s
  · exact g32p_row51_cosetGeneratorBlock_0042 s
  · exact g32p_row51_cosetGeneratorBlock_0043 s
  · exact g32p_row51_cosetGeneratorBlock_0044 s


theorem g32p_row51_cosetActualStep (s : Fin 4) (i : Fin 720) :
    g32p_word (g32p_archiveWords s) * g32p_row51_cosetActualRepresentatives i =
      g32p_row51_cosetActualRepresentatives (g32p_row51_cosetGeneratorNext s i) *
        (g32p_row51_groupEquiv (g32p_row51_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row51_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row51_cosetActualRepresentatives (g32p_row51_cosetGeneratorNext s i) *
      (g32p_row51_groupEquiv (g32p_row51_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row51_cosetActualRepresentatives_map,
    g32p_row51_cosetActualRepresentatives_map, g32p_row51_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row51_cosetGeneratorStep]

theorem g32p_row51_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row51_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row51_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row51_cosetGeneratorNext
      (fun s i => g32p_row51_groupEquiv (g32p_row51_cosetGeneratorFactor s i))
    exact g32p_row51_cosetActualStep
  · rw [g32p_row51_finiteSupplier_order]
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

theorem g32p_row51_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 0)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 0)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 0) = g32p_row51_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 1)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 1)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 1) = g32p_row51_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 2)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 2)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 2) = g32p_row51_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 3)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 3)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 3) = g32p_row51_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 4)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 4)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 4) = g32p_row51_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 5)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 5)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 5) = g32p_row51_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 6)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 6)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 6) = g32p_row51_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 7)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 7)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 7) = g32p_row51_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 8)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 8)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 8) = g32p_row51_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 9)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 9)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 9) = g32p_row51_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 10)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 10)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 10) = g32p_row51_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 11)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 11)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 11) = g32p_row51_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 12)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 12)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 12) = g32p_row51_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 13)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 13)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 13) = g32p_row51_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 14)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 14)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 14) = g32p_row51_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 15)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 15)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 15) = g32p_row51_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row51_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row51_cosetBranchMatrices 0) (g32p_row51_cosetLengths0 (g32p_finBlockIndex 300 0 r)))
      (g32p_row51_cosetRepresentatives (g32p_row51_cosetRoots0 (g32p_finBlockIndex 300 0 r))) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetRoots0 (g32p_finBlockIndex 300 0 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 (g32p_finBlockIndex 300 0 r))) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 (g32p_finBlockIndex 300 0 r)) = g32p_row51_cosetExponents0 (g32p_finBlockIndex 300 0 r) := by
  fin_cases r
  · exact g32p_row51_cosetMonodromy_0_0000
  · exact g32p_row51_cosetMonodromy_0_0001
  · exact g32p_row51_cosetMonodromy_0_0002
  · exact g32p_row51_cosetMonodromy_0_0003
  · exact g32p_row51_cosetMonodromy_0_0004
  · exact g32p_row51_cosetMonodromy_0_0005
  · exact g32p_row51_cosetMonodromy_0_0006
  · exact g32p_row51_cosetMonodromy_0_0007
  · exact g32p_row51_cosetMonodromy_0_0008
  · exact g32p_row51_cosetMonodromy_0_0009
  · exact g32p_row51_cosetMonodromy_0_0010
  · exact g32p_row51_cosetMonodromy_0_0011
  · exact g32p_row51_cosetMonodromy_0_0012
  · exact g32p_row51_cosetMonodromy_0_0013
  · exact g32p_row51_cosetMonodromy_0_0014
  · exact g32p_row51_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row51_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 16)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 16)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 16) = g32p_row51_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 17)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 17)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 17) = g32p_row51_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 18)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 18)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 18) = g32p_row51_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 19)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 19)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 19) = g32p_row51_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 21)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 20)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 20) = g32p_row51_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 22)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 21)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 21) = g32p_row51_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row51_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 23)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 22)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 22) = g32p_row51_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 24)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 23)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 23) = g32p_row51_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 25)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 24)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 24) = g32p_row51_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 26)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 25)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 25) = g32p_row51_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 27)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 26)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 26) = g32p_row51_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 28)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 27)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 27) = g32p_row51_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 29)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 28)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 28) = g32p_row51_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 30)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 29)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 29) = g32p_row51_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 31)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 30)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 30) = g32p_row51_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row51_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row51_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row51_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives 32)
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 31)) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 31) = g32p_row51_cosetExponents0 31 := by
  decide +kernel

theorem g32p_row51_cosetMonodromyBlock0_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row51_cosetBranchMatrices 0) (g32p_row51_cosetLengths0 (g32p_finBlockIndex 300 1 r)))
      (g32p_row51_cosetRepresentatives (g32p_row51_cosetRoots0 (g32p_finBlockIndex 300 1 r))) =
      HurwitzPrymRex_mmul (g32p_row51_cosetRepresentatives (g32p_row51_cosetRoots0 (g32p_finBlockIndex 300 1 r)))
        (g32p_row51_groupNodes (g32p_row51_cosetMonodromies0 (g32p_finBlockIndex 300 1 r))) ∧
    g32p_row51_characterValues (g32p_row51_cosetMonodromies0 (g32p_finBlockIndex 300 1 r)) = g32p_row51_cosetExponents0 (g32p_finBlockIndex 300 1 r) := by
  fin_cases r
  · exact g32p_row51_cosetMonodromy_0_0016
  · exact g32p_row51_cosetMonodromy_0_0017
  · exact g32p_row51_cosetMonodromy_0_0018
  · exact g32p_row51_cosetMonodromy_0_0019
  · exact g32p_row51_cosetMonodromy_0_0020
  · exact g32p_row51_cosetMonodromy_0_0021
  · exact g32p_row51_cosetMonodromy_0_0022
  · exact g32p_row51_cosetMonodromy_0_0023
  · exact g32p_row51_cosetMonodromy_0_0024
  · exact g32p_row51_cosetMonodromy_0_0025
  · exact g32p_row51_cosetMonodromy_0_0026
  · exact g32p_row51_cosetMonodromy_0_0027
  · exact g32p_row51_cosetMonodromy_0_0028
  · exact g32p_row51_cosetMonodromy_0_0029
  · exact g32p_row51_cosetMonodromy_0_0030
  · exact g32p_row51_cosetMonodromy_0_0031


end HodgeLean.Foundations.Program

end
