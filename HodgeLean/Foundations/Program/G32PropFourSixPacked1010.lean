import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness50CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked1008
import HodgeLean.Foundations.Program.G32PropFourSixPacked1009
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow50
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetWord_0512 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 512) = g32p_row50_cosetRepresentatives 512 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0512 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 512) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 512))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 512)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0512 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 512) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 512))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 512)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0513 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 513) = g32p_row50_cosetRepresentatives 513 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0513 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 513) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 513))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 513)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0513 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 513) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 513))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 513)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0514 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 514) = g32p_row50_cosetRepresentatives 514 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0514 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 514) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 514))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 514)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0514 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 514) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 514))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 514)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0515 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 515) = g32p_row50_cosetRepresentatives 515 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0515 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 515) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 515))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 515)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0515 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 515) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 515))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 515)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0516 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 516) = g32p_row50_cosetRepresentatives 516 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0516 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 516) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 516))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 516)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0516 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 516) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 516))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 516)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0517 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 517) = g32p_row50_cosetRepresentatives 517 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0517 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 517) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 517))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 517)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0517 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 517) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 517))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 517)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0518 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 518) = g32p_row50_cosetRepresentatives 518 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0518 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 518) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 518))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 518)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0518 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 518) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 518))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 518)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0519 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 519) = g32p_row50_cosetRepresentatives 519 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0519 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 519) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 519))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 519)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0519 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 519) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 519))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 519)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0520 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 520) = g32p_row50_cosetRepresentatives 520 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0520 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 520) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 520))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 520)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0520 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 520) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 520))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 520)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0521 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 521) = g32p_row50_cosetRepresentatives 521 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0521 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 521) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 521))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 521)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0521 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 521) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 521))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 521)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0522 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 522) = g32p_row50_cosetRepresentatives 522 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0522 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 522) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 522))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 522)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0522 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 522) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 522))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 522)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0523 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 523) = g32p_row50_cosetRepresentatives 523 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0523 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 523) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 523))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 523)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0523 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 523) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 523))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 523)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0524 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 524) = g32p_row50_cosetRepresentatives 524 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0524 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 524) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 524))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 524)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0524 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 524) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 524))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 524)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0525 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 525) = g32p_row50_cosetRepresentatives 525 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0525 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 525) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 525))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 525)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0525 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 525) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 525))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 525)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0526 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 526) = g32p_row50_cosetRepresentatives 526 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0526 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 526) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 526))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 526)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0526 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 526) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 526))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 526)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0527 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 527) = g32p_row50_cosetRepresentatives 527 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0527 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 527) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 527))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 527)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0527 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 527) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 527))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 527)) := by
  decide +kernel

theorem g32p_row50_cosetWordBlock_0032 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords (g32p_finBlockIndex 640 32 r)) = g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 32 r) := by
  fin_cases r
  · exact g32p_row50_cosetWord_0512
  · exact g32p_row50_cosetWord_0513
  · exact g32p_row50_cosetWord_0514
  · exact g32p_row50_cosetWord_0515
  · exact g32p_row50_cosetWord_0516
  · exact g32p_row50_cosetWord_0517
  · exact g32p_row50_cosetWord_0518
  · exact g32p_row50_cosetWord_0519
  · exact g32p_row50_cosetWord_0520
  · exact g32p_row50_cosetWord_0521
  · exact g32p_row50_cosetWord_0522
  · exact g32p_row50_cosetWord_0523
  · exact g32p_row50_cosetWord_0524
  · exact g32p_row50_cosetWord_0525
  · exact g32p_row50_cosetWord_0526
  · exact g32p_row50_cosetWord_0527

theorem g32p_row50_cosetGeneratorBlock_0032 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 32 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s (g32p_finBlockIndex 640 32 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s (g32p_finBlockIndex 640 32 r))) := by
  fin_cases r
  · exact g32p_row50_cosetGeneratorStep_0512 s
  · exact g32p_row50_cosetGeneratorStep_0513 s
  · exact g32p_row50_cosetGeneratorStep_0514 s
  · exact g32p_row50_cosetGeneratorStep_0515 s
  · exact g32p_row50_cosetGeneratorStep_0516 s
  · exact g32p_row50_cosetGeneratorStep_0517 s
  · exact g32p_row50_cosetGeneratorStep_0518 s
  · exact g32p_row50_cosetGeneratorStep_0519 s
  · exact g32p_row50_cosetGeneratorStep_0520 s
  · exact g32p_row50_cosetGeneratorStep_0521 s
  · exact g32p_row50_cosetGeneratorStep_0522 s
  · exact g32p_row50_cosetGeneratorStep_0523 s
  · exact g32p_row50_cosetGeneratorStep_0524 s
  · exact g32p_row50_cosetGeneratorStep_0525 s
  · exact g32p_row50_cosetGeneratorStep_0526 s
  · exact g32p_row50_cosetGeneratorStep_0527 s

theorem g32p_row50_cosetBranchBlock_0032 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 32 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s (g32p_finBlockIndex 640 32 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s (g32p_finBlockIndex 640 32 r))) := by
  fin_cases r
  · exact g32p_row50_cosetBranchStep_0512 s
  · exact g32p_row50_cosetBranchStep_0513 s
  · exact g32p_row50_cosetBranchStep_0514 s
  · exact g32p_row50_cosetBranchStep_0515 s
  · exact g32p_row50_cosetBranchStep_0516 s
  · exact g32p_row50_cosetBranchStep_0517 s
  · exact g32p_row50_cosetBranchStep_0518 s
  · exact g32p_row50_cosetBranchStep_0519 s
  · exact g32p_row50_cosetBranchStep_0520 s
  · exact g32p_row50_cosetBranchStep_0521 s
  · exact g32p_row50_cosetBranchStep_0522 s
  · exact g32p_row50_cosetBranchStep_0523 s
  · exact g32p_row50_cosetBranchStep_0524 s
  · exact g32p_row50_cosetBranchStep_0525 s
  · exact g32p_row50_cosetBranchStep_0526 s
  · exact g32p_row50_cosetBranchStep_0527 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetWord_0528 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 528) = g32p_row50_cosetRepresentatives 528 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0528 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 528) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 528))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 528)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0528 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 528) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 528))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 528)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0529 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 529) = g32p_row50_cosetRepresentatives 529 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0529 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 529) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 529))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 529)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0529 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 529) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 529))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 529)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0530 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 530) = g32p_row50_cosetRepresentatives 530 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0530 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 530) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 530))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 530)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0530 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 530) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 530))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 530)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0531 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 531) = g32p_row50_cosetRepresentatives 531 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0531 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 531) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 531))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 531)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0531 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 531) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 531))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 531)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0532 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 532) = g32p_row50_cosetRepresentatives 532 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0532 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 532) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 532))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 532)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0532 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 532) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 532))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 532)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0533 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 533) = g32p_row50_cosetRepresentatives 533 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0533 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 533) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 533))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 533)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0533 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 533) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 533))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 533)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0534 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 534) = g32p_row50_cosetRepresentatives 534 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0534 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 534) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 534))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 534)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0534 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 534) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 534))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 534)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0535 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 535) = g32p_row50_cosetRepresentatives 535 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0535 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 535) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 535))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 535)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0535 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 535) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 535))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 535)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0536 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 536) = g32p_row50_cosetRepresentatives 536 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0536 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 536) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 536))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 536)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0536 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 536) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 536))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 536)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0537 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 537) = g32p_row50_cosetRepresentatives 537 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0537 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 537) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 537))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 537)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0537 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 537) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 537))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 537)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0538 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 538) = g32p_row50_cosetRepresentatives 538 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0538 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 538) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 538))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 538)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0538 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 538) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 538))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 538)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0539 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 539) = g32p_row50_cosetRepresentatives 539 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0539 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 539) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 539))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 539)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0539 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 539) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 539))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 539)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0540 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 540) = g32p_row50_cosetRepresentatives 540 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0540 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 540) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 540))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 540)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0540 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 540) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 540))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 540)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0541 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 541) = g32p_row50_cosetRepresentatives 541 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0541 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 541) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 541))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 541)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0541 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 541) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 541))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 541)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0542 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 542) = g32p_row50_cosetRepresentatives 542 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0542 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 542) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 542))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 542)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0542 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 542) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 542))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 542)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0543 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 543) = g32p_row50_cosetRepresentatives 543 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0543 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 543) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 543))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 543)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0543 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 543) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 543))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 543)) := by
  decide +kernel

theorem g32p_row50_cosetWordBlock_0033 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords (g32p_finBlockIndex 640 33 r)) = g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 33 r) := by
  fin_cases r
  · exact g32p_row50_cosetWord_0528
  · exact g32p_row50_cosetWord_0529
  · exact g32p_row50_cosetWord_0530
  · exact g32p_row50_cosetWord_0531
  · exact g32p_row50_cosetWord_0532
  · exact g32p_row50_cosetWord_0533
  · exact g32p_row50_cosetWord_0534
  · exact g32p_row50_cosetWord_0535
  · exact g32p_row50_cosetWord_0536
  · exact g32p_row50_cosetWord_0537
  · exact g32p_row50_cosetWord_0538
  · exact g32p_row50_cosetWord_0539
  · exact g32p_row50_cosetWord_0540
  · exact g32p_row50_cosetWord_0541
  · exact g32p_row50_cosetWord_0542
  · exact g32p_row50_cosetWord_0543

theorem g32p_row50_cosetGeneratorBlock_0033 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 33 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s (g32p_finBlockIndex 640 33 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s (g32p_finBlockIndex 640 33 r))) := by
  fin_cases r
  · exact g32p_row50_cosetGeneratorStep_0528 s
  · exact g32p_row50_cosetGeneratorStep_0529 s
  · exact g32p_row50_cosetGeneratorStep_0530 s
  · exact g32p_row50_cosetGeneratorStep_0531 s
  · exact g32p_row50_cosetGeneratorStep_0532 s
  · exact g32p_row50_cosetGeneratorStep_0533 s
  · exact g32p_row50_cosetGeneratorStep_0534 s
  · exact g32p_row50_cosetGeneratorStep_0535 s
  · exact g32p_row50_cosetGeneratorStep_0536 s
  · exact g32p_row50_cosetGeneratorStep_0537 s
  · exact g32p_row50_cosetGeneratorStep_0538 s
  · exact g32p_row50_cosetGeneratorStep_0539 s
  · exact g32p_row50_cosetGeneratorStep_0540 s
  · exact g32p_row50_cosetGeneratorStep_0541 s
  · exact g32p_row50_cosetGeneratorStep_0542 s
  · exact g32p_row50_cosetGeneratorStep_0543 s

theorem g32p_row50_cosetBranchBlock_0033 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 33 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s (g32p_finBlockIndex 640 33 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s (g32p_finBlockIndex 640 33 r))) := by
  fin_cases r
  · exact g32p_row50_cosetBranchStep_0528 s
  · exact g32p_row50_cosetBranchStep_0529 s
  · exact g32p_row50_cosetBranchStep_0530 s
  · exact g32p_row50_cosetBranchStep_0531 s
  · exact g32p_row50_cosetBranchStep_0532 s
  · exact g32p_row50_cosetBranchStep_0533 s
  · exact g32p_row50_cosetBranchStep_0534 s
  · exact g32p_row50_cosetBranchStep_0535 s
  · exact g32p_row50_cosetBranchStep_0536 s
  · exact g32p_row50_cosetBranchStep_0537 s
  · exact g32p_row50_cosetBranchStep_0538 s
  · exact g32p_row50_cosetBranchStep_0539 s
  · exact g32p_row50_cosetBranchStep_0540 s
  · exact g32p_row50_cosetBranchStep_0541 s
  · exact g32p_row50_cosetBranchStep_0542 s
  · exact g32p_row50_cosetBranchStep_0543 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetWord_0544 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 544) = g32p_row50_cosetRepresentatives 544 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0544 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 544) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 544))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 544)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0544 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 544) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 544))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 544)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0545 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 545) = g32p_row50_cosetRepresentatives 545 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0545 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 545) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 545))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 545)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0545 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 545) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 545))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 545)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0546 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 546) = g32p_row50_cosetRepresentatives 546 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0546 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 546) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 546))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 546)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0546 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 546) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 546))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 546)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0547 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 547) = g32p_row50_cosetRepresentatives 547 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0547 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 547) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 547))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 547)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0547 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 547) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 547))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 547)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0548 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 548) = g32p_row50_cosetRepresentatives 548 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0548 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 548) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 548))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 548)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0548 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 548) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 548))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 548)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0549 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 549) = g32p_row50_cosetRepresentatives 549 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0549 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 549) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 549))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 549)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0549 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 549) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 549))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 549)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0550 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 550) = g32p_row50_cosetRepresentatives 550 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0550 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 550) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 550))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 550)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0550 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 550) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 550))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 550)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0551 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 551) = g32p_row50_cosetRepresentatives 551 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0551 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 551) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 551))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 551)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0551 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 551) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 551))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 551)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0552 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 552) = g32p_row50_cosetRepresentatives 552 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0552 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 552) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 552))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 552)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0552 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 552) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 552))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 552)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0553 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 553) = g32p_row50_cosetRepresentatives 553 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0553 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 553) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 553))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 553)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0553 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 553) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 553))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 553)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0554 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 554) = g32p_row50_cosetRepresentatives 554 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0554 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 554) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 554))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 554)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0554 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 554) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 554))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 554)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0555 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 555) = g32p_row50_cosetRepresentatives 555 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0555 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 555) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 555))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 555)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0555 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 555) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 555))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 555)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0556 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 556) = g32p_row50_cosetRepresentatives 556 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0556 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 556) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 556))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 556)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0556 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 556) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 556))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 556)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0557 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 557) = g32p_row50_cosetRepresentatives 557 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0557 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 557) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 557))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 557)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0557 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 557) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 557))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 557)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0558 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 558) = g32p_row50_cosetRepresentatives 558 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0558 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 558) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 558))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 558)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0558 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 558) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 558))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 558)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0559 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 559) = g32p_row50_cosetRepresentatives 559 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0559 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 559) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 559))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 559)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0559 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 559) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 559))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 559)) := by
  decide +kernel

theorem g32p_row50_cosetWordBlock_0034 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords (g32p_finBlockIndex 640 34 r)) = g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 34 r) := by
  fin_cases r
  · exact g32p_row50_cosetWord_0544
  · exact g32p_row50_cosetWord_0545
  · exact g32p_row50_cosetWord_0546
  · exact g32p_row50_cosetWord_0547
  · exact g32p_row50_cosetWord_0548
  · exact g32p_row50_cosetWord_0549
  · exact g32p_row50_cosetWord_0550
  · exact g32p_row50_cosetWord_0551
  · exact g32p_row50_cosetWord_0552
  · exact g32p_row50_cosetWord_0553
  · exact g32p_row50_cosetWord_0554
  · exact g32p_row50_cosetWord_0555
  · exact g32p_row50_cosetWord_0556
  · exact g32p_row50_cosetWord_0557
  · exact g32p_row50_cosetWord_0558
  · exact g32p_row50_cosetWord_0559

theorem g32p_row50_cosetGeneratorBlock_0034 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 34 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s (g32p_finBlockIndex 640 34 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s (g32p_finBlockIndex 640 34 r))) := by
  fin_cases r
  · exact g32p_row50_cosetGeneratorStep_0544 s
  · exact g32p_row50_cosetGeneratorStep_0545 s
  · exact g32p_row50_cosetGeneratorStep_0546 s
  · exact g32p_row50_cosetGeneratorStep_0547 s
  · exact g32p_row50_cosetGeneratorStep_0548 s
  · exact g32p_row50_cosetGeneratorStep_0549 s
  · exact g32p_row50_cosetGeneratorStep_0550 s
  · exact g32p_row50_cosetGeneratorStep_0551 s
  · exact g32p_row50_cosetGeneratorStep_0552 s
  · exact g32p_row50_cosetGeneratorStep_0553 s
  · exact g32p_row50_cosetGeneratorStep_0554 s
  · exact g32p_row50_cosetGeneratorStep_0555 s
  · exact g32p_row50_cosetGeneratorStep_0556 s
  · exact g32p_row50_cosetGeneratorStep_0557 s
  · exact g32p_row50_cosetGeneratorStep_0558 s
  · exact g32p_row50_cosetGeneratorStep_0559 s

theorem g32p_row50_cosetBranchBlock_0034 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 34 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s (g32p_finBlockIndex 640 34 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s (g32p_finBlockIndex 640 34 r))) := by
  fin_cases r
  · exact g32p_row50_cosetBranchStep_0544 s
  · exact g32p_row50_cosetBranchStep_0545 s
  · exact g32p_row50_cosetBranchStep_0546 s
  · exact g32p_row50_cosetBranchStep_0547 s
  · exact g32p_row50_cosetBranchStep_0548 s
  · exact g32p_row50_cosetBranchStep_0549 s
  · exact g32p_row50_cosetBranchStep_0550 s
  · exact g32p_row50_cosetBranchStep_0551 s
  · exact g32p_row50_cosetBranchStep_0552 s
  · exact g32p_row50_cosetBranchStep_0553 s
  · exact g32p_row50_cosetBranchStep_0554 s
  · exact g32p_row50_cosetBranchStep_0555 s
  · exact g32p_row50_cosetBranchStep_0556 s
  · exact g32p_row50_cosetBranchStep_0557 s
  · exact g32p_row50_cosetBranchStep_0558 s
  · exact g32p_row50_cosetBranchStep_0559 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetWord_0560 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 560) = g32p_row50_cosetRepresentatives 560 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0560 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 560) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 560))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 560)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0560 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 560) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 560))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 560)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0561 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 561) = g32p_row50_cosetRepresentatives 561 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0561 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 561) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 561))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 561)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0561 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 561) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 561))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 561)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0562 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 562) = g32p_row50_cosetRepresentatives 562 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0562 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 562) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 562))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 562)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0562 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 562) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 562))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 562)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0563 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 563) = g32p_row50_cosetRepresentatives 563 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0563 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 563) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 563))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 563)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0563 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 563) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 563))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 563)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0564 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 564) = g32p_row50_cosetRepresentatives 564 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0564 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 564) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 564))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 564)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0564 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 564) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 564))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 564)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0565 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 565) = g32p_row50_cosetRepresentatives 565 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0565 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 565) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 565))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 565)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0565 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 565) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 565))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 565)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0566 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 566) = g32p_row50_cosetRepresentatives 566 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0566 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 566) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 566))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 566)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0566 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 566) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 566))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 566)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0567 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 567) = g32p_row50_cosetRepresentatives 567 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0567 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 567) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 567))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 567)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0567 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 567) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 567))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 567)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0568 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 568) = g32p_row50_cosetRepresentatives 568 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0568 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 568) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 568))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 568)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0568 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 568) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 568))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 568)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0569 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 569) = g32p_row50_cosetRepresentatives 569 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0569 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 569) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 569))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 569)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0569 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 569) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 569))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 569)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0570 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 570) = g32p_row50_cosetRepresentatives 570 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0570 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 570) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 570))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 570)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0570 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 570) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 570))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 570)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0571 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 571) = g32p_row50_cosetRepresentatives 571 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0571 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 571) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 571))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 571)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0571 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 571) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 571))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 571)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0572 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 572) = g32p_row50_cosetRepresentatives 572 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0572 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 572) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 572))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 572)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0572 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 572) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 572))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 572)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0573 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 573) = g32p_row50_cosetRepresentatives 573 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0573 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 573) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 573))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 573)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0573 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 573) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 573))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 573)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0574 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 574) = g32p_row50_cosetRepresentatives 574 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0574 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 574) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 574))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 574)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0574 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 574) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 574))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 574)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0575 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 575) = g32p_row50_cosetRepresentatives 575 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0575 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 575) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 575))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 575)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0575 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 575) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 575))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 575)) := by
  decide +kernel

theorem g32p_row50_cosetWordBlock_0035 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords (g32p_finBlockIndex 640 35 r)) = g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 35 r) := by
  fin_cases r
  · exact g32p_row50_cosetWord_0560
  · exact g32p_row50_cosetWord_0561
  · exact g32p_row50_cosetWord_0562
  · exact g32p_row50_cosetWord_0563
  · exact g32p_row50_cosetWord_0564
  · exact g32p_row50_cosetWord_0565
  · exact g32p_row50_cosetWord_0566
  · exact g32p_row50_cosetWord_0567
  · exact g32p_row50_cosetWord_0568
  · exact g32p_row50_cosetWord_0569
  · exact g32p_row50_cosetWord_0570
  · exact g32p_row50_cosetWord_0571
  · exact g32p_row50_cosetWord_0572
  · exact g32p_row50_cosetWord_0573
  · exact g32p_row50_cosetWord_0574
  · exact g32p_row50_cosetWord_0575

theorem g32p_row50_cosetGeneratorBlock_0035 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 35 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s (g32p_finBlockIndex 640 35 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s (g32p_finBlockIndex 640 35 r))) := by
  fin_cases r
  · exact g32p_row50_cosetGeneratorStep_0560 s
  · exact g32p_row50_cosetGeneratorStep_0561 s
  · exact g32p_row50_cosetGeneratorStep_0562 s
  · exact g32p_row50_cosetGeneratorStep_0563 s
  · exact g32p_row50_cosetGeneratorStep_0564 s
  · exact g32p_row50_cosetGeneratorStep_0565 s
  · exact g32p_row50_cosetGeneratorStep_0566 s
  · exact g32p_row50_cosetGeneratorStep_0567 s
  · exact g32p_row50_cosetGeneratorStep_0568 s
  · exact g32p_row50_cosetGeneratorStep_0569 s
  · exact g32p_row50_cosetGeneratorStep_0570 s
  · exact g32p_row50_cosetGeneratorStep_0571 s
  · exact g32p_row50_cosetGeneratorStep_0572 s
  · exact g32p_row50_cosetGeneratorStep_0573 s
  · exact g32p_row50_cosetGeneratorStep_0574 s
  · exact g32p_row50_cosetGeneratorStep_0575 s

theorem g32p_row50_cosetBranchBlock_0035 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 35 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s (g32p_finBlockIndex 640 35 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s (g32p_finBlockIndex 640 35 r))) := by
  fin_cases r
  · exact g32p_row50_cosetBranchStep_0560 s
  · exact g32p_row50_cosetBranchStep_0561 s
  · exact g32p_row50_cosetBranchStep_0562 s
  · exact g32p_row50_cosetBranchStep_0563 s
  · exact g32p_row50_cosetBranchStep_0564 s
  · exact g32p_row50_cosetBranchStep_0565 s
  · exact g32p_row50_cosetBranchStep_0566 s
  · exact g32p_row50_cosetBranchStep_0567 s
  · exact g32p_row50_cosetBranchStep_0568 s
  · exact g32p_row50_cosetBranchStep_0569 s
  · exact g32p_row50_cosetBranchStep_0570 s
  · exact g32p_row50_cosetBranchStep_0571 s
  · exact g32p_row50_cosetBranchStep_0572 s
  · exact g32p_row50_cosetBranchStep_0573 s
  · exact g32p_row50_cosetBranchStep_0574 s
  · exact g32p_row50_cosetBranchStep_0575 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetWord_0576 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 576) = g32p_row50_cosetRepresentatives 576 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0576 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 576) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 576))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 576)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0576 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 576) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 576))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 576)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0577 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 577) = g32p_row50_cosetRepresentatives 577 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0577 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 577) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 577))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 577)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0577 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 577) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 577))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 577)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0578 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 578) = g32p_row50_cosetRepresentatives 578 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0578 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 578) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 578))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 578)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0578 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 578) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 578))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 578)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0579 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 579) = g32p_row50_cosetRepresentatives 579 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0579 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 579) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 579))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 579)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0579 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 579) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 579))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 579)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0580 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 580) = g32p_row50_cosetRepresentatives 580 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0580 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 580) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 580))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 580)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0580 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 580) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 580))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 580)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0581 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 581) = g32p_row50_cosetRepresentatives 581 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0581 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 581) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 581))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 581)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0581 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 581) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 581))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 581)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0582 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 582) = g32p_row50_cosetRepresentatives 582 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0582 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 582) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 582))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 582)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0582 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 582) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 582))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 582)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0583 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 583) = g32p_row50_cosetRepresentatives 583 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0583 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 583) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 583))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 583)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0583 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 583) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 583))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 583)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0584 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 584) = g32p_row50_cosetRepresentatives 584 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0584 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 584) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 584))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 584)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0584 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 584) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 584))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 584)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0585 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 585) = g32p_row50_cosetRepresentatives 585 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0585 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 585) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 585))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 585)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0585 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 585) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 585))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 585)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0586 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 586) = g32p_row50_cosetRepresentatives 586 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0586 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 586) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 586))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 586)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0586 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 586) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 586))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 586)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0587 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 587) = g32p_row50_cosetRepresentatives 587 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0587 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 587) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 587))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 587)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0587 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 587) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 587))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 587)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0588 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 588) = g32p_row50_cosetRepresentatives 588 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0588 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 588) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 588))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 588)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0588 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 588) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 588))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 588)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0589 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 589) = g32p_row50_cosetRepresentatives 589 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0589 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 589) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 589))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 589)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0589 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 589) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 589))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 589)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0590 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 590) = g32p_row50_cosetRepresentatives 590 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0590 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 590) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 590))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 590)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0590 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 590) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 590))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 590)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0591 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 591) = g32p_row50_cosetRepresentatives 591 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0591 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 591) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 591))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 591)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0591 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 591) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 591))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 591)) := by
  decide +kernel

theorem g32p_row50_cosetWordBlock_0036 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords (g32p_finBlockIndex 640 36 r)) = g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 36 r) := by
  fin_cases r
  · exact g32p_row50_cosetWord_0576
  · exact g32p_row50_cosetWord_0577
  · exact g32p_row50_cosetWord_0578
  · exact g32p_row50_cosetWord_0579
  · exact g32p_row50_cosetWord_0580
  · exact g32p_row50_cosetWord_0581
  · exact g32p_row50_cosetWord_0582
  · exact g32p_row50_cosetWord_0583
  · exact g32p_row50_cosetWord_0584
  · exact g32p_row50_cosetWord_0585
  · exact g32p_row50_cosetWord_0586
  · exact g32p_row50_cosetWord_0587
  · exact g32p_row50_cosetWord_0588
  · exact g32p_row50_cosetWord_0589
  · exact g32p_row50_cosetWord_0590
  · exact g32p_row50_cosetWord_0591

theorem g32p_row50_cosetGeneratorBlock_0036 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 36 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s (g32p_finBlockIndex 640 36 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s (g32p_finBlockIndex 640 36 r))) := by
  fin_cases r
  · exact g32p_row50_cosetGeneratorStep_0576 s
  · exact g32p_row50_cosetGeneratorStep_0577 s
  · exact g32p_row50_cosetGeneratorStep_0578 s
  · exact g32p_row50_cosetGeneratorStep_0579 s
  · exact g32p_row50_cosetGeneratorStep_0580 s
  · exact g32p_row50_cosetGeneratorStep_0581 s
  · exact g32p_row50_cosetGeneratorStep_0582 s
  · exact g32p_row50_cosetGeneratorStep_0583 s
  · exact g32p_row50_cosetGeneratorStep_0584 s
  · exact g32p_row50_cosetGeneratorStep_0585 s
  · exact g32p_row50_cosetGeneratorStep_0586 s
  · exact g32p_row50_cosetGeneratorStep_0587 s
  · exact g32p_row50_cosetGeneratorStep_0588 s
  · exact g32p_row50_cosetGeneratorStep_0589 s
  · exact g32p_row50_cosetGeneratorStep_0590 s
  · exact g32p_row50_cosetGeneratorStep_0591 s

theorem g32p_row50_cosetBranchBlock_0036 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 36 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s (g32p_finBlockIndex 640 36 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s (g32p_finBlockIndex 640 36 r))) := by
  fin_cases r
  · exact g32p_row50_cosetBranchStep_0576 s
  · exact g32p_row50_cosetBranchStep_0577 s
  · exact g32p_row50_cosetBranchStep_0578 s
  · exact g32p_row50_cosetBranchStep_0579 s
  · exact g32p_row50_cosetBranchStep_0580 s
  · exact g32p_row50_cosetBranchStep_0581 s
  · exact g32p_row50_cosetBranchStep_0582 s
  · exact g32p_row50_cosetBranchStep_0583 s
  · exact g32p_row50_cosetBranchStep_0584 s
  · exact g32p_row50_cosetBranchStep_0585 s
  · exact g32p_row50_cosetBranchStep_0586 s
  · exact g32p_row50_cosetBranchStep_0587 s
  · exact g32p_row50_cosetBranchStep_0588 s
  · exact g32p_row50_cosetBranchStep_0589 s
  · exact g32p_row50_cosetBranchStep_0590 s
  · exact g32p_row50_cosetBranchStep_0591 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetWord_0592 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 592) = g32p_row50_cosetRepresentatives 592 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0592 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 592) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 592))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 592)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0592 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 592) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 592))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 592)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0593 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 593) = g32p_row50_cosetRepresentatives 593 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0593 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 593) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 593))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 593)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0593 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 593) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 593))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 593)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0594 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 594) = g32p_row50_cosetRepresentatives 594 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0594 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 594) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 594))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 594)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0594 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 594) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 594))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 594)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0595 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 595) = g32p_row50_cosetRepresentatives 595 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0595 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 595) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 595))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 595)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0595 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 595) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 595))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 595)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0596 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 596) = g32p_row50_cosetRepresentatives 596 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0596 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 596) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 596))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 596)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0596 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 596) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 596))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 596)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0597 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 597) = g32p_row50_cosetRepresentatives 597 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0597 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 597) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 597))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 597)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0597 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 597) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 597))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 597)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0598 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 598) = g32p_row50_cosetRepresentatives 598 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0598 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 598) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 598))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 598)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0598 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 598) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 598))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 598)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0599 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 599) = g32p_row50_cosetRepresentatives 599 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0599 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 599) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 599))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 599)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0599 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 599) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 599))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 599)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0600 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 600) = g32p_row50_cosetRepresentatives 600 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0600 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 600) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 600))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 600)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0600 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 600) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 600))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 600)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0601 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 601) = g32p_row50_cosetRepresentatives 601 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0601 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 601) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 601))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 601)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0601 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 601) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 601))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 601)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0602 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 602) = g32p_row50_cosetRepresentatives 602 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0602 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 602) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 602))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 602)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0602 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 602) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 602))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 602)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0603 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 603) = g32p_row50_cosetRepresentatives 603 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0603 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 603) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 603))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 603)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0603 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 603) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 603))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 603)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0604 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 604) = g32p_row50_cosetRepresentatives 604 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0604 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 604) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 604))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 604)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0604 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 604) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 604))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 604)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0605 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 605) = g32p_row50_cosetRepresentatives 605 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0605 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 605) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 605))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 605)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0605 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 605) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 605))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 605)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0606 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 606) = g32p_row50_cosetRepresentatives 606 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0606 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 606) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 606))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 606)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0606 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 606) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 606))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 606)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0607 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 607) = g32p_row50_cosetRepresentatives 607 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0607 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 607) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 607))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 607)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0607 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 607) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 607))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 607)) := by
  decide +kernel

theorem g32p_row50_cosetWordBlock_0037 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords (g32p_finBlockIndex 640 37 r)) = g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 37 r) := by
  fin_cases r
  · exact g32p_row50_cosetWord_0592
  · exact g32p_row50_cosetWord_0593
  · exact g32p_row50_cosetWord_0594
  · exact g32p_row50_cosetWord_0595
  · exact g32p_row50_cosetWord_0596
  · exact g32p_row50_cosetWord_0597
  · exact g32p_row50_cosetWord_0598
  · exact g32p_row50_cosetWord_0599
  · exact g32p_row50_cosetWord_0600
  · exact g32p_row50_cosetWord_0601
  · exact g32p_row50_cosetWord_0602
  · exact g32p_row50_cosetWord_0603
  · exact g32p_row50_cosetWord_0604
  · exact g32p_row50_cosetWord_0605
  · exact g32p_row50_cosetWord_0606
  · exact g32p_row50_cosetWord_0607

theorem g32p_row50_cosetGeneratorBlock_0037 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 37 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s (g32p_finBlockIndex 640 37 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s (g32p_finBlockIndex 640 37 r))) := by
  fin_cases r
  · exact g32p_row50_cosetGeneratorStep_0592 s
  · exact g32p_row50_cosetGeneratorStep_0593 s
  · exact g32p_row50_cosetGeneratorStep_0594 s
  · exact g32p_row50_cosetGeneratorStep_0595 s
  · exact g32p_row50_cosetGeneratorStep_0596 s
  · exact g32p_row50_cosetGeneratorStep_0597 s
  · exact g32p_row50_cosetGeneratorStep_0598 s
  · exact g32p_row50_cosetGeneratorStep_0599 s
  · exact g32p_row50_cosetGeneratorStep_0600 s
  · exact g32p_row50_cosetGeneratorStep_0601 s
  · exact g32p_row50_cosetGeneratorStep_0602 s
  · exact g32p_row50_cosetGeneratorStep_0603 s
  · exact g32p_row50_cosetGeneratorStep_0604 s
  · exact g32p_row50_cosetGeneratorStep_0605 s
  · exact g32p_row50_cosetGeneratorStep_0606 s
  · exact g32p_row50_cosetGeneratorStep_0607 s

theorem g32p_row50_cosetBranchBlock_0037 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 37 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s (g32p_finBlockIndex 640 37 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s (g32p_finBlockIndex 640 37 r))) := by
  fin_cases r
  · exact g32p_row50_cosetBranchStep_0592 s
  · exact g32p_row50_cosetBranchStep_0593 s
  · exact g32p_row50_cosetBranchStep_0594 s
  · exact g32p_row50_cosetBranchStep_0595 s
  · exact g32p_row50_cosetBranchStep_0596 s
  · exact g32p_row50_cosetBranchStep_0597 s
  · exact g32p_row50_cosetBranchStep_0598 s
  · exact g32p_row50_cosetBranchStep_0599 s
  · exact g32p_row50_cosetBranchStep_0600 s
  · exact g32p_row50_cosetBranchStep_0601 s
  · exact g32p_row50_cosetBranchStep_0602 s
  · exact g32p_row50_cosetBranchStep_0603 s
  · exact g32p_row50_cosetBranchStep_0604 s
  · exact g32p_row50_cosetBranchStep_0605 s
  · exact g32p_row50_cosetBranchStep_0606 s
  · exact g32p_row50_cosetBranchStep_0607 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetWord_0608 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 608) = g32p_row50_cosetRepresentatives 608 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0608 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 608) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 608))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 608)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0608 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 608) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 608))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 608)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0609 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 609) = g32p_row50_cosetRepresentatives 609 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0609 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 609) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 609))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 609)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0609 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 609) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 609))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 609)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0610 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 610) = g32p_row50_cosetRepresentatives 610 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0610 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 610) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 610))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 610)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0610 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 610) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 610))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 610)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0611 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 611) = g32p_row50_cosetRepresentatives 611 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0611 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 611) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 611))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 611)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0611 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 611) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 611))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 611)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0612 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 612) = g32p_row50_cosetRepresentatives 612 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0612 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 612) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 612))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 612)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0612 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 612) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 612))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 612)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0613 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 613) = g32p_row50_cosetRepresentatives 613 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0613 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 613) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 613))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 613)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0613 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 613) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 613))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 613)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0614 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 614) = g32p_row50_cosetRepresentatives 614 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0614 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 614) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 614))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 614)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0614 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 614) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 614))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 614)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0615 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 615) = g32p_row50_cosetRepresentatives 615 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0615 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 615) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 615))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 615)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0615 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 615) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 615))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 615)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0616 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 616) = g32p_row50_cosetRepresentatives 616 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0616 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 616) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 616))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 616)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0616 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 616) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 616))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 616)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0617 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 617) = g32p_row50_cosetRepresentatives 617 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0617 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 617) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 617))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 617)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0617 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 617) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 617))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 617)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0618 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 618) = g32p_row50_cosetRepresentatives 618 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0618 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 618) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 618))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 618)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0618 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 618) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 618))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 618)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0619 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 619) = g32p_row50_cosetRepresentatives 619 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0619 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 619) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 619))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 619)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0619 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 619) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 619))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 619)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0620 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 620) = g32p_row50_cosetRepresentatives 620 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0620 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 620) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 620))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 620)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0620 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 620) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 620))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 620)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0621 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 621) = g32p_row50_cosetRepresentatives 621 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0621 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 621) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 621))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 621)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0621 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 621) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 621))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 621)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0622 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 622) = g32p_row50_cosetRepresentatives 622 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0622 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 622) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 622))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 622)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0622 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 622) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 622))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 622)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0623 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 623) = g32p_row50_cosetRepresentatives 623 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0623 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 623) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 623))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 623)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0623 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 623) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 623))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 623)) := by
  decide +kernel

theorem g32p_row50_cosetWordBlock_0038 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords (g32p_finBlockIndex 640 38 r)) = g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 38 r) := by
  fin_cases r
  · exact g32p_row50_cosetWord_0608
  · exact g32p_row50_cosetWord_0609
  · exact g32p_row50_cosetWord_0610
  · exact g32p_row50_cosetWord_0611
  · exact g32p_row50_cosetWord_0612
  · exact g32p_row50_cosetWord_0613
  · exact g32p_row50_cosetWord_0614
  · exact g32p_row50_cosetWord_0615
  · exact g32p_row50_cosetWord_0616
  · exact g32p_row50_cosetWord_0617
  · exact g32p_row50_cosetWord_0618
  · exact g32p_row50_cosetWord_0619
  · exact g32p_row50_cosetWord_0620
  · exact g32p_row50_cosetWord_0621
  · exact g32p_row50_cosetWord_0622
  · exact g32p_row50_cosetWord_0623

theorem g32p_row50_cosetGeneratorBlock_0038 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 38 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s (g32p_finBlockIndex 640 38 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s (g32p_finBlockIndex 640 38 r))) := by
  fin_cases r
  · exact g32p_row50_cosetGeneratorStep_0608 s
  · exact g32p_row50_cosetGeneratorStep_0609 s
  · exact g32p_row50_cosetGeneratorStep_0610 s
  · exact g32p_row50_cosetGeneratorStep_0611 s
  · exact g32p_row50_cosetGeneratorStep_0612 s
  · exact g32p_row50_cosetGeneratorStep_0613 s
  · exact g32p_row50_cosetGeneratorStep_0614 s
  · exact g32p_row50_cosetGeneratorStep_0615 s
  · exact g32p_row50_cosetGeneratorStep_0616 s
  · exact g32p_row50_cosetGeneratorStep_0617 s
  · exact g32p_row50_cosetGeneratorStep_0618 s
  · exact g32p_row50_cosetGeneratorStep_0619 s
  · exact g32p_row50_cosetGeneratorStep_0620 s
  · exact g32p_row50_cosetGeneratorStep_0621 s
  · exact g32p_row50_cosetGeneratorStep_0622 s
  · exact g32p_row50_cosetGeneratorStep_0623 s

theorem g32p_row50_cosetBranchBlock_0038 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 38 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s (g32p_finBlockIndex 640 38 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s (g32p_finBlockIndex 640 38 r))) := by
  fin_cases r
  · exact g32p_row50_cosetBranchStep_0608 s
  · exact g32p_row50_cosetBranchStep_0609 s
  · exact g32p_row50_cosetBranchStep_0610 s
  · exact g32p_row50_cosetBranchStep_0611 s
  · exact g32p_row50_cosetBranchStep_0612 s
  · exact g32p_row50_cosetBranchStep_0613 s
  · exact g32p_row50_cosetBranchStep_0614 s
  · exact g32p_row50_cosetBranchStep_0615 s
  · exact g32p_row50_cosetBranchStep_0616 s
  · exact g32p_row50_cosetBranchStep_0617 s
  · exact g32p_row50_cosetBranchStep_0618 s
  · exact g32p_row50_cosetBranchStep_0619 s
  · exact g32p_row50_cosetBranchStep_0620 s
  · exact g32p_row50_cosetBranchStep_0621 s
  · exact g32p_row50_cosetBranchStep_0622 s
  · exact g32p_row50_cosetBranchStep_0623 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetWord_0624 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 624) = g32p_row50_cosetRepresentatives 624 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0624 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 624) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 624))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 624)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0624 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 624) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 624))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 624)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0625 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 625) = g32p_row50_cosetRepresentatives 625 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0625 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 625) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 625))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 625)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0625 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 625) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 625))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 625)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0626 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 626) = g32p_row50_cosetRepresentatives 626 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0626 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 626) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 626))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 626)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0626 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 626) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 626))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 626)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0627 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 627) = g32p_row50_cosetRepresentatives 627 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0627 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 627) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 627))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 627)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0627 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 627) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 627))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 627)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0628 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 628) = g32p_row50_cosetRepresentatives 628 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0628 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 628) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 628))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 628)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0628 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 628) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 628))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 628)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0629 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 629) = g32p_row50_cosetRepresentatives 629 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0629 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 629) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 629))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 629)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0629 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 629) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 629))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 629)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0630 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 630) = g32p_row50_cosetRepresentatives 630 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0630 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 630) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 630))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 630)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0630 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 630) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 630))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 630)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0631 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 631) = g32p_row50_cosetRepresentatives 631 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0631 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 631) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 631))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 631)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0631 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 631) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 631))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 631)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0632 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 632) = g32p_row50_cosetRepresentatives 632 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0632 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 632) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 632))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 632)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0632 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 632) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 632))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 632)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0633 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 633) = g32p_row50_cosetRepresentatives 633 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0633 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 633) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 633))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 633)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0633 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 633) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 633))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 633)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0634 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 634) = g32p_row50_cosetRepresentatives 634 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0634 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 634) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 634))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 634)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0634 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 634) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 634))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 634)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0635 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 635) = g32p_row50_cosetRepresentatives 635 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0635 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 635) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 635))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 635)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0635 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 635) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 635))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 635)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0636 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 636) = g32p_row50_cosetRepresentatives 636 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0636 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 636) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 636))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 636)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0636 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 636) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 636))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 636)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0637 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 637) = g32p_row50_cosetRepresentatives 637 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0637 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 637) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 637))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 637)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0637 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 637) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 637))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 637)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0638 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 638) = g32p_row50_cosetRepresentatives 638 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0638 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 638) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 638))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 638)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0638 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 638) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 638))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 638)) := by
  decide +kernel

theorem g32p_row50_cosetWord_0639 :
    g32p_archiveIntegralWord (g32p_row50_cosetWords 639) = g32p_row50_cosetRepresentatives 639 := by
  decide +kernel

theorem g32p_row50_cosetGeneratorStep_0639 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives 639) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s 639))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s 639)) := by
  decide +kernel

theorem g32p_row50_cosetBranchStep_0639 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives 639) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s 639))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s 639)) := by
  decide +kernel

theorem g32p_row50_cosetWordBlock_0039 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords (g32p_finBlockIndex 640 39 r)) = g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 39 r) := by
  fin_cases r
  · exact g32p_row50_cosetWord_0624
  · exact g32p_row50_cosetWord_0625
  · exact g32p_row50_cosetWord_0626
  · exact g32p_row50_cosetWord_0627
  · exact g32p_row50_cosetWord_0628
  · exact g32p_row50_cosetWord_0629
  · exact g32p_row50_cosetWord_0630
  · exact g32p_row50_cosetWord_0631
  · exact g32p_row50_cosetWord_0632
  · exact g32p_row50_cosetWord_0633
  · exact g32p_row50_cosetWord_0634
  · exact g32p_row50_cosetWord_0635
  · exact g32p_row50_cosetWord_0636
  · exact g32p_row50_cosetWord_0637
  · exact g32p_row50_cosetWord_0638
  · exact g32p_row50_cosetWord_0639

theorem g32p_row50_cosetGeneratorBlock_0039 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 39 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s (g32p_finBlockIndex 640 39 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s (g32p_finBlockIndex 640 39 r))) := by
  fin_cases r
  · exact g32p_row50_cosetGeneratorStep_0624 s
  · exact g32p_row50_cosetGeneratorStep_0625 s
  · exact g32p_row50_cosetGeneratorStep_0626 s
  · exact g32p_row50_cosetGeneratorStep_0627 s
  · exact g32p_row50_cosetGeneratorStep_0628 s
  · exact g32p_row50_cosetGeneratorStep_0629 s
  · exact g32p_row50_cosetGeneratorStep_0630 s
  · exact g32p_row50_cosetGeneratorStep_0631 s
  · exact g32p_row50_cosetGeneratorStep_0632 s
  · exact g32p_row50_cosetGeneratorStep_0633 s
  · exact g32p_row50_cosetGeneratorStep_0634 s
  · exact g32p_row50_cosetGeneratorStep_0635 s
  · exact g32p_row50_cosetGeneratorStep_0636 s
  · exact g32p_row50_cosetGeneratorStep_0637 s
  · exact g32p_row50_cosetGeneratorStep_0638 s
  · exact g32p_row50_cosetGeneratorStep_0639 s

theorem g32p_row50_cosetBranchBlock_0039 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices s) (g32p_row50_cosetRepresentatives (g32p_finBlockIndex 640 39 r)) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetBranchNext s (g32p_finBlockIndex 640 39 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetBranchFactor s (g32p_finBlockIndex 640 39 r))) := by
  fin_cases r
  · exact g32p_row50_cosetBranchStep_0624 s
  · exact g32p_row50_cosetBranchStep_0625 s
  · exact g32p_row50_cosetBranchStep_0626 s
  · exact g32p_row50_cosetBranchStep_0627 s
  · exact g32p_row50_cosetBranchStep_0628 s
  · exact g32p_row50_cosetBranchStep_0629 s
  · exact g32p_row50_cosetBranchStep_0630 s
  · exact g32p_row50_cosetBranchStep_0631 s
  · exact g32p_row50_cosetBranchStep_0632 s
  · exact g32p_row50_cosetBranchStep_0633 s
  · exact g32p_row50_cosetBranchStep_0634 s
  · exact g32p_row50_cosetBranchStep_0635 s
  · exact g32p_row50_cosetBranchStep_0636 s
  · exact g32p_row50_cosetBranchStep_0637 s
  · exact g32p_row50_cosetBranchStep_0638 s
  · exact g32p_row50_cosetBranchStep_0639 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row50_cosetWord (i : Fin 640) :
    g32p_archiveIntegralWord (g32p_row50_cosetWords i) = g32p_row50_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row50_cosetWordBlock_0000
  · exact g32p_row50_cosetWordBlock_0001
  · exact g32p_row50_cosetWordBlock_0002
  · exact g32p_row50_cosetWordBlock_0003
  · exact g32p_row50_cosetWordBlock_0004
  · exact g32p_row50_cosetWordBlock_0005
  · exact g32p_row50_cosetWordBlock_0006
  · exact g32p_row50_cosetWordBlock_0007
  · exact g32p_row50_cosetWordBlock_0008
  · exact g32p_row50_cosetWordBlock_0009
  · exact g32p_row50_cosetWordBlock_0010
  · exact g32p_row50_cosetWordBlock_0011
  · exact g32p_row50_cosetWordBlock_0012
  · exact g32p_row50_cosetWordBlock_0013
  · exact g32p_row50_cosetWordBlock_0014
  · exact g32p_row50_cosetWordBlock_0015
  · exact g32p_row50_cosetWordBlock_0016
  · exact g32p_row50_cosetWordBlock_0017
  · exact g32p_row50_cosetWordBlock_0018
  · exact g32p_row50_cosetWordBlock_0019
  · exact g32p_row50_cosetWordBlock_0020
  · exact g32p_row50_cosetWordBlock_0021
  · exact g32p_row50_cosetWordBlock_0022
  · exact g32p_row50_cosetWordBlock_0023
  · exact g32p_row50_cosetWordBlock_0024
  · exact g32p_row50_cosetWordBlock_0025
  · exact g32p_row50_cosetWordBlock_0026
  · exact g32p_row50_cosetWordBlock_0027
  · exact g32p_row50_cosetWordBlock_0028
  · exact g32p_row50_cosetWordBlock_0029
  · exact g32p_row50_cosetWordBlock_0030
  · exact g32p_row50_cosetWordBlock_0031
  · exact g32p_row50_cosetWordBlock_0032
  · exact g32p_row50_cosetWordBlock_0033
  · exact g32p_row50_cosetWordBlock_0034
  · exact g32p_row50_cosetWordBlock_0035
  · exact g32p_row50_cosetWordBlock_0036
  · exact g32p_row50_cosetWordBlock_0037
  · exact g32p_row50_cosetWordBlock_0038
  · exact g32p_row50_cosetWordBlock_0039


def g32p_row50_cosetActualRepresentatives (i : Fin 640) : g32p_G := g32p_archiveWord (g32p_row50_cosetWords i)

theorem g32p_row50_cosetActualRepresentatives_map (i : Fin 640) :
    b4b_toMatrix (g32p_row50_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row50_cosetRepresentatives i)) := by
  rw [g32p_row50_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row50_cosetWord]

theorem g32p_row50_cosetGeneratorStep (s : Fin 4) (i : Fin 640) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row50_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetGeneratorNext s i))
        (g32p_row50_groupNodes (g32p_row50_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row50_cosetGeneratorBlock_0000 s
  · exact g32p_row50_cosetGeneratorBlock_0001 s
  · exact g32p_row50_cosetGeneratorBlock_0002 s
  · exact g32p_row50_cosetGeneratorBlock_0003 s
  · exact g32p_row50_cosetGeneratorBlock_0004 s
  · exact g32p_row50_cosetGeneratorBlock_0005 s
  · exact g32p_row50_cosetGeneratorBlock_0006 s
  · exact g32p_row50_cosetGeneratorBlock_0007 s
  · exact g32p_row50_cosetGeneratorBlock_0008 s
  · exact g32p_row50_cosetGeneratorBlock_0009 s
  · exact g32p_row50_cosetGeneratorBlock_0010 s
  · exact g32p_row50_cosetGeneratorBlock_0011 s
  · exact g32p_row50_cosetGeneratorBlock_0012 s
  · exact g32p_row50_cosetGeneratorBlock_0013 s
  · exact g32p_row50_cosetGeneratorBlock_0014 s
  · exact g32p_row50_cosetGeneratorBlock_0015 s
  · exact g32p_row50_cosetGeneratorBlock_0016 s
  · exact g32p_row50_cosetGeneratorBlock_0017 s
  · exact g32p_row50_cosetGeneratorBlock_0018 s
  · exact g32p_row50_cosetGeneratorBlock_0019 s
  · exact g32p_row50_cosetGeneratorBlock_0020 s
  · exact g32p_row50_cosetGeneratorBlock_0021 s
  · exact g32p_row50_cosetGeneratorBlock_0022 s
  · exact g32p_row50_cosetGeneratorBlock_0023 s
  · exact g32p_row50_cosetGeneratorBlock_0024 s
  · exact g32p_row50_cosetGeneratorBlock_0025 s
  · exact g32p_row50_cosetGeneratorBlock_0026 s
  · exact g32p_row50_cosetGeneratorBlock_0027 s
  · exact g32p_row50_cosetGeneratorBlock_0028 s
  · exact g32p_row50_cosetGeneratorBlock_0029 s
  · exact g32p_row50_cosetGeneratorBlock_0030 s
  · exact g32p_row50_cosetGeneratorBlock_0031 s
  · exact g32p_row50_cosetGeneratorBlock_0032 s
  · exact g32p_row50_cosetGeneratorBlock_0033 s
  · exact g32p_row50_cosetGeneratorBlock_0034 s
  · exact g32p_row50_cosetGeneratorBlock_0035 s
  · exact g32p_row50_cosetGeneratorBlock_0036 s
  · exact g32p_row50_cosetGeneratorBlock_0037 s
  · exact g32p_row50_cosetGeneratorBlock_0038 s
  · exact g32p_row50_cosetGeneratorBlock_0039 s


theorem g32p_row50_cosetActualStep (s : Fin 4) (i : Fin 640) :
    g32p_word (g32p_archiveWords s) * g32p_row50_cosetActualRepresentatives i =
      g32p_row50_cosetActualRepresentatives (g32p_row50_cosetGeneratorNext s i) *
        (g32p_row50_groupEquiv (g32p_row50_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row50_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row50_cosetActualRepresentatives (g32p_row50_cosetGeneratorNext s i) *
      (g32p_row50_groupEquiv (g32p_row50_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row50_cosetActualRepresentatives_map,
    g32p_row50_cosetActualRepresentatives_map, g32p_row50_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row50_cosetGeneratorStep]

theorem g32p_row50_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row50_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row50_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row50_cosetGeneratorNext
      (fun s i => g32p_row50_groupEquiv (g32p_row50_cosetGeneratorFactor s i))
    exact g32p_row50_cosetActualStep
  · rw [g32p_row50_finiteSupplier_order]
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

theorem g32p_row50_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 0)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 0)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 0) = g32p_row50_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 1)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 1)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 1) = g32p_row50_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 2)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 2)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 2) = g32p_row50_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 3)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 3)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 3) = g32p_row50_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 4)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 4)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 4) = g32p_row50_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 5)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 5)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 5) = g32p_row50_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 6)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 6)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 6) = g32p_row50_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 7)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 7)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 7) = g32p_row50_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 8)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 8)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 8) = g32p_row50_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 9)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 9)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 9) = g32p_row50_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 11)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 10)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 10) = g32p_row50_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 12)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 11)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 11) = g32p_row50_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 13)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 12)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 12) = g32p_row50_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 14)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 13)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 13) = g32p_row50_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 15)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 14)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 14) = g32p_row50_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 16)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 15)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 15) = g32p_row50_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row50_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 0) (g32p_row50_cosetLengths0 (g32p_finBlockIndex 256 0 r)))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 0 r))) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 0 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 0 r))) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 0 r)) = g32p_row50_cosetExponents0 (g32p_finBlockIndex 256 0 r) := by
  fin_cases r
  · exact g32p_row50_cosetMonodromy_0_0000
  · exact g32p_row50_cosetMonodromy_0_0001
  · exact g32p_row50_cosetMonodromy_0_0002
  · exact g32p_row50_cosetMonodromy_0_0003
  · exact g32p_row50_cosetMonodromy_0_0004
  · exact g32p_row50_cosetMonodromy_0_0005
  · exact g32p_row50_cosetMonodromy_0_0006
  · exact g32p_row50_cosetMonodromy_0_0007
  · exact g32p_row50_cosetMonodromy_0_0008
  · exact g32p_row50_cosetMonodromy_0_0009
  · exact g32p_row50_cosetMonodromy_0_0010
  · exact g32p_row50_cosetMonodromy_0_0011
  · exact g32p_row50_cosetMonodromy_0_0012
  · exact g32p_row50_cosetMonodromy_0_0013
  · exact g32p_row50_cosetMonodromy_0_0014
  · exact g32p_row50_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 17)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 16)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 16) = g32p_row50_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 19)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 17)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 17) = g32p_row50_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 20)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 18)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 18) = g32p_row50_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 21)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 19)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 19) = g32p_row50_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 22)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 20)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 20) = g32p_row50_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 23)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 21)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 21) = g32p_row50_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 24)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 22)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 22) = g32p_row50_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 25)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 23)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 23) = g32p_row50_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 26)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 24)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 24) = g32p_row50_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 27)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 25)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 25) = g32p_row50_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 29)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 26)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 26) = g32p_row50_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 30)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 27)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 27) = g32p_row50_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 31)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 28)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 28) = g32p_row50_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 32)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 29)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 29) = g32p_row50_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 33)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 30)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 30) = g32p_row50_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 35)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 31)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 31) = g32p_row50_cosetExponents0 31 := by
  decide +kernel

theorem g32p_row50_cosetMonodromyBlock0_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 0) (g32p_row50_cosetLengths0 (g32p_finBlockIndex 256 1 r)))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 1 r))) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 1 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 1 r))) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 1 r)) = g32p_row50_cosetExponents0 (g32p_finBlockIndex 256 1 r) := by
  fin_cases r
  · exact g32p_row50_cosetMonodromy_0_0016
  · exact g32p_row50_cosetMonodromy_0_0017
  · exact g32p_row50_cosetMonodromy_0_0018
  · exact g32p_row50_cosetMonodromy_0_0019
  · exact g32p_row50_cosetMonodromy_0_0020
  · exact g32p_row50_cosetMonodromy_0_0021
  · exact g32p_row50_cosetMonodromy_0_0022
  · exact g32p_row50_cosetMonodromy_0_0023
  · exact g32p_row50_cosetMonodromy_0_0024
  · exact g32p_row50_cosetMonodromy_0_0025
  · exact g32p_row50_cosetMonodromy_0_0026
  · exact g32p_row50_cosetMonodromy_0_0027
  · exact g32p_row50_cosetMonodromy_0_0028
  · exact g32p_row50_cosetMonodromy_0_0029
  · exact g32p_row50_cosetMonodromy_0_0030
  · exact g32p_row50_cosetMonodromy_0_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetMonodromy_0_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 36)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 32)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 32) = g32p_row50_cosetExponents0 32 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 37)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 33)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 33) = g32p_row50_cosetExponents0 33 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 38)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 34)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 34) = g32p_row50_cosetExponents0 34 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 39)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 35)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 35) = g32p_row50_cosetExponents0 35 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 41)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 36)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 36) = g32p_row50_cosetExponents0 36 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 44)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 37)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 37) = g32p_row50_cosetExponents0 37 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 45)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 38)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 38) = g32p_row50_cosetExponents0 38 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 46)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 39)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 39) = g32p_row50_cosetExponents0 39 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 47)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 40)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 40) = g32p_row50_cosetExponents0 40 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 50)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 41)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 41) = g32p_row50_cosetExponents0 41 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 51)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 42)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 42) = g32p_row50_cosetExponents0 42 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 52)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 43)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 43) = g32p_row50_cosetExponents0 43 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 53)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 44)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 44) = g32p_row50_cosetExponents0 44 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 54)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 45)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 45) = g32p_row50_cosetExponents0 45 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 55)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 46)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 46) = g32p_row50_cosetExponents0 46 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 57) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 57)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 47)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 47) = g32p_row50_cosetExponents0 47 := by
  decide +kernel

theorem g32p_row50_cosetMonodromyBlock0_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 0) (g32p_row50_cosetLengths0 (g32p_finBlockIndex 256 2 r)))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 2 r))) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 2 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 2 r))) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 2 r)) = g32p_row50_cosetExponents0 (g32p_finBlockIndex 256 2 r) := by
  fin_cases r
  · exact g32p_row50_cosetMonodromy_0_0032
  · exact g32p_row50_cosetMonodromy_0_0033
  · exact g32p_row50_cosetMonodromy_0_0034
  · exact g32p_row50_cosetMonodromy_0_0035
  · exact g32p_row50_cosetMonodromy_0_0036
  · exact g32p_row50_cosetMonodromy_0_0037
  · exact g32p_row50_cosetMonodromy_0_0038
  · exact g32p_row50_cosetMonodromy_0_0039
  · exact g32p_row50_cosetMonodromy_0_0040
  · exact g32p_row50_cosetMonodromy_0_0041
  · exact g32p_row50_cosetMonodromy_0_0042
  · exact g32p_row50_cosetMonodromy_0_0043
  · exact g32p_row50_cosetMonodromy_0_0044
  · exact g32p_row50_cosetMonodromy_0_0045
  · exact g32p_row50_cosetMonodromy_0_0046
  · exact g32p_row50_cosetMonodromy_0_0047


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetMonodromy_0_0048 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 58)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 48)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 48) = g32p_row50_cosetExponents0 48 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0049 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 59)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 49)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 49) = g32p_row50_cosetExponents0 49 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0050 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 60) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 60)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 50)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 50) = g32p_row50_cosetExponents0 50 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0051 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 61)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 51)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 51) = g32p_row50_cosetExponents0 51 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0052 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 62)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 52)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 52) = g32p_row50_cosetExponents0 52 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0053 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 63)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 53)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 53) = g32p_row50_cosetExponents0 53 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0054 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 65)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 54)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 54) = g32p_row50_cosetExponents0 54 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0055 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 66)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 55)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 55) = g32p_row50_cosetExponents0 55 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0056 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 67) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 67)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 56)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 56) = g32p_row50_cosetExponents0 56 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0057 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 68)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 57)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 57) = g32p_row50_cosetExponents0 57 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0058 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 69)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 58)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 58) = g32p_row50_cosetExponents0 58 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0059 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 70)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 59)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 59) = g32p_row50_cosetExponents0 59 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0060 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 71)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 60)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 60) = g32p_row50_cosetExponents0 60 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0061 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 72)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 61)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 61) = g32p_row50_cosetExponents0 61 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0062 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 75)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 62)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 62) = g32p_row50_cosetExponents0 62 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0063 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 76)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 63)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 63) = g32p_row50_cosetExponents0 63 := by
  decide +kernel

theorem g32p_row50_cosetMonodromyBlock0_0003 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 0) (g32p_row50_cosetLengths0 (g32p_finBlockIndex 256 3 r)))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 3 r))) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 3 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 3 r))) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 3 r)) = g32p_row50_cosetExponents0 (g32p_finBlockIndex 256 3 r) := by
  fin_cases r
  · exact g32p_row50_cosetMonodromy_0_0048
  · exact g32p_row50_cosetMonodromy_0_0049
  · exact g32p_row50_cosetMonodromy_0_0050
  · exact g32p_row50_cosetMonodromy_0_0051
  · exact g32p_row50_cosetMonodromy_0_0052
  · exact g32p_row50_cosetMonodromy_0_0053
  · exact g32p_row50_cosetMonodromy_0_0054
  · exact g32p_row50_cosetMonodromy_0_0055
  · exact g32p_row50_cosetMonodromy_0_0056
  · exact g32p_row50_cosetMonodromy_0_0057
  · exact g32p_row50_cosetMonodromy_0_0058
  · exact g32p_row50_cosetMonodromy_0_0059
  · exact g32p_row50_cosetMonodromy_0_0060
  · exact g32p_row50_cosetMonodromy_0_0061
  · exact g32p_row50_cosetMonodromy_0_0062
  · exact g32p_row50_cosetMonodromy_0_0063


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetMonodromy_0_0064 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 77)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 64)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 64) = g32p_row50_cosetExponents0 64 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0065 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 79)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 65)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 65) = g32p_row50_cosetExponents0 65 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0066 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 80)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 66)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 66) = g32p_row50_cosetExponents0 66 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0067 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 81)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 67)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 67) = g32p_row50_cosetExponents0 67 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0068 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 82)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 68)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 68) = g32p_row50_cosetExponents0 68 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0069 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 84) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 84)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 69)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 69) = g32p_row50_cosetExponents0 69 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0070 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 85)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 70)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 70) = g32p_row50_cosetExponents0 70 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0071 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 86) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 86)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 71)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 71) = g32p_row50_cosetExponents0 71 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0072 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 88)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 72)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 72) = g32p_row50_cosetExponents0 72 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0073 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 89) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 89)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 73)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 73) = g32p_row50_cosetExponents0 73 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0074 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 92) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 92)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 74)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 74) = g32p_row50_cosetExponents0 74 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0075 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 95) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 95)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 75)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 75) = g32p_row50_cosetExponents0 75 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0076 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 96) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 96)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 76)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 76) = g32p_row50_cosetExponents0 76 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0077 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 97) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 97)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 77)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 77) = g32p_row50_cosetExponents0 77 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0078 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 99) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 99)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 78)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 78) = g32p_row50_cosetExponents0 78 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0079 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 101) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 101)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 79)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 79) = g32p_row50_cosetExponents0 79 := by
  decide +kernel

theorem g32p_row50_cosetMonodromyBlock0_0004 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 0) (g32p_row50_cosetLengths0 (g32p_finBlockIndex 256 4 r)))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 4 r))) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 4 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 4 r))) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 4 r)) = g32p_row50_cosetExponents0 (g32p_finBlockIndex 256 4 r) := by
  fin_cases r
  · exact g32p_row50_cosetMonodromy_0_0064
  · exact g32p_row50_cosetMonodromy_0_0065
  · exact g32p_row50_cosetMonodromy_0_0066
  · exact g32p_row50_cosetMonodromy_0_0067
  · exact g32p_row50_cosetMonodromy_0_0068
  · exact g32p_row50_cosetMonodromy_0_0069
  · exact g32p_row50_cosetMonodromy_0_0070
  · exact g32p_row50_cosetMonodromy_0_0071
  · exact g32p_row50_cosetMonodromy_0_0072
  · exact g32p_row50_cosetMonodromy_0_0073
  · exact g32p_row50_cosetMonodromy_0_0074
  · exact g32p_row50_cosetMonodromy_0_0075
  · exact g32p_row50_cosetMonodromy_0_0076
  · exact g32p_row50_cosetMonodromy_0_0077
  · exact g32p_row50_cosetMonodromy_0_0078
  · exact g32p_row50_cosetMonodromy_0_0079


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetMonodromy_0_0080 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 102) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 102)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 80)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 80) = g32p_row50_cosetExponents0 80 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0081 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 103) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 103)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 81)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 81) = g32p_row50_cosetExponents0 81 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0082 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 104) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 104)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 82)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 82) = g32p_row50_cosetExponents0 82 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0083 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 106) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 106)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 83)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 83) = g32p_row50_cosetExponents0 83 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0084 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 107) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 107)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 84)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 84) = g32p_row50_cosetExponents0 84 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0085 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 108) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 108)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 85)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 85) = g32p_row50_cosetExponents0 85 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0086 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 109) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 109)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 86)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 86) = g32p_row50_cosetExponents0 86 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0087 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 113) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 113)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 87)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 87) = g32p_row50_cosetExponents0 87 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0088 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 114) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 114)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 88)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 88) = g32p_row50_cosetExponents0 88 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0089 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 115) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 115)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 89)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 89) = g32p_row50_cosetExponents0 89 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0090 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 116) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 116)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 90)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 90) = g32p_row50_cosetExponents0 90 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0091 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 117) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 117)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 91)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 91) = g32p_row50_cosetExponents0 91 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0092 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 118) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 118)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 92)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 92) = g32p_row50_cosetExponents0 92 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0093 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 119) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 119)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 93)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 93) = g32p_row50_cosetExponents0 93 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0094 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 120) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 120)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 94)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 94) = g32p_row50_cosetExponents0 94 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0095 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 121) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 121)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 95)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 95) = g32p_row50_cosetExponents0 95 := by
  decide +kernel

theorem g32p_row50_cosetMonodromyBlock0_0005 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 0) (g32p_row50_cosetLengths0 (g32p_finBlockIndex 256 5 r)))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 5 r))) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 5 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 5 r))) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 5 r)) = g32p_row50_cosetExponents0 (g32p_finBlockIndex 256 5 r) := by
  fin_cases r
  · exact g32p_row50_cosetMonodromy_0_0080
  · exact g32p_row50_cosetMonodromy_0_0081
  · exact g32p_row50_cosetMonodromy_0_0082
  · exact g32p_row50_cosetMonodromy_0_0083
  · exact g32p_row50_cosetMonodromy_0_0084
  · exact g32p_row50_cosetMonodromy_0_0085
  · exact g32p_row50_cosetMonodromy_0_0086
  · exact g32p_row50_cosetMonodromy_0_0087
  · exact g32p_row50_cosetMonodromy_0_0088
  · exact g32p_row50_cosetMonodromy_0_0089
  · exact g32p_row50_cosetMonodromy_0_0090
  · exact g32p_row50_cosetMonodromy_0_0091
  · exact g32p_row50_cosetMonodromy_0_0092
  · exact g32p_row50_cosetMonodromy_0_0093
  · exact g32p_row50_cosetMonodromy_0_0094
  · exact g32p_row50_cosetMonodromy_0_0095


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row50_cosetMonodromy_0_0096 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 122) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 122)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 96)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 96) = g32p_row50_cosetExponents0 96 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0097 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 123) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 123)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 97)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 97) = g32p_row50_cosetExponents0 97 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0098 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 124) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 124)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 98)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 98) = g32p_row50_cosetExponents0 98 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0099 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 125) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 125)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 99)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 99) = g32p_row50_cosetExponents0 99 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0100 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 127) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 127)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 100)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 100) = g32p_row50_cosetExponents0 100 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0101 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 128) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 128)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 101)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 101) = g32p_row50_cosetExponents0 101 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0102 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 130) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 130)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 102)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 102) = g32p_row50_cosetExponents0 102 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0103 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 131) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 131)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 103)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 103) = g32p_row50_cosetExponents0 103 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0104 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 133) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 133)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 104)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 104) = g32p_row50_cosetExponents0 104 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0105 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 134) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 134)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 105)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 105) = g32p_row50_cosetExponents0 105 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0106 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 135) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 135)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 106)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 106) = g32p_row50_cosetExponents0 106 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0107 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row50_cosetRepresentatives 136) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 136)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 107)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 107) = g32p_row50_cosetExponents0 107 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0108 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 137) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 137)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 108)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 108) = g32p_row50_cosetExponents0 108 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0109 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 138) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 138)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 109)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 109) = g32p_row50_cosetExponents0 109 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0110 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 139) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 139)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 110)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 110) = g32p_row50_cosetExponents0 110 := by
  decide +kernel

theorem g32p_row50_cosetMonodromy_0_0111 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row50_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row50_cosetRepresentatives 140) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives 140)
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 111)) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 111) = g32p_row50_cosetExponents0 111 := by
  decide +kernel

theorem g32p_row50_cosetMonodromyBlock0_0006 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row50_cosetBranchMatrices 0) (g32p_row50_cosetLengths0 (g32p_finBlockIndex 256 6 r)))
      (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 6 r))) =
      HurwitzPrymRex_mmul (g32p_row50_cosetRepresentatives (g32p_row50_cosetRoots0 (g32p_finBlockIndex 256 6 r)))
        (g32p_row50_groupNodes (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 6 r))) ∧
    g32p_row50_characterValues (g32p_row50_cosetMonodromies0 (g32p_finBlockIndex 256 6 r)) = g32p_row50_cosetExponents0 (g32p_finBlockIndex 256 6 r) := by
  fin_cases r
  · exact g32p_row50_cosetMonodromy_0_0096
  · exact g32p_row50_cosetMonodromy_0_0097
  · exact g32p_row50_cosetMonodromy_0_0098
  · exact g32p_row50_cosetMonodromy_0_0099
  · exact g32p_row50_cosetMonodromy_0_0100
  · exact g32p_row50_cosetMonodromy_0_0101
  · exact g32p_row50_cosetMonodromy_0_0102
  · exact g32p_row50_cosetMonodromy_0_0103
  · exact g32p_row50_cosetMonodromy_0_0104
  · exact g32p_row50_cosetMonodromy_0_0105
  · exact g32p_row50_cosetMonodromy_0_0106
  · exact g32p_row50_cosetMonodromy_0_0107
  · exact g32p_row50_cosetMonodromy_0_0108
  · exact g32p_row50_cosetMonodromy_0_0109
  · exact g32p_row50_cosetMonodromy_0_0110
  · exact g32p_row50_cosetMonodromy_0_0111


end HodgeLean.Foundations.Program

end
