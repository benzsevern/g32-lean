import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked1044

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2560 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2560) = g32p_row13_cosetRepresentatives 2560 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2560 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2560) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2560))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2560)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2560 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2560) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2560))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2560)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2561 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2561) = g32p_row13_cosetRepresentatives 2561 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2561 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2561) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2561))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2561)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2561 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2561) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2561))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2561)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2562 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2562) = g32p_row13_cosetRepresentatives 2562 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2562 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2562) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2562))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2562)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2562 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2562) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2562))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2562)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2563 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2563) = g32p_row13_cosetRepresentatives 2563 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2563 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2563) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2563))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2563)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2563 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2563) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2563))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2563)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2564 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2564) = g32p_row13_cosetRepresentatives 2564 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2564 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2564) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2564))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2564)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2564 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2564) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2564))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2564)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2565 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2565) = g32p_row13_cosetRepresentatives 2565 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2565 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2565) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2565))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2565)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2565 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2565) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2565))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2565)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2566 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2566) = g32p_row13_cosetRepresentatives 2566 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2566 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2566) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2566))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2566)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2566 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2566) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2566))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2566)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2567 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2567) = g32p_row13_cosetRepresentatives 2567 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2567 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2567) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2567))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2567)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2567 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2567) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2567))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2567)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2568 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2568) = g32p_row13_cosetRepresentatives 2568 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2568 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2568) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2568))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2568)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2568 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2568) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2568))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2568)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2569 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2569) = g32p_row13_cosetRepresentatives 2569 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2569 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2569) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2569))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2569)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2569 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2569) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2569))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2569)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2570 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2570) = g32p_row13_cosetRepresentatives 2570 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2570 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2570) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2570))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2570)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2570 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2570) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2570))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2570)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2571 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2571) = g32p_row13_cosetRepresentatives 2571 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2571 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2571) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2571))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2571)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2571 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2571) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2571))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2571)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2572 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2572) = g32p_row13_cosetRepresentatives 2572 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2572 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2572) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2572))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2572)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2572 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2572) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2572))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2572)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2573 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2573) = g32p_row13_cosetRepresentatives 2573 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2573 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2573) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2573))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2573)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2573 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2573) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2573))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2573)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2574 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2574) = g32p_row13_cosetRepresentatives 2574 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2574 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2574) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2574))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2574)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2574 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2574) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2574))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2574)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2575 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2575) = g32p_row13_cosetRepresentatives 2575 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2575 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2575) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2575))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2575)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2575 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2575) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2575))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2575)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0160 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 160 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 160 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2560
  · exact g32p_row13_cosetWord_2561
  · exact g32p_row13_cosetWord_2562
  · exact g32p_row13_cosetWord_2563
  · exact g32p_row13_cosetWord_2564
  · exact g32p_row13_cosetWord_2565
  · exact g32p_row13_cosetWord_2566
  · exact g32p_row13_cosetWord_2567
  · exact g32p_row13_cosetWord_2568
  · exact g32p_row13_cosetWord_2569
  · exact g32p_row13_cosetWord_2570
  · exact g32p_row13_cosetWord_2571
  · exact g32p_row13_cosetWord_2572
  · exact g32p_row13_cosetWord_2573
  · exact g32p_row13_cosetWord_2574
  · exact g32p_row13_cosetWord_2575

theorem g32p_row13_cosetGeneratorBlock_0160 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 160 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 160 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 160 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2560 s
  · exact g32p_row13_cosetGeneratorStep_2561 s
  · exact g32p_row13_cosetGeneratorStep_2562 s
  · exact g32p_row13_cosetGeneratorStep_2563 s
  · exact g32p_row13_cosetGeneratorStep_2564 s
  · exact g32p_row13_cosetGeneratorStep_2565 s
  · exact g32p_row13_cosetGeneratorStep_2566 s
  · exact g32p_row13_cosetGeneratorStep_2567 s
  · exact g32p_row13_cosetGeneratorStep_2568 s
  · exact g32p_row13_cosetGeneratorStep_2569 s
  · exact g32p_row13_cosetGeneratorStep_2570 s
  · exact g32p_row13_cosetGeneratorStep_2571 s
  · exact g32p_row13_cosetGeneratorStep_2572 s
  · exact g32p_row13_cosetGeneratorStep_2573 s
  · exact g32p_row13_cosetGeneratorStep_2574 s
  · exact g32p_row13_cosetGeneratorStep_2575 s

theorem g32p_row13_cosetBranchBlock_0160 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 160 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 160 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 160 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2560 s
  · exact g32p_row13_cosetBranchStep_2561 s
  · exact g32p_row13_cosetBranchStep_2562 s
  · exact g32p_row13_cosetBranchStep_2563 s
  · exact g32p_row13_cosetBranchStep_2564 s
  · exact g32p_row13_cosetBranchStep_2565 s
  · exact g32p_row13_cosetBranchStep_2566 s
  · exact g32p_row13_cosetBranchStep_2567 s
  · exact g32p_row13_cosetBranchStep_2568 s
  · exact g32p_row13_cosetBranchStep_2569 s
  · exact g32p_row13_cosetBranchStep_2570 s
  · exact g32p_row13_cosetBranchStep_2571 s
  · exact g32p_row13_cosetBranchStep_2572 s
  · exact g32p_row13_cosetBranchStep_2573 s
  · exact g32p_row13_cosetBranchStep_2574 s
  · exact g32p_row13_cosetBranchStep_2575 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2576 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2576) = g32p_row13_cosetRepresentatives 2576 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2576 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2576) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2576))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2576)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2576 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2576) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2576))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2576)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2577 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2577) = g32p_row13_cosetRepresentatives 2577 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2577 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2577) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2577))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2577)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2577 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2577) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2577))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2577)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2578 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2578) = g32p_row13_cosetRepresentatives 2578 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2578 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2578) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2578))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2578)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2578 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2578) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2578))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2578)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2579 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2579) = g32p_row13_cosetRepresentatives 2579 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2579 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2579) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2579))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2579)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2579 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2579) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2579))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2579)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2580 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2580) = g32p_row13_cosetRepresentatives 2580 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2580 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2580) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2580))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2580)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2580 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2580) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2580))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2580)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2581 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2581) = g32p_row13_cosetRepresentatives 2581 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2581 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2581) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2581))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2581)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2581 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2581) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2581))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2581)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2582 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2582) = g32p_row13_cosetRepresentatives 2582 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2582 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2582) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2582))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2582)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2582 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2582) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2582))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2582)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2583 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2583) = g32p_row13_cosetRepresentatives 2583 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2583 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2583) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2583))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2583)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2583 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2583) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2583))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2583)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2584 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2584) = g32p_row13_cosetRepresentatives 2584 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2584 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2584) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2584))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2584)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2584 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2584) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2584))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2584)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2585 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2585) = g32p_row13_cosetRepresentatives 2585 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2585 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2585) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2585))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2585)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2585 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2585) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2585))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2585)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2586 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2586) = g32p_row13_cosetRepresentatives 2586 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2586 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2586) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2586))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2586)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2586 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2586) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2586))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2586)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2587 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2587) = g32p_row13_cosetRepresentatives 2587 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2587 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2587) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2587))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2587)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2587 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2587) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2587))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2587)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2588 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2588) = g32p_row13_cosetRepresentatives 2588 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2588 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2588) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2588))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2588)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2588 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2588) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2588))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2588)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2589 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2589) = g32p_row13_cosetRepresentatives 2589 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2589 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2589) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2589))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2589)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2589 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2589) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2589))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2589)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2590 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2590) = g32p_row13_cosetRepresentatives 2590 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2590 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2590) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2590))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2590)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2590 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2590) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2590))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2590)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2591 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2591) = g32p_row13_cosetRepresentatives 2591 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2591 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2591) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2591))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2591)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2591 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2591) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2591))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2591)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0161 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 161 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 161 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2576
  · exact g32p_row13_cosetWord_2577
  · exact g32p_row13_cosetWord_2578
  · exact g32p_row13_cosetWord_2579
  · exact g32p_row13_cosetWord_2580
  · exact g32p_row13_cosetWord_2581
  · exact g32p_row13_cosetWord_2582
  · exact g32p_row13_cosetWord_2583
  · exact g32p_row13_cosetWord_2584
  · exact g32p_row13_cosetWord_2585
  · exact g32p_row13_cosetWord_2586
  · exact g32p_row13_cosetWord_2587
  · exact g32p_row13_cosetWord_2588
  · exact g32p_row13_cosetWord_2589
  · exact g32p_row13_cosetWord_2590
  · exact g32p_row13_cosetWord_2591

theorem g32p_row13_cosetGeneratorBlock_0161 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 161 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 161 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 161 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2576 s
  · exact g32p_row13_cosetGeneratorStep_2577 s
  · exact g32p_row13_cosetGeneratorStep_2578 s
  · exact g32p_row13_cosetGeneratorStep_2579 s
  · exact g32p_row13_cosetGeneratorStep_2580 s
  · exact g32p_row13_cosetGeneratorStep_2581 s
  · exact g32p_row13_cosetGeneratorStep_2582 s
  · exact g32p_row13_cosetGeneratorStep_2583 s
  · exact g32p_row13_cosetGeneratorStep_2584 s
  · exact g32p_row13_cosetGeneratorStep_2585 s
  · exact g32p_row13_cosetGeneratorStep_2586 s
  · exact g32p_row13_cosetGeneratorStep_2587 s
  · exact g32p_row13_cosetGeneratorStep_2588 s
  · exact g32p_row13_cosetGeneratorStep_2589 s
  · exact g32p_row13_cosetGeneratorStep_2590 s
  · exact g32p_row13_cosetGeneratorStep_2591 s

theorem g32p_row13_cosetBranchBlock_0161 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 161 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 161 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 161 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2576 s
  · exact g32p_row13_cosetBranchStep_2577 s
  · exact g32p_row13_cosetBranchStep_2578 s
  · exact g32p_row13_cosetBranchStep_2579 s
  · exact g32p_row13_cosetBranchStep_2580 s
  · exact g32p_row13_cosetBranchStep_2581 s
  · exact g32p_row13_cosetBranchStep_2582 s
  · exact g32p_row13_cosetBranchStep_2583 s
  · exact g32p_row13_cosetBranchStep_2584 s
  · exact g32p_row13_cosetBranchStep_2585 s
  · exact g32p_row13_cosetBranchStep_2586 s
  · exact g32p_row13_cosetBranchStep_2587 s
  · exact g32p_row13_cosetBranchStep_2588 s
  · exact g32p_row13_cosetBranchStep_2589 s
  · exact g32p_row13_cosetBranchStep_2590 s
  · exact g32p_row13_cosetBranchStep_2591 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2592 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2592) = g32p_row13_cosetRepresentatives 2592 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2592 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2592) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2592))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2592)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2592 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2592) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2592))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2592)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2593 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2593) = g32p_row13_cosetRepresentatives 2593 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2593 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2593) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2593))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2593)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2593 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2593) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2593))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2593)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2594 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2594) = g32p_row13_cosetRepresentatives 2594 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2594 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2594) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2594))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2594)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2594 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2594) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2594))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2594)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2595 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2595) = g32p_row13_cosetRepresentatives 2595 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2595 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2595) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2595))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2595)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2595 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2595) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2595))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2595)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2596 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2596) = g32p_row13_cosetRepresentatives 2596 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2596 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2596) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2596))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2596)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2596 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2596) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2596))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2596)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2597 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2597) = g32p_row13_cosetRepresentatives 2597 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2597 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2597) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2597))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2597)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2597 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2597) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2597))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2597)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2598 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2598) = g32p_row13_cosetRepresentatives 2598 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2598 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2598) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2598))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2598)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2598 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2598) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2598))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2598)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2599 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2599) = g32p_row13_cosetRepresentatives 2599 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2599 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2599) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2599))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2599)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2599 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2599) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2599))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2599)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2600 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2600) = g32p_row13_cosetRepresentatives 2600 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2600 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2600) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2600))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2600)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2600 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2600) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2600))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2600)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2601 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2601) = g32p_row13_cosetRepresentatives 2601 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2601 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2601) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2601))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2601)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2601 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2601) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2601))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2601)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2602 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2602) = g32p_row13_cosetRepresentatives 2602 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2602 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2602) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2602))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2602)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2602 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2602) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2602))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2602)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2603 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2603) = g32p_row13_cosetRepresentatives 2603 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2603 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2603) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2603))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2603)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2603 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2603) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2603))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2603)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2604 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2604) = g32p_row13_cosetRepresentatives 2604 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2604 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2604) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2604))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2604)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2604 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2604) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2604))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2604)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2605 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2605) = g32p_row13_cosetRepresentatives 2605 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2605 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2605) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2605))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2605)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2605 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2605) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2605))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2605)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2606 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2606) = g32p_row13_cosetRepresentatives 2606 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2606 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2606) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2606))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2606)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2606 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2606) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2606))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2606)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2607 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2607) = g32p_row13_cosetRepresentatives 2607 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2607 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2607) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2607))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2607)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2607 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2607) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2607))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2607)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0162 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 162 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 162 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2592
  · exact g32p_row13_cosetWord_2593
  · exact g32p_row13_cosetWord_2594
  · exact g32p_row13_cosetWord_2595
  · exact g32p_row13_cosetWord_2596
  · exact g32p_row13_cosetWord_2597
  · exact g32p_row13_cosetWord_2598
  · exact g32p_row13_cosetWord_2599
  · exact g32p_row13_cosetWord_2600
  · exact g32p_row13_cosetWord_2601
  · exact g32p_row13_cosetWord_2602
  · exact g32p_row13_cosetWord_2603
  · exact g32p_row13_cosetWord_2604
  · exact g32p_row13_cosetWord_2605
  · exact g32p_row13_cosetWord_2606
  · exact g32p_row13_cosetWord_2607

theorem g32p_row13_cosetGeneratorBlock_0162 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 162 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 162 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 162 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2592 s
  · exact g32p_row13_cosetGeneratorStep_2593 s
  · exact g32p_row13_cosetGeneratorStep_2594 s
  · exact g32p_row13_cosetGeneratorStep_2595 s
  · exact g32p_row13_cosetGeneratorStep_2596 s
  · exact g32p_row13_cosetGeneratorStep_2597 s
  · exact g32p_row13_cosetGeneratorStep_2598 s
  · exact g32p_row13_cosetGeneratorStep_2599 s
  · exact g32p_row13_cosetGeneratorStep_2600 s
  · exact g32p_row13_cosetGeneratorStep_2601 s
  · exact g32p_row13_cosetGeneratorStep_2602 s
  · exact g32p_row13_cosetGeneratorStep_2603 s
  · exact g32p_row13_cosetGeneratorStep_2604 s
  · exact g32p_row13_cosetGeneratorStep_2605 s
  · exact g32p_row13_cosetGeneratorStep_2606 s
  · exact g32p_row13_cosetGeneratorStep_2607 s

theorem g32p_row13_cosetBranchBlock_0162 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 162 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 162 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 162 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2592 s
  · exact g32p_row13_cosetBranchStep_2593 s
  · exact g32p_row13_cosetBranchStep_2594 s
  · exact g32p_row13_cosetBranchStep_2595 s
  · exact g32p_row13_cosetBranchStep_2596 s
  · exact g32p_row13_cosetBranchStep_2597 s
  · exact g32p_row13_cosetBranchStep_2598 s
  · exact g32p_row13_cosetBranchStep_2599 s
  · exact g32p_row13_cosetBranchStep_2600 s
  · exact g32p_row13_cosetBranchStep_2601 s
  · exact g32p_row13_cosetBranchStep_2602 s
  · exact g32p_row13_cosetBranchStep_2603 s
  · exact g32p_row13_cosetBranchStep_2604 s
  · exact g32p_row13_cosetBranchStep_2605 s
  · exact g32p_row13_cosetBranchStep_2606 s
  · exact g32p_row13_cosetBranchStep_2607 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2608 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2608) = g32p_row13_cosetRepresentatives 2608 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2608 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2608) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2608))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2608)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2608 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2608) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2608))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2608)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2609 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2609) = g32p_row13_cosetRepresentatives 2609 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2609 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2609) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2609))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2609)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2609 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2609) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2609))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2609)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2610 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2610) = g32p_row13_cosetRepresentatives 2610 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2610 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2610) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2610))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2610)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2610 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2610) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2610))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2610)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2611 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2611) = g32p_row13_cosetRepresentatives 2611 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2611 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2611) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2611))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2611)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2611 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2611) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2611))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2611)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2612 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2612) = g32p_row13_cosetRepresentatives 2612 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2612 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2612) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2612))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2612)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2612 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2612) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2612))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2612)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2613 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2613) = g32p_row13_cosetRepresentatives 2613 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2613 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2613) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2613))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2613)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2613 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2613) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2613))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2613)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2614 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2614) = g32p_row13_cosetRepresentatives 2614 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2614 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2614) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2614))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2614)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2614 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2614) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2614))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2614)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2615 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2615) = g32p_row13_cosetRepresentatives 2615 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2615 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2615) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2615))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2615)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2615 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2615) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2615))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2615)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2616 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2616) = g32p_row13_cosetRepresentatives 2616 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2616 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2616) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2616))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2616)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2616 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2616) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2616))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2616)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2617 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2617) = g32p_row13_cosetRepresentatives 2617 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2617 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2617) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2617))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2617)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2617 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2617) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2617))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2617)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2618 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2618) = g32p_row13_cosetRepresentatives 2618 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2618 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2618) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2618))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2618)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2618 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2618) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2618))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2618)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2619 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2619) = g32p_row13_cosetRepresentatives 2619 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2619 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2619) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2619))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2619)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2619 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2619) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2619))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2619)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2620 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2620) = g32p_row13_cosetRepresentatives 2620 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2620 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2620) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2620))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2620)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2620 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2620) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2620))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2620)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2621 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2621) = g32p_row13_cosetRepresentatives 2621 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2621 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2621) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2621))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2621)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2621 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2621) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2621))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2621)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2622 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2622) = g32p_row13_cosetRepresentatives 2622 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2622 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2622) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2622))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2622)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2622 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2622) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2622))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2622)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2623 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2623) = g32p_row13_cosetRepresentatives 2623 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2623 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2623) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2623))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2623)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2623 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2623) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2623))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2623)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0163 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 163 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 163 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2608
  · exact g32p_row13_cosetWord_2609
  · exact g32p_row13_cosetWord_2610
  · exact g32p_row13_cosetWord_2611
  · exact g32p_row13_cosetWord_2612
  · exact g32p_row13_cosetWord_2613
  · exact g32p_row13_cosetWord_2614
  · exact g32p_row13_cosetWord_2615
  · exact g32p_row13_cosetWord_2616
  · exact g32p_row13_cosetWord_2617
  · exact g32p_row13_cosetWord_2618
  · exact g32p_row13_cosetWord_2619
  · exact g32p_row13_cosetWord_2620
  · exact g32p_row13_cosetWord_2621
  · exact g32p_row13_cosetWord_2622
  · exact g32p_row13_cosetWord_2623

theorem g32p_row13_cosetGeneratorBlock_0163 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 163 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 163 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 163 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2608 s
  · exact g32p_row13_cosetGeneratorStep_2609 s
  · exact g32p_row13_cosetGeneratorStep_2610 s
  · exact g32p_row13_cosetGeneratorStep_2611 s
  · exact g32p_row13_cosetGeneratorStep_2612 s
  · exact g32p_row13_cosetGeneratorStep_2613 s
  · exact g32p_row13_cosetGeneratorStep_2614 s
  · exact g32p_row13_cosetGeneratorStep_2615 s
  · exact g32p_row13_cosetGeneratorStep_2616 s
  · exact g32p_row13_cosetGeneratorStep_2617 s
  · exact g32p_row13_cosetGeneratorStep_2618 s
  · exact g32p_row13_cosetGeneratorStep_2619 s
  · exact g32p_row13_cosetGeneratorStep_2620 s
  · exact g32p_row13_cosetGeneratorStep_2621 s
  · exact g32p_row13_cosetGeneratorStep_2622 s
  · exact g32p_row13_cosetGeneratorStep_2623 s

theorem g32p_row13_cosetBranchBlock_0163 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 163 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 163 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 163 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2608 s
  · exact g32p_row13_cosetBranchStep_2609 s
  · exact g32p_row13_cosetBranchStep_2610 s
  · exact g32p_row13_cosetBranchStep_2611 s
  · exact g32p_row13_cosetBranchStep_2612 s
  · exact g32p_row13_cosetBranchStep_2613 s
  · exact g32p_row13_cosetBranchStep_2614 s
  · exact g32p_row13_cosetBranchStep_2615 s
  · exact g32p_row13_cosetBranchStep_2616 s
  · exact g32p_row13_cosetBranchStep_2617 s
  · exact g32p_row13_cosetBranchStep_2618 s
  · exact g32p_row13_cosetBranchStep_2619 s
  · exact g32p_row13_cosetBranchStep_2620 s
  · exact g32p_row13_cosetBranchStep_2621 s
  · exact g32p_row13_cosetBranchStep_2622 s
  · exact g32p_row13_cosetBranchStep_2623 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2624 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2624) = g32p_row13_cosetRepresentatives 2624 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2624 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2624) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2624))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2624)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2624 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2624) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2624))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2624)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2625 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2625) = g32p_row13_cosetRepresentatives 2625 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2625 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2625) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2625))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2625)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2625 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2625) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2625))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2625)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2626 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2626) = g32p_row13_cosetRepresentatives 2626 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2626 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2626) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2626))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2626)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2626 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2626) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2626))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2626)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2627 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2627) = g32p_row13_cosetRepresentatives 2627 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2627 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2627) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2627))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2627)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2627 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2627) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2627))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2627)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2628 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2628) = g32p_row13_cosetRepresentatives 2628 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2628 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2628) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2628))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2628)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2628 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2628) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2628))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2628)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2629 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2629) = g32p_row13_cosetRepresentatives 2629 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2629 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2629) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2629))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2629)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2629 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2629) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2629))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2629)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2630 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2630) = g32p_row13_cosetRepresentatives 2630 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2630 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2630) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2630))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2630)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2630 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2630) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2630))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2630)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2631 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2631) = g32p_row13_cosetRepresentatives 2631 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2631 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2631) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2631))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2631)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2631 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2631) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2631))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2631)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2632 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2632) = g32p_row13_cosetRepresentatives 2632 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2632 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2632) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2632))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2632)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2632 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2632) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2632))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2632)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2633 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2633) = g32p_row13_cosetRepresentatives 2633 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2633 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2633) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2633))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2633)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2633 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2633) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2633))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2633)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2634 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2634) = g32p_row13_cosetRepresentatives 2634 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2634 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2634) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2634))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2634)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2634 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2634) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2634))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2634)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2635 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2635) = g32p_row13_cosetRepresentatives 2635 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2635 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2635) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2635))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2635)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2635 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2635) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2635))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2635)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2636 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2636) = g32p_row13_cosetRepresentatives 2636 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2636 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2636) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2636))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2636)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2636 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2636) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2636))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2636)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2637 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2637) = g32p_row13_cosetRepresentatives 2637 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2637 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2637) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2637))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2637)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2637 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2637) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2637))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2637)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2638 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2638) = g32p_row13_cosetRepresentatives 2638 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2638 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2638) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2638))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2638)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2638 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2638) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2638))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2638)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2639 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2639) = g32p_row13_cosetRepresentatives 2639 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2639 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2639) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2639))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2639)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2639 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2639) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2639))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2639)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0164 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 164 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 164 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2624
  · exact g32p_row13_cosetWord_2625
  · exact g32p_row13_cosetWord_2626
  · exact g32p_row13_cosetWord_2627
  · exact g32p_row13_cosetWord_2628
  · exact g32p_row13_cosetWord_2629
  · exact g32p_row13_cosetWord_2630
  · exact g32p_row13_cosetWord_2631
  · exact g32p_row13_cosetWord_2632
  · exact g32p_row13_cosetWord_2633
  · exact g32p_row13_cosetWord_2634
  · exact g32p_row13_cosetWord_2635
  · exact g32p_row13_cosetWord_2636
  · exact g32p_row13_cosetWord_2637
  · exact g32p_row13_cosetWord_2638
  · exact g32p_row13_cosetWord_2639

theorem g32p_row13_cosetGeneratorBlock_0164 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 164 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 164 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 164 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2624 s
  · exact g32p_row13_cosetGeneratorStep_2625 s
  · exact g32p_row13_cosetGeneratorStep_2626 s
  · exact g32p_row13_cosetGeneratorStep_2627 s
  · exact g32p_row13_cosetGeneratorStep_2628 s
  · exact g32p_row13_cosetGeneratorStep_2629 s
  · exact g32p_row13_cosetGeneratorStep_2630 s
  · exact g32p_row13_cosetGeneratorStep_2631 s
  · exact g32p_row13_cosetGeneratorStep_2632 s
  · exact g32p_row13_cosetGeneratorStep_2633 s
  · exact g32p_row13_cosetGeneratorStep_2634 s
  · exact g32p_row13_cosetGeneratorStep_2635 s
  · exact g32p_row13_cosetGeneratorStep_2636 s
  · exact g32p_row13_cosetGeneratorStep_2637 s
  · exact g32p_row13_cosetGeneratorStep_2638 s
  · exact g32p_row13_cosetGeneratorStep_2639 s

theorem g32p_row13_cosetBranchBlock_0164 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 164 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 164 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 164 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2624 s
  · exact g32p_row13_cosetBranchStep_2625 s
  · exact g32p_row13_cosetBranchStep_2626 s
  · exact g32p_row13_cosetBranchStep_2627 s
  · exact g32p_row13_cosetBranchStep_2628 s
  · exact g32p_row13_cosetBranchStep_2629 s
  · exact g32p_row13_cosetBranchStep_2630 s
  · exact g32p_row13_cosetBranchStep_2631 s
  · exact g32p_row13_cosetBranchStep_2632 s
  · exact g32p_row13_cosetBranchStep_2633 s
  · exact g32p_row13_cosetBranchStep_2634 s
  · exact g32p_row13_cosetBranchStep_2635 s
  · exact g32p_row13_cosetBranchStep_2636 s
  · exact g32p_row13_cosetBranchStep_2637 s
  · exact g32p_row13_cosetBranchStep_2638 s
  · exact g32p_row13_cosetBranchStep_2639 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2640 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2640) = g32p_row13_cosetRepresentatives 2640 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2640 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2640) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2640))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2640)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2640 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2640) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2640))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2640)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2641 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2641) = g32p_row13_cosetRepresentatives 2641 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2641 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2641) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2641))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2641)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2641 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2641) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2641))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2641)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2642 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2642) = g32p_row13_cosetRepresentatives 2642 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2642 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2642) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2642))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2642)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2642 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2642) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2642))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2642)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2643 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2643) = g32p_row13_cosetRepresentatives 2643 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2643 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2643) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2643))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2643)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2643 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2643) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2643))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2643)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2644 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2644) = g32p_row13_cosetRepresentatives 2644 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2644 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2644) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2644))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2644)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2644 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2644) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2644))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2644)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2645 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2645) = g32p_row13_cosetRepresentatives 2645 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2645 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2645) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2645))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2645)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2645 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2645) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2645))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2645)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2646 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2646) = g32p_row13_cosetRepresentatives 2646 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2646 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2646) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2646))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2646)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2646 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2646) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2646))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2646)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2647 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2647) = g32p_row13_cosetRepresentatives 2647 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2647 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2647) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2647))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2647)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2647 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2647) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2647))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2647)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2648 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2648) = g32p_row13_cosetRepresentatives 2648 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2648 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2648) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2648))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2648)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2648 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2648) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2648))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2648)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2649 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2649) = g32p_row13_cosetRepresentatives 2649 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2649 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2649) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2649))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2649)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2649 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2649) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2649))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2649)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2650 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2650) = g32p_row13_cosetRepresentatives 2650 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2650 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2650) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2650))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2650)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2650 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2650) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2650))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2650)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2651 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2651) = g32p_row13_cosetRepresentatives 2651 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2651 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2651) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2651))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2651)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2651 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2651) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2651))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2651)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2652 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2652) = g32p_row13_cosetRepresentatives 2652 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2652 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2652) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2652))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2652)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2652 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2652) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2652))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2652)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2653 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2653) = g32p_row13_cosetRepresentatives 2653 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2653 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2653) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2653))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2653)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2653 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2653) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2653))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2653)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2654 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2654) = g32p_row13_cosetRepresentatives 2654 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2654 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2654) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2654))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2654)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2654 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2654) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2654))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2654)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2655 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2655) = g32p_row13_cosetRepresentatives 2655 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2655 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2655) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2655))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2655)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2655 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2655) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2655))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2655)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0165 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 165 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 165 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2640
  · exact g32p_row13_cosetWord_2641
  · exact g32p_row13_cosetWord_2642
  · exact g32p_row13_cosetWord_2643
  · exact g32p_row13_cosetWord_2644
  · exact g32p_row13_cosetWord_2645
  · exact g32p_row13_cosetWord_2646
  · exact g32p_row13_cosetWord_2647
  · exact g32p_row13_cosetWord_2648
  · exact g32p_row13_cosetWord_2649
  · exact g32p_row13_cosetWord_2650
  · exact g32p_row13_cosetWord_2651
  · exact g32p_row13_cosetWord_2652
  · exact g32p_row13_cosetWord_2653
  · exact g32p_row13_cosetWord_2654
  · exact g32p_row13_cosetWord_2655

theorem g32p_row13_cosetGeneratorBlock_0165 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 165 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 165 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 165 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2640 s
  · exact g32p_row13_cosetGeneratorStep_2641 s
  · exact g32p_row13_cosetGeneratorStep_2642 s
  · exact g32p_row13_cosetGeneratorStep_2643 s
  · exact g32p_row13_cosetGeneratorStep_2644 s
  · exact g32p_row13_cosetGeneratorStep_2645 s
  · exact g32p_row13_cosetGeneratorStep_2646 s
  · exact g32p_row13_cosetGeneratorStep_2647 s
  · exact g32p_row13_cosetGeneratorStep_2648 s
  · exact g32p_row13_cosetGeneratorStep_2649 s
  · exact g32p_row13_cosetGeneratorStep_2650 s
  · exact g32p_row13_cosetGeneratorStep_2651 s
  · exact g32p_row13_cosetGeneratorStep_2652 s
  · exact g32p_row13_cosetGeneratorStep_2653 s
  · exact g32p_row13_cosetGeneratorStep_2654 s
  · exact g32p_row13_cosetGeneratorStep_2655 s

theorem g32p_row13_cosetBranchBlock_0165 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 165 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 165 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 165 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2640 s
  · exact g32p_row13_cosetBranchStep_2641 s
  · exact g32p_row13_cosetBranchStep_2642 s
  · exact g32p_row13_cosetBranchStep_2643 s
  · exact g32p_row13_cosetBranchStep_2644 s
  · exact g32p_row13_cosetBranchStep_2645 s
  · exact g32p_row13_cosetBranchStep_2646 s
  · exact g32p_row13_cosetBranchStep_2647 s
  · exact g32p_row13_cosetBranchStep_2648 s
  · exact g32p_row13_cosetBranchStep_2649 s
  · exact g32p_row13_cosetBranchStep_2650 s
  · exact g32p_row13_cosetBranchStep_2651 s
  · exact g32p_row13_cosetBranchStep_2652 s
  · exact g32p_row13_cosetBranchStep_2653 s
  · exact g32p_row13_cosetBranchStep_2654 s
  · exact g32p_row13_cosetBranchStep_2655 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2656 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2656) = g32p_row13_cosetRepresentatives 2656 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2656 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2656) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2656))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2656)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2656 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2656) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2656))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2656)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2657 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2657) = g32p_row13_cosetRepresentatives 2657 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2657 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2657) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2657))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2657)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2657 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2657) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2657))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2657)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2658 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2658) = g32p_row13_cosetRepresentatives 2658 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2658 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2658) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2658))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2658)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2658 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2658) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2658))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2658)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2659 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2659) = g32p_row13_cosetRepresentatives 2659 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2659 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2659) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2659))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2659)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2659 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2659) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2659))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2659)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2660 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2660) = g32p_row13_cosetRepresentatives 2660 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2660 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2660) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2660))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2660)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2660 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2660) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2660))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2660)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2661 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2661) = g32p_row13_cosetRepresentatives 2661 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2661 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2661) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2661))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2661)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2661 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2661) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2661))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2661)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2662 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2662) = g32p_row13_cosetRepresentatives 2662 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2662 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2662) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2662))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2662)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2662 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2662) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2662))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2662)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2663 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2663) = g32p_row13_cosetRepresentatives 2663 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2663 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2663) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2663))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2663)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2663 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2663) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2663))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2663)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2664 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2664) = g32p_row13_cosetRepresentatives 2664 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2664 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2664) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2664))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2664)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2664 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2664) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2664))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2664)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2665 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2665) = g32p_row13_cosetRepresentatives 2665 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2665 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2665) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2665))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2665)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2665 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2665) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2665))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2665)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2666 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2666) = g32p_row13_cosetRepresentatives 2666 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2666 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2666) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2666))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2666)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2666 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2666) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2666))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2666)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2667 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2667) = g32p_row13_cosetRepresentatives 2667 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2667 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2667) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2667))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2667)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2667 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2667) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2667))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2667)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2668 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2668) = g32p_row13_cosetRepresentatives 2668 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2668 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2668) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2668))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2668)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2668 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2668) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2668))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2668)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2669 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2669) = g32p_row13_cosetRepresentatives 2669 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2669 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2669) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2669))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2669)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2669 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2669) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2669))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2669)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2670 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2670) = g32p_row13_cosetRepresentatives 2670 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2670 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2670) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2670))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2670)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2670 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2670) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2670))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2670)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2671 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2671) = g32p_row13_cosetRepresentatives 2671 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2671 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2671) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2671))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2671)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2671 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2671) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2671))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2671)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0166 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 166 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 166 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2656
  · exact g32p_row13_cosetWord_2657
  · exact g32p_row13_cosetWord_2658
  · exact g32p_row13_cosetWord_2659
  · exact g32p_row13_cosetWord_2660
  · exact g32p_row13_cosetWord_2661
  · exact g32p_row13_cosetWord_2662
  · exact g32p_row13_cosetWord_2663
  · exact g32p_row13_cosetWord_2664
  · exact g32p_row13_cosetWord_2665
  · exact g32p_row13_cosetWord_2666
  · exact g32p_row13_cosetWord_2667
  · exact g32p_row13_cosetWord_2668
  · exact g32p_row13_cosetWord_2669
  · exact g32p_row13_cosetWord_2670
  · exact g32p_row13_cosetWord_2671

theorem g32p_row13_cosetGeneratorBlock_0166 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 166 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 166 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 166 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2656 s
  · exact g32p_row13_cosetGeneratorStep_2657 s
  · exact g32p_row13_cosetGeneratorStep_2658 s
  · exact g32p_row13_cosetGeneratorStep_2659 s
  · exact g32p_row13_cosetGeneratorStep_2660 s
  · exact g32p_row13_cosetGeneratorStep_2661 s
  · exact g32p_row13_cosetGeneratorStep_2662 s
  · exact g32p_row13_cosetGeneratorStep_2663 s
  · exact g32p_row13_cosetGeneratorStep_2664 s
  · exact g32p_row13_cosetGeneratorStep_2665 s
  · exact g32p_row13_cosetGeneratorStep_2666 s
  · exact g32p_row13_cosetGeneratorStep_2667 s
  · exact g32p_row13_cosetGeneratorStep_2668 s
  · exact g32p_row13_cosetGeneratorStep_2669 s
  · exact g32p_row13_cosetGeneratorStep_2670 s
  · exact g32p_row13_cosetGeneratorStep_2671 s

theorem g32p_row13_cosetBranchBlock_0166 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 166 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 166 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 166 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2656 s
  · exact g32p_row13_cosetBranchStep_2657 s
  · exact g32p_row13_cosetBranchStep_2658 s
  · exact g32p_row13_cosetBranchStep_2659 s
  · exact g32p_row13_cosetBranchStep_2660 s
  · exact g32p_row13_cosetBranchStep_2661 s
  · exact g32p_row13_cosetBranchStep_2662 s
  · exact g32p_row13_cosetBranchStep_2663 s
  · exact g32p_row13_cosetBranchStep_2664 s
  · exact g32p_row13_cosetBranchStep_2665 s
  · exact g32p_row13_cosetBranchStep_2666 s
  · exact g32p_row13_cosetBranchStep_2667 s
  · exact g32p_row13_cosetBranchStep_2668 s
  · exact g32p_row13_cosetBranchStep_2669 s
  · exact g32p_row13_cosetBranchStep_2670 s
  · exact g32p_row13_cosetBranchStep_2671 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2672 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2672) = g32p_row13_cosetRepresentatives 2672 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2672 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2672) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2672))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2672)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2672 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2672) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2672))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2672)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2673 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2673) = g32p_row13_cosetRepresentatives 2673 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2673 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2673) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2673))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2673)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2673 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2673) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2673))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2673)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2674 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2674) = g32p_row13_cosetRepresentatives 2674 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2674 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2674) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2674))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2674)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2674 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2674) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2674))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2674)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2675 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2675) = g32p_row13_cosetRepresentatives 2675 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2675 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2675) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2675))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2675)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2675 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2675) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2675))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2675)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2676 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2676) = g32p_row13_cosetRepresentatives 2676 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2676 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2676) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2676))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2676)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2676 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2676) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2676))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2676)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2677 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2677) = g32p_row13_cosetRepresentatives 2677 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2677 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2677) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2677))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2677)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2677 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2677) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2677))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2677)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2678 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2678) = g32p_row13_cosetRepresentatives 2678 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2678 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2678) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2678))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2678)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2678 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2678) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2678))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2678)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2679 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2679) = g32p_row13_cosetRepresentatives 2679 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2679 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2679) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2679))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2679)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2679 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2679) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2679))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2679)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2680 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2680) = g32p_row13_cosetRepresentatives 2680 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2680 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2680) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2680))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2680)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2680 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2680) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2680))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2680)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2681 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2681) = g32p_row13_cosetRepresentatives 2681 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2681 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2681) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2681))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2681)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2681 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2681) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2681))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2681)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2682 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2682) = g32p_row13_cosetRepresentatives 2682 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2682 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2682) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2682))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2682)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2682 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2682) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2682))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2682)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2683 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2683) = g32p_row13_cosetRepresentatives 2683 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2683 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2683) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2683))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2683)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2683 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2683) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2683))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2683)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2684 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2684) = g32p_row13_cosetRepresentatives 2684 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2684 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2684) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2684))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2684)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2684 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2684) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2684))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2684)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2685 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2685) = g32p_row13_cosetRepresentatives 2685 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2685 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2685) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2685))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2685)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2685 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2685) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2685))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2685)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2686 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2686) = g32p_row13_cosetRepresentatives 2686 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2686 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2686) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2686))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2686)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2686 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2686) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2686))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2686)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2687 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2687) = g32p_row13_cosetRepresentatives 2687 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2687 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2687) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2687))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2687)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2687 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2687) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2687))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2687)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0167 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 167 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 167 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2672
  · exact g32p_row13_cosetWord_2673
  · exact g32p_row13_cosetWord_2674
  · exact g32p_row13_cosetWord_2675
  · exact g32p_row13_cosetWord_2676
  · exact g32p_row13_cosetWord_2677
  · exact g32p_row13_cosetWord_2678
  · exact g32p_row13_cosetWord_2679
  · exact g32p_row13_cosetWord_2680
  · exact g32p_row13_cosetWord_2681
  · exact g32p_row13_cosetWord_2682
  · exact g32p_row13_cosetWord_2683
  · exact g32p_row13_cosetWord_2684
  · exact g32p_row13_cosetWord_2685
  · exact g32p_row13_cosetWord_2686
  · exact g32p_row13_cosetWord_2687

theorem g32p_row13_cosetGeneratorBlock_0167 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 167 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 167 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 167 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2672 s
  · exact g32p_row13_cosetGeneratorStep_2673 s
  · exact g32p_row13_cosetGeneratorStep_2674 s
  · exact g32p_row13_cosetGeneratorStep_2675 s
  · exact g32p_row13_cosetGeneratorStep_2676 s
  · exact g32p_row13_cosetGeneratorStep_2677 s
  · exact g32p_row13_cosetGeneratorStep_2678 s
  · exact g32p_row13_cosetGeneratorStep_2679 s
  · exact g32p_row13_cosetGeneratorStep_2680 s
  · exact g32p_row13_cosetGeneratorStep_2681 s
  · exact g32p_row13_cosetGeneratorStep_2682 s
  · exact g32p_row13_cosetGeneratorStep_2683 s
  · exact g32p_row13_cosetGeneratorStep_2684 s
  · exact g32p_row13_cosetGeneratorStep_2685 s
  · exact g32p_row13_cosetGeneratorStep_2686 s
  · exact g32p_row13_cosetGeneratorStep_2687 s

theorem g32p_row13_cosetBranchBlock_0167 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 167 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 167 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 167 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2672 s
  · exact g32p_row13_cosetBranchStep_2673 s
  · exact g32p_row13_cosetBranchStep_2674 s
  · exact g32p_row13_cosetBranchStep_2675 s
  · exact g32p_row13_cosetBranchStep_2676 s
  · exact g32p_row13_cosetBranchStep_2677 s
  · exact g32p_row13_cosetBranchStep_2678 s
  · exact g32p_row13_cosetBranchStep_2679 s
  · exact g32p_row13_cosetBranchStep_2680 s
  · exact g32p_row13_cosetBranchStep_2681 s
  · exact g32p_row13_cosetBranchStep_2682 s
  · exact g32p_row13_cosetBranchStep_2683 s
  · exact g32p_row13_cosetBranchStep_2684 s
  · exact g32p_row13_cosetBranchStep_2685 s
  · exact g32p_row13_cosetBranchStep_2686 s
  · exact g32p_row13_cosetBranchStep_2687 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2688 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2688) = g32p_row13_cosetRepresentatives 2688 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2688 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2688) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2688))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2688)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2688 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2688) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2688))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2688)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2689 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2689) = g32p_row13_cosetRepresentatives 2689 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2689 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2689) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2689))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2689)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2689 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2689) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2689))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2689)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2690 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2690) = g32p_row13_cosetRepresentatives 2690 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2690 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2690) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2690))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2690)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2690 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2690) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2690))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2690)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2691 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2691) = g32p_row13_cosetRepresentatives 2691 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2691 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2691) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2691))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2691)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2691 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2691) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2691))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2691)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2692 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2692) = g32p_row13_cosetRepresentatives 2692 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2692 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2692) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2692))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2692)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2692 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2692) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2692))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2692)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2693 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2693) = g32p_row13_cosetRepresentatives 2693 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2693 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2693) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2693))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2693)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2693 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2693) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2693))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2693)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2694 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2694) = g32p_row13_cosetRepresentatives 2694 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2694 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2694) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2694))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2694)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2694 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2694) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2694))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2694)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2695 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2695) = g32p_row13_cosetRepresentatives 2695 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2695 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2695) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2695))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2695)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2695 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2695) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2695))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2695)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2696 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2696) = g32p_row13_cosetRepresentatives 2696 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2696 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2696) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2696))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2696)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2696 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2696) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2696))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2696)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2697 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2697) = g32p_row13_cosetRepresentatives 2697 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2697 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2697) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2697))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2697)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2697 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2697) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2697))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2697)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2698 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2698) = g32p_row13_cosetRepresentatives 2698 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2698 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2698) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2698))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2698)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2698 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2698) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2698))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2698)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2699 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2699) = g32p_row13_cosetRepresentatives 2699 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2699 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2699) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2699))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2699)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2699 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2699) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2699))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2699)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2700 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2700) = g32p_row13_cosetRepresentatives 2700 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2700 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2700) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2700))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2700)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2700 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2700) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2700))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2700)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2701 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2701) = g32p_row13_cosetRepresentatives 2701 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2701 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2701) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2701))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2701)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2701 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2701) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2701))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2701)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2702 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2702) = g32p_row13_cosetRepresentatives 2702 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2702 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2702) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2702))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2702)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2702 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2702) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2702))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2702)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2703 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2703) = g32p_row13_cosetRepresentatives 2703 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2703 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2703) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2703))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2703)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2703 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2703) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2703))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2703)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0168 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 168 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 168 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2688
  · exact g32p_row13_cosetWord_2689
  · exact g32p_row13_cosetWord_2690
  · exact g32p_row13_cosetWord_2691
  · exact g32p_row13_cosetWord_2692
  · exact g32p_row13_cosetWord_2693
  · exact g32p_row13_cosetWord_2694
  · exact g32p_row13_cosetWord_2695
  · exact g32p_row13_cosetWord_2696
  · exact g32p_row13_cosetWord_2697
  · exact g32p_row13_cosetWord_2698
  · exact g32p_row13_cosetWord_2699
  · exact g32p_row13_cosetWord_2700
  · exact g32p_row13_cosetWord_2701
  · exact g32p_row13_cosetWord_2702
  · exact g32p_row13_cosetWord_2703

theorem g32p_row13_cosetGeneratorBlock_0168 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 168 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 168 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 168 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2688 s
  · exact g32p_row13_cosetGeneratorStep_2689 s
  · exact g32p_row13_cosetGeneratorStep_2690 s
  · exact g32p_row13_cosetGeneratorStep_2691 s
  · exact g32p_row13_cosetGeneratorStep_2692 s
  · exact g32p_row13_cosetGeneratorStep_2693 s
  · exact g32p_row13_cosetGeneratorStep_2694 s
  · exact g32p_row13_cosetGeneratorStep_2695 s
  · exact g32p_row13_cosetGeneratorStep_2696 s
  · exact g32p_row13_cosetGeneratorStep_2697 s
  · exact g32p_row13_cosetGeneratorStep_2698 s
  · exact g32p_row13_cosetGeneratorStep_2699 s
  · exact g32p_row13_cosetGeneratorStep_2700 s
  · exact g32p_row13_cosetGeneratorStep_2701 s
  · exact g32p_row13_cosetGeneratorStep_2702 s
  · exact g32p_row13_cosetGeneratorStep_2703 s

theorem g32p_row13_cosetBranchBlock_0168 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 168 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 168 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 168 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2688 s
  · exact g32p_row13_cosetBranchStep_2689 s
  · exact g32p_row13_cosetBranchStep_2690 s
  · exact g32p_row13_cosetBranchStep_2691 s
  · exact g32p_row13_cosetBranchStep_2692 s
  · exact g32p_row13_cosetBranchStep_2693 s
  · exact g32p_row13_cosetBranchStep_2694 s
  · exact g32p_row13_cosetBranchStep_2695 s
  · exact g32p_row13_cosetBranchStep_2696 s
  · exact g32p_row13_cosetBranchStep_2697 s
  · exact g32p_row13_cosetBranchStep_2698 s
  · exact g32p_row13_cosetBranchStep_2699 s
  · exact g32p_row13_cosetBranchStep_2700 s
  · exact g32p_row13_cosetBranchStep_2701 s
  · exact g32p_row13_cosetBranchStep_2702 s
  · exact g32p_row13_cosetBranchStep_2703 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2704 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2704) = g32p_row13_cosetRepresentatives 2704 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2704 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2704) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2704))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2704)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2704 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2704) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2704))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2704)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2705 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2705) = g32p_row13_cosetRepresentatives 2705 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2705 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2705) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2705))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2705)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2705 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2705) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2705))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2705)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2706 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2706) = g32p_row13_cosetRepresentatives 2706 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2706 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2706) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2706))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2706)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2706 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2706) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2706))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2706)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2707 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2707) = g32p_row13_cosetRepresentatives 2707 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2707 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2707) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2707))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2707)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2707 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2707) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2707))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2707)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2708 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2708) = g32p_row13_cosetRepresentatives 2708 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2708 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2708) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2708))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2708)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2708 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2708) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2708))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2708)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2709 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2709) = g32p_row13_cosetRepresentatives 2709 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2709 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2709) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2709))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2709)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2709 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2709) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2709))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2709)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2710 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2710) = g32p_row13_cosetRepresentatives 2710 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2710 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2710) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2710))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2710)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2710 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2710) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2710))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2710)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2711 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2711) = g32p_row13_cosetRepresentatives 2711 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2711 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2711) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2711))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2711)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2711 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2711) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2711))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2711)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2712 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2712) = g32p_row13_cosetRepresentatives 2712 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2712 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2712) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2712))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2712)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2712 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2712) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2712))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2712)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2713 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2713) = g32p_row13_cosetRepresentatives 2713 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2713 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2713) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2713))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2713)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2713 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2713) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2713))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2713)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2714 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2714) = g32p_row13_cosetRepresentatives 2714 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2714 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2714) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2714))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2714)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2714 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2714) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2714))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2714)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2715 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2715) = g32p_row13_cosetRepresentatives 2715 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2715 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2715) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2715))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2715)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2715 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2715) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2715))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2715)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2716 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2716) = g32p_row13_cosetRepresentatives 2716 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2716 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2716) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2716))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2716)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2716 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2716) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2716))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2716)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2717 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2717) = g32p_row13_cosetRepresentatives 2717 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2717 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2717) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2717))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2717)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2717 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2717) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2717))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2717)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2718 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2718) = g32p_row13_cosetRepresentatives 2718 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2718 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2718) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2718))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2718)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2718 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2718) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2718))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2718)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2719 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2719) = g32p_row13_cosetRepresentatives 2719 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2719 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2719) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2719))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2719)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2719 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2719) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2719))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2719)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0169 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 169 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 169 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2704
  · exact g32p_row13_cosetWord_2705
  · exact g32p_row13_cosetWord_2706
  · exact g32p_row13_cosetWord_2707
  · exact g32p_row13_cosetWord_2708
  · exact g32p_row13_cosetWord_2709
  · exact g32p_row13_cosetWord_2710
  · exact g32p_row13_cosetWord_2711
  · exact g32p_row13_cosetWord_2712
  · exact g32p_row13_cosetWord_2713
  · exact g32p_row13_cosetWord_2714
  · exact g32p_row13_cosetWord_2715
  · exact g32p_row13_cosetWord_2716
  · exact g32p_row13_cosetWord_2717
  · exact g32p_row13_cosetWord_2718
  · exact g32p_row13_cosetWord_2719

theorem g32p_row13_cosetGeneratorBlock_0169 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 169 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 169 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 169 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2704 s
  · exact g32p_row13_cosetGeneratorStep_2705 s
  · exact g32p_row13_cosetGeneratorStep_2706 s
  · exact g32p_row13_cosetGeneratorStep_2707 s
  · exact g32p_row13_cosetGeneratorStep_2708 s
  · exact g32p_row13_cosetGeneratorStep_2709 s
  · exact g32p_row13_cosetGeneratorStep_2710 s
  · exact g32p_row13_cosetGeneratorStep_2711 s
  · exact g32p_row13_cosetGeneratorStep_2712 s
  · exact g32p_row13_cosetGeneratorStep_2713 s
  · exact g32p_row13_cosetGeneratorStep_2714 s
  · exact g32p_row13_cosetGeneratorStep_2715 s
  · exact g32p_row13_cosetGeneratorStep_2716 s
  · exact g32p_row13_cosetGeneratorStep_2717 s
  · exact g32p_row13_cosetGeneratorStep_2718 s
  · exact g32p_row13_cosetGeneratorStep_2719 s

theorem g32p_row13_cosetBranchBlock_0169 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 169 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 169 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 169 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2704 s
  · exact g32p_row13_cosetBranchStep_2705 s
  · exact g32p_row13_cosetBranchStep_2706 s
  · exact g32p_row13_cosetBranchStep_2707 s
  · exact g32p_row13_cosetBranchStep_2708 s
  · exact g32p_row13_cosetBranchStep_2709 s
  · exact g32p_row13_cosetBranchStep_2710 s
  · exact g32p_row13_cosetBranchStep_2711 s
  · exact g32p_row13_cosetBranchStep_2712 s
  · exact g32p_row13_cosetBranchStep_2713 s
  · exact g32p_row13_cosetBranchStep_2714 s
  · exact g32p_row13_cosetBranchStep_2715 s
  · exact g32p_row13_cosetBranchStep_2716 s
  · exact g32p_row13_cosetBranchStep_2717 s
  · exact g32p_row13_cosetBranchStep_2718 s
  · exact g32p_row13_cosetBranchStep_2719 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2720 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2720) = g32p_row13_cosetRepresentatives 2720 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2720 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2720) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2720))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2720)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2720 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2720) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2720))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2720)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2721 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2721) = g32p_row13_cosetRepresentatives 2721 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2721 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2721) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2721))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2721)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2721 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2721) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2721))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2721)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2722 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2722) = g32p_row13_cosetRepresentatives 2722 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2722 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2722) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2722))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2722)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2722 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2722) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2722))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2722)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2723 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2723) = g32p_row13_cosetRepresentatives 2723 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2723 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2723) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2723))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2723)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2723 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2723) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2723))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2723)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2724 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2724) = g32p_row13_cosetRepresentatives 2724 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2724 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2724) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2724))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2724)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2724 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2724) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2724))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2724)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2725 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2725) = g32p_row13_cosetRepresentatives 2725 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2725 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2725) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2725))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2725)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2725 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2725) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2725))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2725)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2726 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2726) = g32p_row13_cosetRepresentatives 2726 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2726 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2726) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2726))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2726)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2726 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2726) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2726))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2726)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2727 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2727) = g32p_row13_cosetRepresentatives 2727 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2727 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2727) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2727))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2727)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2727 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2727) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2727))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2727)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2728 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2728) = g32p_row13_cosetRepresentatives 2728 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2728 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2728) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2728))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2728)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2728 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2728) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2728))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2728)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2729 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2729) = g32p_row13_cosetRepresentatives 2729 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2729 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2729) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2729))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2729)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2729 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2729) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2729))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2729)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2730 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2730) = g32p_row13_cosetRepresentatives 2730 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2730 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2730) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2730))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2730)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2730 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2730) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2730))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2730)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2731 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2731) = g32p_row13_cosetRepresentatives 2731 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2731 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2731) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2731))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2731)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2731 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2731) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2731))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2731)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2732 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2732) = g32p_row13_cosetRepresentatives 2732 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2732 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2732) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2732))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2732)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2732 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2732) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2732))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2732)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2733 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2733) = g32p_row13_cosetRepresentatives 2733 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2733 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2733) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2733))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2733)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2733 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2733) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2733))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2733)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2734 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2734) = g32p_row13_cosetRepresentatives 2734 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2734 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2734) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2734))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2734)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2734 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2734) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2734))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2734)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2735 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2735) = g32p_row13_cosetRepresentatives 2735 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2735 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2735) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2735))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2735)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2735 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2735) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2735))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2735)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0170 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 170 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 170 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2720
  · exact g32p_row13_cosetWord_2721
  · exact g32p_row13_cosetWord_2722
  · exact g32p_row13_cosetWord_2723
  · exact g32p_row13_cosetWord_2724
  · exact g32p_row13_cosetWord_2725
  · exact g32p_row13_cosetWord_2726
  · exact g32p_row13_cosetWord_2727
  · exact g32p_row13_cosetWord_2728
  · exact g32p_row13_cosetWord_2729
  · exact g32p_row13_cosetWord_2730
  · exact g32p_row13_cosetWord_2731
  · exact g32p_row13_cosetWord_2732
  · exact g32p_row13_cosetWord_2733
  · exact g32p_row13_cosetWord_2734
  · exact g32p_row13_cosetWord_2735

theorem g32p_row13_cosetGeneratorBlock_0170 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 170 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 170 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 170 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2720 s
  · exact g32p_row13_cosetGeneratorStep_2721 s
  · exact g32p_row13_cosetGeneratorStep_2722 s
  · exact g32p_row13_cosetGeneratorStep_2723 s
  · exact g32p_row13_cosetGeneratorStep_2724 s
  · exact g32p_row13_cosetGeneratorStep_2725 s
  · exact g32p_row13_cosetGeneratorStep_2726 s
  · exact g32p_row13_cosetGeneratorStep_2727 s
  · exact g32p_row13_cosetGeneratorStep_2728 s
  · exact g32p_row13_cosetGeneratorStep_2729 s
  · exact g32p_row13_cosetGeneratorStep_2730 s
  · exact g32p_row13_cosetGeneratorStep_2731 s
  · exact g32p_row13_cosetGeneratorStep_2732 s
  · exact g32p_row13_cosetGeneratorStep_2733 s
  · exact g32p_row13_cosetGeneratorStep_2734 s
  · exact g32p_row13_cosetGeneratorStep_2735 s

theorem g32p_row13_cosetBranchBlock_0170 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 170 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 170 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 170 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2720 s
  · exact g32p_row13_cosetBranchStep_2721 s
  · exact g32p_row13_cosetBranchStep_2722 s
  · exact g32p_row13_cosetBranchStep_2723 s
  · exact g32p_row13_cosetBranchStep_2724 s
  · exact g32p_row13_cosetBranchStep_2725 s
  · exact g32p_row13_cosetBranchStep_2726 s
  · exact g32p_row13_cosetBranchStep_2727 s
  · exact g32p_row13_cosetBranchStep_2728 s
  · exact g32p_row13_cosetBranchStep_2729 s
  · exact g32p_row13_cosetBranchStep_2730 s
  · exact g32p_row13_cosetBranchStep_2731 s
  · exact g32p_row13_cosetBranchStep_2732 s
  · exact g32p_row13_cosetBranchStep_2733 s
  · exact g32p_row13_cosetBranchStep_2734 s
  · exact g32p_row13_cosetBranchStep_2735 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2736 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2736) = g32p_row13_cosetRepresentatives 2736 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2736 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2736) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2736))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2736)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2736 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2736) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2736))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2736)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2737 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2737) = g32p_row13_cosetRepresentatives 2737 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2737 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2737) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2737))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2737)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2737 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2737) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2737))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2737)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2738 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2738) = g32p_row13_cosetRepresentatives 2738 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2738 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2738) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2738))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2738)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2738 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2738) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2738))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2738)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2739 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2739) = g32p_row13_cosetRepresentatives 2739 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2739 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2739) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2739))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2739)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2739 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2739) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2739))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2739)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2740 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2740) = g32p_row13_cosetRepresentatives 2740 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2740 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2740) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2740))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2740)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2740 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2740) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2740))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2740)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2741 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2741) = g32p_row13_cosetRepresentatives 2741 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2741 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2741) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2741))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2741)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2741 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2741) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2741))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2741)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2742 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2742) = g32p_row13_cosetRepresentatives 2742 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2742 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2742) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2742))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2742)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2742 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2742) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2742))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2742)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2743 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2743) = g32p_row13_cosetRepresentatives 2743 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2743 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2743) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2743))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2743)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2743 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2743) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2743))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2743)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2744 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2744) = g32p_row13_cosetRepresentatives 2744 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2744 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2744) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2744))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2744)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2744 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2744) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2744))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2744)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2745 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2745) = g32p_row13_cosetRepresentatives 2745 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2745 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2745) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2745))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2745)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2745 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2745) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2745))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2745)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2746 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2746) = g32p_row13_cosetRepresentatives 2746 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2746 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2746) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2746))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2746)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2746 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2746) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2746))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2746)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2747 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2747) = g32p_row13_cosetRepresentatives 2747 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2747 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2747) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2747))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2747)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2747 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2747) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2747))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2747)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2748 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2748) = g32p_row13_cosetRepresentatives 2748 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2748 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2748) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2748))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2748)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2748 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2748) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2748))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2748)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2749 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2749) = g32p_row13_cosetRepresentatives 2749 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2749 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2749) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2749))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2749)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2749 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2749) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2749))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2749)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2750 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2750) = g32p_row13_cosetRepresentatives 2750 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2750 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2750) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2750))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2750)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2750 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2750) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2750))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2750)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2751 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2751) = g32p_row13_cosetRepresentatives 2751 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2751 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2751) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2751))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2751)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2751 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2751) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2751))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2751)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0171 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 171 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 171 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2736
  · exact g32p_row13_cosetWord_2737
  · exact g32p_row13_cosetWord_2738
  · exact g32p_row13_cosetWord_2739
  · exact g32p_row13_cosetWord_2740
  · exact g32p_row13_cosetWord_2741
  · exact g32p_row13_cosetWord_2742
  · exact g32p_row13_cosetWord_2743
  · exact g32p_row13_cosetWord_2744
  · exact g32p_row13_cosetWord_2745
  · exact g32p_row13_cosetWord_2746
  · exact g32p_row13_cosetWord_2747
  · exact g32p_row13_cosetWord_2748
  · exact g32p_row13_cosetWord_2749
  · exact g32p_row13_cosetWord_2750
  · exact g32p_row13_cosetWord_2751

theorem g32p_row13_cosetGeneratorBlock_0171 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 171 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 171 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 171 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2736 s
  · exact g32p_row13_cosetGeneratorStep_2737 s
  · exact g32p_row13_cosetGeneratorStep_2738 s
  · exact g32p_row13_cosetGeneratorStep_2739 s
  · exact g32p_row13_cosetGeneratorStep_2740 s
  · exact g32p_row13_cosetGeneratorStep_2741 s
  · exact g32p_row13_cosetGeneratorStep_2742 s
  · exact g32p_row13_cosetGeneratorStep_2743 s
  · exact g32p_row13_cosetGeneratorStep_2744 s
  · exact g32p_row13_cosetGeneratorStep_2745 s
  · exact g32p_row13_cosetGeneratorStep_2746 s
  · exact g32p_row13_cosetGeneratorStep_2747 s
  · exact g32p_row13_cosetGeneratorStep_2748 s
  · exact g32p_row13_cosetGeneratorStep_2749 s
  · exact g32p_row13_cosetGeneratorStep_2750 s
  · exact g32p_row13_cosetGeneratorStep_2751 s

theorem g32p_row13_cosetBranchBlock_0171 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 171 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 171 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 171 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2736 s
  · exact g32p_row13_cosetBranchStep_2737 s
  · exact g32p_row13_cosetBranchStep_2738 s
  · exact g32p_row13_cosetBranchStep_2739 s
  · exact g32p_row13_cosetBranchStep_2740 s
  · exact g32p_row13_cosetBranchStep_2741 s
  · exact g32p_row13_cosetBranchStep_2742 s
  · exact g32p_row13_cosetBranchStep_2743 s
  · exact g32p_row13_cosetBranchStep_2744 s
  · exact g32p_row13_cosetBranchStep_2745 s
  · exact g32p_row13_cosetBranchStep_2746 s
  · exact g32p_row13_cosetBranchStep_2747 s
  · exact g32p_row13_cosetBranchStep_2748 s
  · exact g32p_row13_cosetBranchStep_2749 s
  · exact g32p_row13_cosetBranchStep_2750 s
  · exact g32p_row13_cosetBranchStep_2751 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2752 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2752) = g32p_row13_cosetRepresentatives 2752 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2752 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2752) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2752))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2752)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2752 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2752) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2752))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2752)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2753 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2753) = g32p_row13_cosetRepresentatives 2753 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2753 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2753) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2753))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2753)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2753 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2753) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2753))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2753)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2754 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2754) = g32p_row13_cosetRepresentatives 2754 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2754 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2754) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2754))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2754)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2754 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2754) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2754))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2754)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2755 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2755) = g32p_row13_cosetRepresentatives 2755 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2755 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2755) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2755))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2755)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2755 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2755) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2755))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2755)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2756 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2756) = g32p_row13_cosetRepresentatives 2756 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2756 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2756) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2756))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2756)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2756 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2756) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2756))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2756)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2757 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2757) = g32p_row13_cosetRepresentatives 2757 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2757 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2757) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2757))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2757)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2757 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2757) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2757))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2757)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2758 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2758) = g32p_row13_cosetRepresentatives 2758 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2758 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2758) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2758))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2758)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2758 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2758) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2758))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2758)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2759 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2759) = g32p_row13_cosetRepresentatives 2759 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2759 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2759) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2759))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2759)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2759 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2759) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2759))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2759)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2760 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2760) = g32p_row13_cosetRepresentatives 2760 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2760 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2760) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2760))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2760)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2760 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2760) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2760))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2760)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2761 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2761) = g32p_row13_cosetRepresentatives 2761 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2761 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2761) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2761))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2761)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2761 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2761) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2761))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2761)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2762 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2762) = g32p_row13_cosetRepresentatives 2762 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2762 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2762) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2762))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2762)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2762 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2762) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2762))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2762)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2763 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2763) = g32p_row13_cosetRepresentatives 2763 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2763 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2763) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2763))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2763)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2763 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2763) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2763))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2763)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2764 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2764) = g32p_row13_cosetRepresentatives 2764 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2764 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2764) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2764))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2764)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2764 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2764) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2764))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2764)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2765 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2765) = g32p_row13_cosetRepresentatives 2765 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2765 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2765) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2765))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2765)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2765 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2765) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2765))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2765)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2766 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2766) = g32p_row13_cosetRepresentatives 2766 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2766 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2766) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2766))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2766)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2766 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2766) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2766))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2766)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2767 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2767) = g32p_row13_cosetRepresentatives 2767 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2767 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2767) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2767))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2767)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2767 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2767) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2767))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2767)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0172 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 172 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 172 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2752
  · exact g32p_row13_cosetWord_2753
  · exact g32p_row13_cosetWord_2754
  · exact g32p_row13_cosetWord_2755
  · exact g32p_row13_cosetWord_2756
  · exact g32p_row13_cosetWord_2757
  · exact g32p_row13_cosetWord_2758
  · exact g32p_row13_cosetWord_2759
  · exact g32p_row13_cosetWord_2760
  · exact g32p_row13_cosetWord_2761
  · exact g32p_row13_cosetWord_2762
  · exact g32p_row13_cosetWord_2763
  · exact g32p_row13_cosetWord_2764
  · exact g32p_row13_cosetWord_2765
  · exact g32p_row13_cosetWord_2766
  · exact g32p_row13_cosetWord_2767

theorem g32p_row13_cosetGeneratorBlock_0172 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 172 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 172 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 172 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2752 s
  · exact g32p_row13_cosetGeneratorStep_2753 s
  · exact g32p_row13_cosetGeneratorStep_2754 s
  · exact g32p_row13_cosetGeneratorStep_2755 s
  · exact g32p_row13_cosetGeneratorStep_2756 s
  · exact g32p_row13_cosetGeneratorStep_2757 s
  · exact g32p_row13_cosetGeneratorStep_2758 s
  · exact g32p_row13_cosetGeneratorStep_2759 s
  · exact g32p_row13_cosetGeneratorStep_2760 s
  · exact g32p_row13_cosetGeneratorStep_2761 s
  · exact g32p_row13_cosetGeneratorStep_2762 s
  · exact g32p_row13_cosetGeneratorStep_2763 s
  · exact g32p_row13_cosetGeneratorStep_2764 s
  · exact g32p_row13_cosetGeneratorStep_2765 s
  · exact g32p_row13_cosetGeneratorStep_2766 s
  · exact g32p_row13_cosetGeneratorStep_2767 s

theorem g32p_row13_cosetBranchBlock_0172 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 172 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 172 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 172 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2752 s
  · exact g32p_row13_cosetBranchStep_2753 s
  · exact g32p_row13_cosetBranchStep_2754 s
  · exact g32p_row13_cosetBranchStep_2755 s
  · exact g32p_row13_cosetBranchStep_2756 s
  · exact g32p_row13_cosetBranchStep_2757 s
  · exact g32p_row13_cosetBranchStep_2758 s
  · exact g32p_row13_cosetBranchStep_2759 s
  · exact g32p_row13_cosetBranchStep_2760 s
  · exact g32p_row13_cosetBranchStep_2761 s
  · exact g32p_row13_cosetBranchStep_2762 s
  · exact g32p_row13_cosetBranchStep_2763 s
  · exact g32p_row13_cosetBranchStep_2764 s
  · exact g32p_row13_cosetBranchStep_2765 s
  · exact g32p_row13_cosetBranchStep_2766 s
  · exact g32p_row13_cosetBranchStep_2767 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2768 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2768) = g32p_row13_cosetRepresentatives 2768 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2768 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2768) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2768))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2768)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2768 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2768) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2768))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2768)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2769 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2769) = g32p_row13_cosetRepresentatives 2769 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2769 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2769) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2769))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2769)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2769 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2769) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2769))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2769)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2770 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2770) = g32p_row13_cosetRepresentatives 2770 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2770 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2770) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2770))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2770)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2770 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2770) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2770))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2770)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2771 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2771) = g32p_row13_cosetRepresentatives 2771 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2771 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2771) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2771))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2771)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2771 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2771) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2771))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2771)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2772 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2772) = g32p_row13_cosetRepresentatives 2772 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2772 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2772) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2772))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2772)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2772 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2772) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2772))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2772)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2773 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2773) = g32p_row13_cosetRepresentatives 2773 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2773 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2773) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2773))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2773)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2773 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2773) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2773))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2773)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2774 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2774) = g32p_row13_cosetRepresentatives 2774 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2774 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2774) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2774))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2774)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2774 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2774) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2774))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2774)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2775 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2775) = g32p_row13_cosetRepresentatives 2775 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2775 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2775) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2775))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2775)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2775 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2775) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2775))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2775)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2776 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2776) = g32p_row13_cosetRepresentatives 2776 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2776 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2776) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2776))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2776)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2776 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2776) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2776))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2776)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2777 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2777) = g32p_row13_cosetRepresentatives 2777 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2777 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2777) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2777))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2777)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2777 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2777) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2777))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2777)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2778 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2778) = g32p_row13_cosetRepresentatives 2778 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2778 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2778) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2778))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2778)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2778 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2778) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2778))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2778)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2779 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2779) = g32p_row13_cosetRepresentatives 2779 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2779 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2779) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2779))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2779)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2779 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2779) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2779))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2779)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2780 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2780) = g32p_row13_cosetRepresentatives 2780 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2780 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2780) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2780))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2780)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2780 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2780) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2780))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2780)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2781 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2781) = g32p_row13_cosetRepresentatives 2781 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2781 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2781) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2781))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2781)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2781 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2781) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2781))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2781)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2782 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2782) = g32p_row13_cosetRepresentatives 2782 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2782 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2782) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2782))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2782)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2782 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2782) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2782))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2782)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2783 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2783) = g32p_row13_cosetRepresentatives 2783 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2783 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2783) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2783))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2783)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2783 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2783) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2783))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2783)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0173 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 173 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 173 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2768
  · exact g32p_row13_cosetWord_2769
  · exact g32p_row13_cosetWord_2770
  · exact g32p_row13_cosetWord_2771
  · exact g32p_row13_cosetWord_2772
  · exact g32p_row13_cosetWord_2773
  · exact g32p_row13_cosetWord_2774
  · exact g32p_row13_cosetWord_2775
  · exact g32p_row13_cosetWord_2776
  · exact g32p_row13_cosetWord_2777
  · exact g32p_row13_cosetWord_2778
  · exact g32p_row13_cosetWord_2779
  · exact g32p_row13_cosetWord_2780
  · exact g32p_row13_cosetWord_2781
  · exact g32p_row13_cosetWord_2782
  · exact g32p_row13_cosetWord_2783

theorem g32p_row13_cosetGeneratorBlock_0173 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 173 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 173 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 173 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2768 s
  · exact g32p_row13_cosetGeneratorStep_2769 s
  · exact g32p_row13_cosetGeneratorStep_2770 s
  · exact g32p_row13_cosetGeneratorStep_2771 s
  · exact g32p_row13_cosetGeneratorStep_2772 s
  · exact g32p_row13_cosetGeneratorStep_2773 s
  · exact g32p_row13_cosetGeneratorStep_2774 s
  · exact g32p_row13_cosetGeneratorStep_2775 s
  · exact g32p_row13_cosetGeneratorStep_2776 s
  · exact g32p_row13_cosetGeneratorStep_2777 s
  · exact g32p_row13_cosetGeneratorStep_2778 s
  · exact g32p_row13_cosetGeneratorStep_2779 s
  · exact g32p_row13_cosetGeneratorStep_2780 s
  · exact g32p_row13_cosetGeneratorStep_2781 s
  · exact g32p_row13_cosetGeneratorStep_2782 s
  · exact g32p_row13_cosetGeneratorStep_2783 s

theorem g32p_row13_cosetBranchBlock_0173 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 173 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 173 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 173 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2768 s
  · exact g32p_row13_cosetBranchStep_2769 s
  · exact g32p_row13_cosetBranchStep_2770 s
  · exact g32p_row13_cosetBranchStep_2771 s
  · exact g32p_row13_cosetBranchStep_2772 s
  · exact g32p_row13_cosetBranchStep_2773 s
  · exact g32p_row13_cosetBranchStep_2774 s
  · exact g32p_row13_cosetBranchStep_2775 s
  · exact g32p_row13_cosetBranchStep_2776 s
  · exact g32p_row13_cosetBranchStep_2777 s
  · exact g32p_row13_cosetBranchStep_2778 s
  · exact g32p_row13_cosetBranchStep_2779 s
  · exact g32p_row13_cosetBranchStep_2780 s
  · exact g32p_row13_cosetBranchStep_2781 s
  · exact g32p_row13_cosetBranchStep_2782 s
  · exact g32p_row13_cosetBranchStep_2783 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2784 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2784) = g32p_row13_cosetRepresentatives 2784 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2784 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2784) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2784))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2784)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2784 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2784) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2784))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2784)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2785 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2785) = g32p_row13_cosetRepresentatives 2785 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2785 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2785) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2785))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2785)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2785 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2785) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2785))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2785)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2786 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2786) = g32p_row13_cosetRepresentatives 2786 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2786 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2786) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2786))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2786)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2786 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2786) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2786))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2786)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2787 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2787) = g32p_row13_cosetRepresentatives 2787 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2787 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2787) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2787))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2787)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2787 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2787) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2787))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2787)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2788 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2788) = g32p_row13_cosetRepresentatives 2788 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2788 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2788) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2788))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2788)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2788 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2788) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2788))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2788)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2789 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2789) = g32p_row13_cosetRepresentatives 2789 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2789 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2789) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2789))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2789)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2789 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2789) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2789))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2789)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2790 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2790) = g32p_row13_cosetRepresentatives 2790 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2790 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2790) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2790))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2790)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2790 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2790) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2790))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2790)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2791 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2791) = g32p_row13_cosetRepresentatives 2791 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2791 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2791) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2791))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2791)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2791 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2791) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2791))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2791)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2792 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2792) = g32p_row13_cosetRepresentatives 2792 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2792 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2792) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2792))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2792)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2792 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2792) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2792))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2792)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2793 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2793) = g32p_row13_cosetRepresentatives 2793 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2793 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2793) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2793))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2793)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2793 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2793) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2793))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2793)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2794 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2794) = g32p_row13_cosetRepresentatives 2794 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2794 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2794) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2794))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2794)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2794 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2794) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2794))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2794)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2795 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2795) = g32p_row13_cosetRepresentatives 2795 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2795 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2795) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2795))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2795)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2795 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2795) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2795))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2795)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2796 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2796) = g32p_row13_cosetRepresentatives 2796 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2796 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2796) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2796))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2796)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2796 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2796) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2796))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2796)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2797 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2797) = g32p_row13_cosetRepresentatives 2797 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2797 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2797) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2797))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2797)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2797 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2797) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2797))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2797)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2798 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2798) = g32p_row13_cosetRepresentatives 2798 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2798 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2798) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2798))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2798)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2798 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2798) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2798))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2798)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2799 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2799) = g32p_row13_cosetRepresentatives 2799 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2799 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2799) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2799))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2799)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2799 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2799) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2799))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2799)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0174 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 174 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 174 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2784
  · exact g32p_row13_cosetWord_2785
  · exact g32p_row13_cosetWord_2786
  · exact g32p_row13_cosetWord_2787
  · exact g32p_row13_cosetWord_2788
  · exact g32p_row13_cosetWord_2789
  · exact g32p_row13_cosetWord_2790
  · exact g32p_row13_cosetWord_2791
  · exact g32p_row13_cosetWord_2792
  · exact g32p_row13_cosetWord_2793
  · exact g32p_row13_cosetWord_2794
  · exact g32p_row13_cosetWord_2795
  · exact g32p_row13_cosetWord_2796
  · exact g32p_row13_cosetWord_2797
  · exact g32p_row13_cosetWord_2798
  · exact g32p_row13_cosetWord_2799

theorem g32p_row13_cosetGeneratorBlock_0174 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 174 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 174 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 174 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2784 s
  · exact g32p_row13_cosetGeneratorStep_2785 s
  · exact g32p_row13_cosetGeneratorStep_2786 s
  · exact g32p_row13_cosetGeneratorStep_2787 s
  · exact g32p_row13_cosetGeneratorStep_2788 s
  · exact g32p_row13_cosetGeneratorStep_2789 s
  · exact g32p_row13_cosetGeneratorStep_2790 s
  · exact g32p_row13_cosetGeneratorStep_2791 s
  · exact g32p_row13_cosetGeneratorStep_2792 s
  · exact g32p_row13_cosetGeneratorStep_2793 s
  · exact g32p_row13_cosetGeneratorStep_2794 s
  · exact g32p_row13_cosetGeneratorStep_2795 s
  · exact g32p_row13_cosetGeneratorStep_2796 s
  · exact g32p_row13_cosetGeneratorStep_2797 s
  · exact g32p_row13_cosetGeneratorStep_2798 s
  · exact g32p_row13_cosetGeneratorStep_2799 s

theorem g32p_row13_cosetBranchBlock_0174 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 174 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 174 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 174 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2784 s
  · exact g32p_row13_cosetBranchStep_2785 s
  · exact g32p_row13_cosetBranchStep_2786 s
  · exact g32p_row13_cosetBranchStep_2787 s
  · exact g32p_row13_cosetBranchStep_2788 s
  · exact g32p_row13_cosetBranchStep_2789 s
  · exact g32p_row13_cosetBranchStep_2790 s
  · exact g32p_row13_cosetBranchStep_2791 s
  · exact g32p_row13_cosetBranchStep_2792 s
  · exact g32p_row13_cosetBranchStep_2793 s
  · exact g32p_row13_cosetBranchStep_2794 s
  · exact g32p_row13_cosetBranchStep_2795 s
  · exact g32p_row13_cosetBranchStep_2796 s
  · exact g32p_row13_cosetBranchStep_2797 s
  · exact g32p_row13_cosetBranchStep_2798 s
  · exact g32p_row13_cosetBranchStep_2799 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2800 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2800) = g32p_row13_cosetRepresentatives 2800 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2800 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2800) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2800))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2800)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2800 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2800) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2800))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2800)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2801 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2801) = g32p_row13_cosetRepresentatives 2801 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2801 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2801) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2801))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2801)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2801 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2801) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2801))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2801)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2802 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2802) = g32p_row13_cosetRepresentatives 2802 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2802 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2802) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2802))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2802)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2802 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2802) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2802))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2802)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2803 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2803) = g32p_row13_cosetRepresentatives 2803 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2803 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2803) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2803))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2803)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2803 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2803) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2803))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2803)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2804 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2804) = g32p_row13_cosetRepresentatives 2804 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2804 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2804) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2804))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2804)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2804 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2804) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2804))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2804)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2805 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2805) = g32p_row13_cosetRepresentatives 2805 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2805 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2805) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2805))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2805)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2805 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2805) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2805))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2805)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2806 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2806) = g32p_row13_cosetRepresentatives 2806 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2806 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2806) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2806))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2806)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2806 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2806) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2806))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2806)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2807 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2807) = g32p_row13_cosetRepresentatives 2807 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2807 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2807) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2807))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2807)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2807 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2807) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2807))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2807)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2808 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2808) = g32p_row13_cosetRepresentatives 2808 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2808 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2808) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2808))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2808)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2808 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2808) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2808))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2808)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2809 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2809) = g32p_row13_cosetRepresentatives 2809 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2809 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2809) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2809))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2809)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2809 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2809) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2809))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2809)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2810 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2810) = g32p_row13_cosetRepresentatives 2810 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2810 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2810) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2810))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2810)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2810 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2810) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2810))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2810)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2811 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2811) = g32p_row13_cosetRepresentatives 2811 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2811 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2811) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2811))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2811)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2811 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2811) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2811))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2811)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2812 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2812) = g32p_row13_cosetRepresentatives 2812 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2812 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2812) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2812))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2812)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2812 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2812) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2812))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2812)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2813 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2813) = g32p_row13_cosetRepresentatives 2813 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2813 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2813) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2813))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2813)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2813 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2813) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2813))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2813)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2814 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2814) = g32p_row13_cosetRepresentatives 2814 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2814 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2814) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2814))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2814)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2814 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2814) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2814))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2814)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2815 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2815) = g32p_row13_cosetRepresentatives 2815 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2815 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2815) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2815))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2815)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2815 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2815) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2815))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2815)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0175 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 175 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 175 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2800
  · exact g32p_row13_cosetWord_2801
  · exact g32p_row13_cosetWord_2802
  · exact g32p_row13_cosetWord_2803
  · exact g32p_row13_cosetWord_2804
  · exact g32p_row13_cosetWord_2805
  · exact g32p_row13_cosetWord_2806
  · exact g32p_row13_cosetWord_2807
  · exact g32p_row13_cosetWord_2808
  · exact g32p_row13_cosetWord_2809
  · exact g32p_row13_cosetWord_2810
  · exact g32p_row13_cosetWord_2811
  · exact g32p_row13_cosetWord_2812
  · exact g32p_row13_cosetWord_2813
  · exact g32p_row13_cosetWord_2814
  · exact g32p_row13_cosetWord_2815

theorem g32p_row13_cosetGeneratorBlock_0175 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 175 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 175 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 175 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2800 s
  · exact g32p_row13_cosetGeneratorStep_2801 s
  · exact g32p_row13_cosetGeneratorStep_2802 s
  · exact g32p_row13_cosetGeneratorStep_2803 s
  · exact g32p_row13_cosetGeneratorStep_2804 s
  · exact g32p_row13_cosetGeneratorStep_2805 s
  · exact g32p_row13_cosetGeneratorStep_2806 s
  · exact g32p_row13_cosetGeneratorStep_2807 s
  · exact g32p_row13_cosetGeneratorStep_2808 s
  · exact g32p_row13_cosetGeneratorStep_2809 s
  · exact g32p_row13_cosetGeneratorStep_2810 s
  · exact g32p_row13_cosetGeneratorStep_2811 s
  · exact g32p_row13_cosetGeneratorStep_2812 s
  · exact g32p_row13_cosetGeneratorStep_2813 s
  · exact g32p_row13_cosetGeneratorStep_2814 s
  · exact g32p_row13_cosetGeneratorStep_2815 s

theorem g32p_row13_cosetBranchBlock_0175 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 175 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 175 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 175 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2800 s
  · exact g32p_row13_cosetBranchStep_2801 s
  · exact g32p_row13_cosetBranchStep_2802 s
  · exact g32p_row13_cosetBranchStep_2803 s
  · exact g32p_row13_cosetBranchStep_2804 s
  · exact g32p_row13_cosetBranchStep_2805 s
  · exact g32p_row13_cosetBranchStep_2806 s
  · exact g32p_row13_cosetBranchStep_2807 s
  · exact g32p_row13_cosetBranchStep_2808 s
  · exact g32p_row13_cosetBranchStep_2809 s
  · exact g32p_row13_cosetBranchStep_2810 s
  · exact g32p_row13_cosetBranchStep_2811 s
  · exact g32p_row13_cosetBranchStep_2812 s
  · exact g32p_row13_cosetBranchStep_2813 s
  · exact g32p_row13_cosetBranchStep_2814 s
  · exact g32p_row13_cosetBranchStep_2815 s


end HodgeLean.Foundations.Program

end
