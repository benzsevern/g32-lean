import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0835
import HodgeLean.Foundations.Program.G32PropFourSixPacked0836
import HodgeLean.Foundations.Program.G32PropFourSixPacked0837
import HodgeLean.Foundations.Program.G32PropFourSixPacked0838
import HodgeLean.Foundations.Program.G32PropFourSixPacked0839
import HodgeLean.Foundations.Program.G32PropFourSixPacked0840
import HodgeLean.Foundations.Program.G32PropFourSixPacked0841
import HodgeLean.Foundations.Program.G32PropFourSixPacked0842
import HodgeLean.Foundations.Program.G32PropFourSixPacked0843
import HodgeLean.Foundations.Program.G32PropFourSixPacked0844
import HodgeLean.Foundations.Program.G32PropFourSixPacked0845
import HodgeLean.Foundations.Program.G32PropFourSixPacked0846
import HodgeLean.Foundations.Program.G32PropFourSixPacked0847
import HodgeLean.Foundations.Program.G32PropFourSixPacked0848
import HodgeLean.Foundations.Program.G32PropFourSixPacked0849
import HodgeLean.Foundations.Program.G32PropFourSixPacked0850
import HodgeLean.Foundations.Program.G32PropFourSixPacked0851
import HodgeLean.Foundations.Program.G32PropFourSixPacked0852
import HodgeLean.Foundations.Program.G32PropFourSixPacked0853
import HodgeLean.Foundations.Program.G32PropFourSixPacked0854
import HodgeLean.Foundations.Program.G32PropFourSixPacked0855
import HodgeLean.Foundations.Program.G32PropFourSixPacked0856
import HodgeLean.Foundations.Program.G32PropFourSixPacked0857
import HodgeLean.Foundations.Program.G32PropFourSixPacked0858
import HodgeLean.Foundations.Program.G32PropFourSixPacked0859
import HodgeLean.Foundations.Program.G32PropFourSixPacked0860
import HodgeLean.Foundations.Program.G32PropFourSixPacked0861
import HodgeLean.Foundations.Program.G32PropFourSixPacked0862
import HodgeLean.Foundations.Program.G32PropFourSixPacked0863
import HodgeLean.Foundations.Program.G32PropFourSixPacked0864
import HodgeLean.Foundations.Program.G32PropFourSixPacked0865
import HodgeLean.Foundations.Program.G32PropFourSixPacked0866
import HodgeLean.Foundations.Program.G32PropFourSixPacked0867
import HodgeLean.Foundations.Program.G32PropFourSixPacked0868
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow31
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8448 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8448) = g32p_row31_cosetRepresentatives 8448 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8448 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8448) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8448))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8448)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8448 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8448) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8448))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8448)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8449 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8449) = g32p_row31_cosetRepresentatives 8449 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8449 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8449) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8449))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8449)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8449 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8449) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8449))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8449)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8450 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8450) = g32p_row31_cosetRepresentatives 8450 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8450 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8450) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8450))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8450)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8450 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8450) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8450))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8450)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8451 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8451) = g32p_row31_cosetRepresentatives 8451 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8451 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8451) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8451))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8451)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8451 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8451) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8451))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8451)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8452 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8452) = g32p_row31_cosetRepresentatives 8452 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8452 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8452) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8452))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8452)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8452 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8452) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8452))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8452)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8453 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8453) = g32p_row31_cosetRepresentatives 8453 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8453 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8453) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8453))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8453)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8453 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8453) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8453))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8453)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8454 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8454) = g32p_row31_cosetRepresentatives 8454 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8454 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8454) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8454))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8454)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8454 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8454) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8454))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8454)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8455 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8455) = g32p_row31_cosetRepresentatives 8455 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8455 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8455) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8455))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8455)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8455 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8455) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8455))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8455)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8456 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8456) = g32p_row31_cosetRepresentatives 8456 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8456 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8456) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8456))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8456)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8456 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8456) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8456))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8456)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8457 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8457) = g32p_row31_cosetRepresentatives 8457 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8457 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8457) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8457))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8457)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8457 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8457) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8457))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8457)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8458 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8458) = g32p_row31_cosetRepresentatives 8458 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8458 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8458) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8458))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8458)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8458 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8458) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8458))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8458)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8459 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8459) = g32p_row31_cosetRepresentatives 8459 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8459 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8459) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8459))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8459)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8459 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8459) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8459))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8459)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8460 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8460) = g32p_row31_cosetRepresentatives 8460 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8460 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8460) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8460))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8460)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8460 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8460) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8460))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8460)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8461 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8461) = g32p_row31_cosetRepresentatives 8461 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8461 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8461) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8461))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8461)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8461 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8461) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8461))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8461)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8462 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8462) = g32p_row31_cosetRepresentatives 8462 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8462 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8462) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8462))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8462)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8462 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8462) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8462))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8462)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8463 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8463) = g32p_row31_cosetRepresentatives 8463 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8463 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8463) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8463))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8463)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8463 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8463) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8463))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8463)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0528 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 528 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 528 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8448
  · exact g32p_row31_cosetWord_8449
  · exact g32p_row31_cosetWord_8450
  · exact g32p_row31_cosetWord_8451
  · exact g32p_row31_cosetWord_8452
  · exact g32p_row31_cosetWord_8453
  · exact g32p_row31_cosetWord_8454
  · exact g32p_row31_cosetWord_8455
  · exact g32p_row31_cosetWord_8456
  · exact g32p_row31_cosetWord_8457
  · exact g32p_row31_cosetWord_8458
  · exact g32p_row31_cosetWord_8459
  · exact g32p_row31_cosetWord_8460
  · exact g32p_row31_cosetWord_8461
  · exact g32p_row31_cosetWord_8462
  · exact g32p_row31_cosetWord_8463

theorem g32p_row31_cosetGeneratorBlock_0528 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 528 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 528 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 528 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8448 s
  · exact g32p_row31_cosetGeneratorStep_8449 s
  · exact g32p_row31_cosetGeneratorStep_8450 s
  · exact g32p_row31_cosetGeneratorStep_8451 s
  · exact g32p_row31_cosetGeneratorStep_8452 s
  · exact g32p_row31_cosetGeneratorStep_8453 s
  · exact g32p_row31_cosetGeneratorStep_8454 s
  · exact g32p_row31_cosetGeneratorStep_8455 s
  · exact g32p_row31_cosetGeneratorStep_8456 s
  · exact g32p_row31_cosetGeneratorStep_8457 s
  · exact g32p_row31_cosetGeneratorStep_8458 s
  · exact g32p_row31_cosetGeneratorStep_8459 s
  · exact g32p_row31_cosetGeneratorStep_8460 s
  · exact g32p_row31_cosetGeneratorStep_8461 s
  · exact g32p_row31_cosetGeneratorStep_8462 s
  · exact g32p_row31_cosetGeneratorStep_8463 s

theorem g32p_row31_cosetBranchBlock_0528 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 528 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 528 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 528 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8448 s
  · exact g32p_row31_cosetBranchStep_8449 s
  · exact g32p_row31_cosetBranchStep_8450 s
  · exact g32p_row31_cosetBranchStep_8451 s
  · exact g32p_row31_cosetBranchStep_8452 s
  · exact g32p_row31_cosetBranchStep_8453 s
  · exact g32p_row31_cosetBranchStep_8454 s
  · exact g32p_row31_cosetBranchStep_8455 s
  · exact g32p_row31_cosetBranchStep_8456 s
  · exact g32p_row31_cosetBranchStep_8457 s
  · exact g32p_row31_cosetBranchStep_8458 s
  · exact g32p_row31_cosetBranchStep_8459 s
  · exact g32p_row31_cosetBranchStep_8460 s
  · exact g32p_row31_cosetBranchStep_8461 s
  · exact g32p_row31_cosetBranchStep_8462 s
  · exact g32p_row31_cosetBranchStep_8463 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8464 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8464) = g32p_row31_cosetRepresentatives 8464 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8464 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8464) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8464))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8464)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8464 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8464) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8464))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8464)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8465 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8465) = g32p_row31_cosetRepresentatives 8465 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8465 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8465) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8465))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8465)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8465 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8465) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8465))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8465)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8466 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8466) = g32p_row31_cosetRepresentatives 8466 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8466 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8466) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8466))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8466)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8466 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8466) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8466))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8466)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8467 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8467) = g32p_row31_cosetRepresentatives 8467 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8467 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8467) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8467))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8467)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8467 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8467) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8467))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8467)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8468 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8468) = g32p_row31_cosetRepresentatives 8468 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8468 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8468) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8468))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8468)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8468 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8468) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8468))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8468)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8469 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8469) = g32p_row31_cosetRepresentatives 8469 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8469 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8469) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8469))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8469)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8469 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8469) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8469))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8469)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8470 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8470) = g32p_row31_cosetRepresentatives 8470 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8470 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8470) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8470))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8470)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8470 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8470) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8470))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8470)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8471 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8471) = g32p_row31_cosetRepresentatives 8471 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8471 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8471) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8471))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8471)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8471 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8471) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8471))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8471)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8472 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8472) = g32p_row31_cosetRepresentatives 8472 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8472 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8472) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8472))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8472)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8472 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8472) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8472))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8472)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8473 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8473) = g32p_row31_cosetRepresentatives 8473 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8473 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8473) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8473))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8473)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8473 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8473) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8473))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8473)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8474 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8474) = g32p_row31_cosetRepresentatives 8474 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8474 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8474) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8474))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8474)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8474 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8474) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8474))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8474)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8475 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8475) = g32p_row31_cosetRepresentatives 8475 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8475 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8475) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8475))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8475)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8475 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8475) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8475))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8475)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8476 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8476) = g32p_row31_cosetRepresentatives 8476 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8476 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8476) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8476))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8476)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8476 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8476) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8476))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8476)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8477 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8477) = g32p_row31_cosetRepresentatives 8477 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8477 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8477) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8477))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8477)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8477 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8477) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8477))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8477)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8478 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8478) = g32p_row31_cosetRepresentatives 8478 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8478 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8478) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8478))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8478)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8478 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8478) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8478))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8478)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8479 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8479) = g32p_row31_cosetRepresentatives 8479 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8479 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8479) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8479))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8479)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8479 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8479) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8479))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8479)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0529 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 529 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 529 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8464
  · exact g32p_row31_cosetWord_8465
  · exact g32p_row31_cosetWord_8466
  · exact g32p_row31_cosetWord_8467
  · exact g32p_row31_cosetWord_8468
  · exact g32p_row31_cosetWord_8469
  · exact g32p_row31_cosetWord_8470
  · exact g32p_row31_cosetWord_8471
  · exact g32p_row31_cosetWord_8472
  · exact g32p_row31_cosetWord_8473
  · exact g32p_row31_cosetWord_8474
  · exact g32p_row31_cosetWord_8475
  · exact g32p_row31_cosetWord_8476
  · exact g32p_row31_cosetWord_8477
  · exact g32p_row31_cosetWord_8478
  · exact g32p_row31_cosetWord_8479

theorem g32p_row31_cosetGeneratorBlock_0529 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 529 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 529 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 529 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8464 s
  · exact g32p_row31_cosetGeneratorStep_8465 s
  · exact g32p_row31_cosetGeneratorStep_8466 s
  · exact g32p_row31_cosetGeneratorStep_8467 s
  · exact g32p_row31_cosetGeneratorStep_8468 s
  · exact g32p_row31_cosetGeneratorStep_8469 s
  · exact g32p_row31_cosetGeneratorStep_8470 s
  · exact g32p_row31_cosetGeneratorStep_8471 s
  · exact g32p_row31_cosetGeneratorStep_8472 s
  · exact g32p_row31_cosetGeneratorStep_8473 s
  · exact g32p_row31_cosetGeneratorStep_8474 s
  · exact g32p_row31_cosetGeneratorStep_8475 s
  · exact g32p_row31_cosetGeneratorStep_8476 s
  · exact g32p_row31_cosetGeneratorStep_8477 s
  · exact g32p_row31_cosetGeneratorStep_8478 s
  · exact g32p_row31_cosetGeneratorStep_8479 s

theorem g32p_row31_cosetBranchBlock_0529 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 529 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 529 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 529 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8464 s
  · exact g32p_row31_cosetBranchStep_8465 s
  · exact g32p_row31_cosetBranchStep_8466 s
  · exact g32p_row31_cosetBranchStep_8467 s
  · exact g32p_row31_cosetBranchStep_8468 s
  · exact g32p_row31_cosetBranchStep_8469 s
  · exact g32p_row31_cosetBranchStep_8470 s
  · exact g32p_row31_cosetBranchStep_8471 s
  · exact g32p_row31_cosetBranchStep_8472 s
  · exact g32p_row31_cosetBranchStep_8473 s
  · exact g32p_row31_cosetBranchStep_8474 s
  · exact g32p_row31_cosetBranchStep_8475 s
  · exact g32p_row31_cosetBranchStep_8476 s
  · exact g32p_row31_cosetBranchStep_8477 s
  · exact g32p_row31_cosetBranchStep_8478 s
  · exact g32p_row31_cosetBranchStep_8479 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8480 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8480) = g32p_row31_cosetRepresentatives 8480 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8480 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8480) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8480))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8480)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8480 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8480) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8480))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8480)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8481 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8481) = g32p_row31_cosetRepresentatives 8481 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8481 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8481) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8481))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8481)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8481 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8481) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8481))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8481)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8482 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8482) = g32p_row31_cosetRepresentatives 8482 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8482 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8482) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8482))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8482)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8482 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8482) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8482))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8482)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8483 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8483) = g32p_row31_cosetRepresentatives 8483 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8483 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8483) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8483))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8483)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8483 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8483) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8483))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8483)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8484 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8484) = g32p_row31_cosetRepresentatives 8484 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8484 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8484) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8484))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8484)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8484 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8484) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8484))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8484)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8485 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8485) = g32p_row31_cosetRepresentatives 8485 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8485 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8485) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8485))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8485)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8485 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8485) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8485))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8485)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8486 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8486) = g32p_row31_cosetRepresentatives 8486 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8486 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8486) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8486))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8486)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8486 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8486) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8486))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8486)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8487 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8487) = g32p_row31_cosetRepresentatives 8487 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8487 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8487) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8487))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8487)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8487 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8487) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8487))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8487)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8488 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8488) = g32p_row31_cosetRepresentatives 8488 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8488 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8488) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8488))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8488)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8488 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8488) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8488))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8488)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8489 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8489) = g32p_row31_cosetRepresentatives 8489 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8489 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8489) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8489))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8489)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8489 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8489) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8489))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8489)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8490 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8490) = g32p_row31_cosetRepresentatives 8490 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8490 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8490) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8490))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8490)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8490 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8490) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8490))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8490)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8491 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8491) = g32p_row31_cosetRepresentatives 8491 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8491 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8491) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8491))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8491)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8491 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8491) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8491))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8491)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8492 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8492) = g32p_row31_cosetRepresentatives 8492 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8492 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8492) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8492))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8492)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8492 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8492) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8492))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8492)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8493 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8493) = g32p_row31_cosetRepresentatives 8493 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8493 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8493) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8493))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8493)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8493 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8493) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8493))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8493)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8494 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8494) = g32p_row31_cosetRepresentatives 8494 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8494 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8494) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8494))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8494)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8494 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8494) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8494))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8494)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8495 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8495) = g32p_row31_cosetRepresentatives 8495 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8495 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8495) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8495))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8495)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8495 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8495) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8495))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8495)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0530 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 530 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 530 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8480
  · exact g32p_row31_cosetWord_8481
  · exact g32p_row31_cosetWord_8482
  · exact g32p_row31_cosetWord_8483
  · exact g32p_row31_cosetWord_8484
  · exact g32p_row31_cosetWord_8485
  · exact g32p_row31_cosetWord_8486
  · exact g32p_row31_cosetWord_8487
  · exact g32p_row31_cosetWord_8488
  · exact g32p_row31_cosetWord_8489
  · exact g32p_row31_cosetWord_8490
  · exact g32p_row31_cosetWord_8491
  · exact g32p_row31_cosetWord_8492
  · exact g32p_row31_cosetWord_8493
  · exact g32p_row31_cosetWord_8494
  · exact g32p_row31_cosetWord_8495

theorem g32p_row31_cosetGeneratorBlock_0530 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 530 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 530 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 530 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8480 s
  · exact g32p_row31_cosetGeneratorStep_8481 s
  · exact g32p_row31_cosetGeneratorStep_8482 s
  · exact g32p_row31_cosetGeneratorStep_8483 s
  · exact g32p_row31_cosetGeneratorStep_8484 s
  · exact g32p_row31_cosetGeneratorStep_8485 s
  · exact g32p_row31_cosetGeneratorStep_8486 s
  · exact g32p_row31_cosetGeneratorStep_8487 s
  · exact g32p_row31_cosetGeneratorStep_8488 s
  · exact g32p_row31_cosetGeneratorStep_8489 s
  · exact g32p_row31_cosetGeneratorStep_8490 s
  · exact g32p_row31_cosetGeneratorStep_8491 s
  · exact g32p_row31_cosetGeneratorStep_8492 s
  · exact g32p_row31_cosetGeneratorStep_8493 s
  · exact g32p_row31_cosetGeneratorStep_8494 s
  · exact g32p_row31_cosetGeneratorStep_8495 s

theorem g32p_row31_cosetBranchBlock_0530 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 530 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 530 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 530 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8480 s
  · exact g32p_row31_cosetBranchStep_8481 s
  · exact g32p_row31_cosetBranchStep_8482 s
  · exact g32p_row31_cosetBranchStep_8483 s
  · exact g32p_row31_cosetBranchStep_8484 s
  · exact g32p_row31_cosetBranchStep_8485 s
  · exact g32p_row31_cosetBranchStep_8486 s
  · exact g32p_row31_cosetBranchStep_8487 s
  · exact g32p_row31_cosetBranchStep_8488 s
  · exact g32p_row31_cosetBranchStep_8489 s
  · exact g32p_row31_cosetBranchStep_8490 s
  · exact g32p_row31_cosetBranchStep_8491 s
  · exact g32p_row31_cosetBranchStep_8492 s
  · exact g32p_row31_cosetBranchStep_8493 s
  · exact g32p_row31_cosetBranchStep_8494 s
  · exact g32p_row31_cosetBranchStep_8495 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8496 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8496) = g32p_row31_cosetRepresentatives 8496 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8496 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8496) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8496))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8496)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8496 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8496) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8496))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8496)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8497 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8497) = g32p_row31_cosetRepresentatives 8497 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8497 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8497) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8497))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8497)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8497 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8497) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8497))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8497)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8498 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8498) = g32p_row31_cosetRepresentatives 8498 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8498 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8498) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8498))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8498)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8498 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8498) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8498))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8498)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8499 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8499) = g32p_row31_cosetRepresentatives 8499 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8499 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8499) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8499))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8499)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8499 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8499) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8499))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8499)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8500 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8500) = g32p_row31_cosetRepresentatives 8500 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8500 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8500) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8500))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8500)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8500 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8500) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8500))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8500)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8501 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8501) = g32p_row31_cosetRepresentatives 8501 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8501 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8501) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8501))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8501)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8501 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8501) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8501))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8501)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8502 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8502) = g32p_row31_cosetRepresentatives 8502 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8502 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8502) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8502))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8502)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8502 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8502) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8502))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8502)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8503 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8503) = g32p_row31_cosetRepresentatives 8503 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8503 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8503) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8503))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8503)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8503 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8503) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8503))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8503)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8504 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8504) = g32p_row31_cosetRepresentatives 8504 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8504 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8504) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8504))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8504)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8504 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8504) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8504))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8504)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8505 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8505) = g32p_row31_cosetRepresentatives 8505 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8505 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8505) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8505))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8505)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8505 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8505) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8505))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8505)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8506 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8506) = g32p_row31_cosetRepresentatives 8506 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8506 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8506) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8506))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8506)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8506 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8506) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8506))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8506)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8507 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8507) = g32p_row31_cosetRepresentatives 8507 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8507 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8507) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8507))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8507)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8507 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8507) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8507))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8507)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8508 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8508) = g32p_row31_cosetRepresentatives 8508 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8508 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8508) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8508))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8508)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8508 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8508) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8508))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8508)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8509 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8509) = g32p_row31_cosetRepresentatives 8509 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8509 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8509) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8509))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8509)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8509 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8509) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8509))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8509)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8510 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8510) = g32p_row31_cosetRepresentatives 8510 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8510 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8510) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8510))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8510)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8510 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8510) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8510))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8510)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8511 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8511) = g32p_row31_cosetRepresentatives 8511 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8511 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8511) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8511))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8511)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8511 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8511) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8511))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8511)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0531 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 531 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 531 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8496
  · exact g32p_row31_cosetWord_8497
  · exact g32p_row31_cosetWord_8498
  · exact g32p_row31_cosetWord_8499
  · exact g32p_row31_cosetWord_8500
  · exact g32p_row31_cosetWord_8501
  · exact g32p_row31_cosetWord_8502
  · exact g32p_row31_cosetWord_8503
  · exact g32p_row31_cosetWord_8504
  · exact g32p_row31_cosetWord_8505
  · exact g32p_row31_cosetWord_8506
  · exact g32p_row31_cosetWord_8507
  · exact g32p_row31_cosetWord_8508
  · exact g32p_row31_cosetWord_8509
  · exact g32p_row31_cosetWord_8510
  · exact g32p_row31_cosetWord_8511

theorem g32p_row31_cosetGeneratorBlock_0531 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 531 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 531 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 531 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8496 s
  · exact g32p_row31_cosetGeneratorStep_8497 s
  · exact g32p_row31_cosetGeneratorStep_8498 s
  · exact g32p_row31_cosetGeneratorStep_8499 s
  · exact g32p_row31_cosetGeneratorStep_8500 s
  · exact g32p_row31_cosetGeneratorStep_8501 s
  · exact g32p_row31_cosetGeneratorStep_8502 s
  · exact g32p_row31_cosetGeneratorStep_8503 s
  · exact g32p_row31_cosetGeneratorStep_8504 s
  · exact g32p_row31_cosetGeneratorStep_8505 s
  · exact g32p_row31_cosetGeneratorStep_8506 s
  · exact g32p_row31_cosetGeneratorStep_8507 s
  · exact g32p_row31_cosetGeneratorStep_8508 s
  · exact g32p_row31_cosetGeneratorStep_8509 s
  · exact g32p_row31_cosetGeneratorStep_8510 s
  · exact g32p_row31_cosetGeneratorStep_8511 s

theorem g32p_row31_cosetBranchBlock_0531 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 531 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 531 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 531 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8496 s
  · exact g32p_row31_cosetBranchStep_8497 s
  · exact g32p_row31_cosetBranchStep_8498 s
  · exact g32p_row31_cosetBranchStep_8499 s
  · exact g32p_row31_cosetBranchStep_8500 s
  · exact g32p_row31_cosetBranchStep_8501 s
  · exact g32p_row31_cosetBranchStep_8502 s
  · exact g32p_row31_cosetBranchStep_8503 s
  · exact g32p_row31_cosetBranchStep_8504 s
  · exact g32p_row31_cosetBranchStep_8505 s
  · exact g32p_row31_cosetBranchStep_8506 s
  · exact g32p_row31_cosetBranchStep_8507 s
  · exact g32p_row31_cosetBranchStep_8508 s
  · exact g32p_row31_cosetBranchStep_8509 s
  · exact g32p_row31_cosetBranchStep_8510 s
  · exact g32p_row31_cosetBranchStep_8511 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8512 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8512) = g32p_row31_cosetRepresentatives 8512 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8512 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8512) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8512))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8512)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8512 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8512) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8512))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8512)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8513 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8513) = g32p_row31_cosetRepresentatives 8513 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8513 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8513) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8513))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8513)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8513 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8513) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8513))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8513)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8514 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8514) = g32p_row31_cosetRepresentatives 8514 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8514 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8514) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8514))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8514)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8514 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8514) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8514))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8514)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8515 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8515) = g32p_row31_cosetRepresentatives 8515 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8515 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8515) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8515))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8515)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8515 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8515) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8515))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8515)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8516 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8516) = g32p_row31_cosetRepresentatives 8516 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8516 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8516) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8516))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8516)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8516 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8516) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8516))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8516)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8517 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8517) = g32p_row31_cosetRepresentatives 8517 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8517 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8517) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8517))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8517)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8517 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8517) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8517))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8517)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8518 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8518) = g32p_row31_cosetRepresentatives 8518 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8518 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8518) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8518))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8518)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8518 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8518) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8518))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8518)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8519 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8519) = g32p_row31_cosetRepresentatives 8519 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8519 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8519) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8519))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8519)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8519 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8519) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8519))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8519)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8520 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8520) = g32p_row31_cosetRepresentatives 8520 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8520 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8520) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8520))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8520)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8520 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8520) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8520))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8520)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8521 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8521) = g32p_row31_cosetRepresentatives 8521 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8521 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8521) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8521))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8521)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8521 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8521) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8521))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8521)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8522 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8522) = g32p_row31_cosetRepresentatives 8522 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8522 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8522) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8522))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8522)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8522 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8522) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8522))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8522)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8523 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8523) = g32p_row31_cosetRepresentatives 8523 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8523 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8523) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8523))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8523)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8523 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8523) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8523))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8523)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8524 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8524) = g32p_row31_cosetRepresentatives 8524 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8524 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8524) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8524))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8524)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8524 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8524) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8524))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8524)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8525 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8525) = g32p_row31_cosetRepresentatives 8525 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8525 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8525) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8525))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8525)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8525 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8525) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8525))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8525)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8526 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8526) = g32p_row31_cosetRepresentatives 8526 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8526 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8526) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8526))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8526)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8526 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8526) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8526))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8526)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8527 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8527) = g32p_row31_cosetRepresentatives 8527 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8527 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8527) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8527))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8527)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8527 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8527) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8527))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8527)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0532 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 532 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 532 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8512
  · exact g32p_row31_cosetWord_8513
  · exact g32p_row31_cosetWord_8514
  · exact g32p_row31_cosetWord_8515
  · exact g32p_row31_cosetWord_8516
  · exact g32p_row31_cosetWord_8517
  · exact g32p_row31_cosetWord_8518
  · exact g32p_row31_cosetWord_8519
  · exact g32p_row31_cosetWord_8520
  · exact g32p_row31_cosetWord_8521
  · exact g32p_row31_cosetWord_8522
  · exact g32p_row31_cosetWord_8523
  · exact g32p_row31_cosetWord_8524
  · exact g32p_row31_cosetWord_8525
  · exact g32p_row31_cosetWord_8526
  · exact g32p_row31_cosetWord_8527

theorem g32p_row31_cosetGeneratorBlock_0532 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 532 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 532 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 532 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8512 s
  · exact g32p_row31_cosetGeneratorStep_8513 s
  · exact g32p_row31_cosetGeneratorStep_8514 s
  · exact g32p_row31_cosetGeneratorStep_8515 s
  · exact g32p_row31_cosetGeneratorStep_8516 s
  · exact g32p_row31_cosetGeneratorStep_8517 s
  · exact g32p_row31_cosetGeneratorStep_8518 s
  · exact g32p_row31_cosetGeneratorStep_8519 s
  · exact g32p_row31_cosetGeneratorStep_8520 s
  · exact g32p_row31_cosetGeneratorStep_8521 s
  · exact g32p_row31_cosetGeneratorStep_8522 s
  · exact g32p_row31_cosetGeneratorStep_8523 s
  · exact g32p_row31_cosetGeneratorStep_8524 s
  · exact g32p_row31_cosetGeneratorStep_8525 s
  · exact g32p_row31_cosetGeneratorStep_8526 s
  · exact g32p_row31_cosetGeneratorStep_8527 s

theorem g32p_row31_cosetBranchBlock_0532 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 532 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 532 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 532 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8512 s
  · exact g32p_row31_cosetBranchStep_8513 s
  · exact g32p_row31_cosetBranchStep_8514 s
  · exact g32p_row31_cosetBranchStep_8515 s
  · exact g32p_row31_cosetBranchStep_8516 s
  · exact g32p_row31_cosetBranchStep_8517 s
  · exact g32p_row31_cosetBranchStep_8518 s
  · exact g32p_row31_cosetBranchStep_8519 s
  · exact g32p_row31_cosetBranchStep_8520 s
  · exact g32p_row31_cosetBranchStep_8521 s
  · exact g32p_row31_cosetBranchStep_8522 s
  · exact g32p_row31_cosetBranchStep_8523 s
  · exact g32p_row31_cosetBranchStep_8524 s
  · exact g32p_row31_cosetBranchStep_8525 s
  · exact g32p_row31_cosetBranchStep_8526 s
  · exact g32p_row31_cosetBranchStep_8527 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8528 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8528) = g32p_row31_cosetRepresentatives 8528 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8528 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8528) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8528))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8528)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8528 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8528) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8528))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8528)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8529 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8529) = g32p_row31_cosetRepresentatives 8529 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8529 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8529) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8529))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8529)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8529 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8529) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8529))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8529)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8530 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8530) = g32p_row31_cosetRepresentatives 8530 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8530 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8530) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8530))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8530)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8530 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8530) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8530))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8530)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8531 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8531) = g32p_row31_cosetRepresentatives 8531 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8531 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8531) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8531))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8531)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8531 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8531) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8531))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8531)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8532 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8532) = g32p_row31_cosetRepresentatives 8532 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8532 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8532) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8532))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8532)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8532 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8532) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8532))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8532)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8533 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8533) = g32p_row31_cosetRepresentatives 8533 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8533 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8533) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8533))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8533)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8533 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8533) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8533))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8533)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8534 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8534) = g32p_row31_cosetRepresentatives 8534 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8534 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8534) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8534))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8534)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8534 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8534) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8534))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8534)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8535 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8535) = g32p_row31_cosetRepresentatives 8535 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8535 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8535) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8535))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8535)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8535 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8535) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8535))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8535)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8536 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8536) = g32p_row31_cosetRepresentatives 8536 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8536 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8536) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8536))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8536)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8536 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8536) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8536))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8536)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8537 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8537) = g32p_row31_cosetRepresentatives 8537 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8537 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8537) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8537))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8537)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8537 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8537) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8537))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8537)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8538 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8538) = g32p_row31_cosetRepresentatives 8538 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8538 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8538) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8538))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8538)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8538 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8538) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8538))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8538)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8539 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8539) = g32p_row31_cosetRepresentatives 8539 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8539 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8539) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8539))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8539)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8539 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8539) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8539))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8539)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8540 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8540) = g32p_row31_cosetRepresentatives 8540 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8540 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8540) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8540))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8540)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8540 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8540) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8540))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8540)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8541 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8541) = g32p_row31_cosetRepresentatives 8541 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8541 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8541) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8541))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8541)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8541 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8541) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8541))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8541)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8542 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8542) = g32p_row31_cosetRepresentatives 8542 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8542 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8542) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8542))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8542)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8542 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8542) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8542))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8542)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8543 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8543) = g32p_row31_cosetRepresentatives 8543 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8543 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8543) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8543))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8543)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8543 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8543) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8543))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8543)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0533 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 533 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 533 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8528
  · exact g32p_row31_cosetWord_8529
  · exact g32p_row31_cosetWord_8530
  · exact g32p_row31_cosetWord_8531
  · exact g32p_row31_cosetWord_8532
  · exact g32p_row31_cosetWord_8533
  · exact g32p_row31_cosetWord_8534
  · exact g32p_row31_cosetWord_8535
  · exact g32p_row31_cosetWord_8536
  · exact g32p_row31_cosetWord_8537
  · exact g32p_row31_cosetWord_8538
  · exact g32p_row31_cosetWord_8539
  · exact g32p_row31_cosetWord_8540
  · exact g32p_row31_cosetWord_8541
  · exact g32p_row31_cosetWord_8542
  · exact g32p_row31_cosetWord_8543

theorem g32p_row31_cosetGeneratorBlock_0533 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 533 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 533 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 533 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8528 s
  · exact g32p_row31_cosetGeneratorStep_8529 s
  · exact g32p_row31_cosetGeneratorStep_8530 s
  · exact g32p_row31_cosetGeneratorStep_8531 s
  · exact g32p_row31_cosetGeneratorStep_8532 s
  · exact g32p_row31_cosetGeneratorStep_8533 s
  · exact g32p_row31_cosetGeneratorStep_8534 s
  · exact g32p_row31_cosetGeneratorStep_8535 s
  · exact g32p_row31_cosetGeneratorStep_8536 s
  · exact g32p_row31_cosetGeneratorStep_8537 s
  · exact g32p_row31_cosetGeneratorStep_8538 s
  · exact g32p_row31_cosetGeneratorStep_8539 s
  · exact g32p_row31_cosetGeneratorStep_8540 s
  · exact g32p_row31_cosetGeneratorStep_8541 s
  · exact g32p_row31_cosetGeneratorStep_8542 s
  · exact g32p_row31_cosetGeneratorStep_8543 s

theorem g32p_row31_cosetBranchBlock_0533 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 533 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 533 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 533 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8528 s
  · exact g32p_row31_cosetBranchStep_8529 s
  · exact g32p_row31_cosetBranchStep_8530 s
  · exact g32p_row31_cosetBranchStep_8531 s
  · exact g32p_row31_cosetBranchStep_8532 s
  · exact g32p_row31_cosetBranchStep_8533 s
  · exact g32p_row31_cosetBranchStep_8534 s
  · exact g32p_row31_cosetBranchStep_8535 s
  · exact g32p_row31_cosetBranchStep_8536 s
  · exact g32p_row31_cosetBranchStep_8537 s
  · exact g32p_row31_cosetBranchStep_8538 s
  · exact g32p_row31_cosetBranchStep_8539 s
  · exact g32p_row31_cosetBranchStep_8540 s
  · exact g32p_row31_cosetBranchStep_8541 s
  · exact g32p_row31_cosetBranchStep_8542 s
  · exact g32p_row31_cosetBranchStep_8543 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8544 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8544) = g32p_row31_cosetRepresentatives 8544 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8544 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8544) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8544))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8544)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8544 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8544) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8544))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8544)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8545 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8545) = g32p_row31_cosetRepresentatives 8545 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8545 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8545) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8545))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8545)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8545 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8545) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8545))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8545)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8546 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8546) = g32p_row31_cosetRepresentatives 8546 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8546 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8546) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8546))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8546)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8546 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8546) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8546))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8546)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8547 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8547) = g32p_row31_cosetRepresentatives 8547 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8547 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8547) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8547))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8547)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8547 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8547) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8547))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8547)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8548 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8548) = g32p_row31_cosetRepresentatives 8548 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8548 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8548) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8548))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8548)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8548 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8548) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8548))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8548)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8549 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8549) = g32p_row31_cosetRepresentatives 8549 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8549 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8549) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8549))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8549)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8549 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8549) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8549))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8549)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8550 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8550) = g32p_row31_cosetRepresentatives 8550 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8550 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8550) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8550))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8550)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8550 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8550) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8550))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8550)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8551 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8551) = g32p_row31_cosetRepresentatives 8551 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8551 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8551) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8551))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8551)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8551 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8551) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8551))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8551)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8552 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8552) = g32p_row31_cosetRepresentatives 8552 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8552 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8552) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8552))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8552)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8552 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8552) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8552))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8552)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8553 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8553) = g32p_row31_cosetRepresentatives 8553 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8553 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8553) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8553))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8553)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8553 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8553) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8553))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8553)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8554 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8554) = g32p_row31_cosetRepresentatives 8554 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8554 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8554) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8554))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8554)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8554 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8554) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8554))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8554)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8555 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8555) = g32p_row31_cosetRepresentatives 8555 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8555 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8555) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8555))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8555)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8555 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8555) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8555))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8555)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8556 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8556) = g32p_row31_cosetRepresentatives 8556 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8556 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8556) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8556))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8556)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8556 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8556) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8556))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8556)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8557 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8557) = g32p_row31_cosetRepresentatives 8557 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8557 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8557) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8557))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8557)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8557 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8557) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8557))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8557)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8558 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8558) = g32p_row31_cosetRepresentatives 8558 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8558 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8558) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8558))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8558)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8558 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8558) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8558))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8558)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8559 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8559) = g32p_row31_cosetRepresentatives 8559 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8559 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8559) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8559))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8559)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8559 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8559) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8559))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8559)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0534 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 534 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 534 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8544
  · exact g32p_row31_cosetWord_8545
  · exact g32p_row31_cosetWord_8546
  · exact g32p_row31_cosetWord_8547
  · exact g32p_row31_cosetWord_8548
  · exact g32p_row31_cosetWord_8549
  · exact g32p_row31_cosetWord_8550
  · exact g32p_row31_cosetWord_8551
  · exact g32p_row31_cosetWord_8552
  · exact g32p_row31_cosetWord_8553
  · exact g32p_row31_cosetWord_8554
  · exact g32p_row31_cosetWord_8555
  · exact g32p_row31_cosetWord_8556
  · exact g32p_row31_cosetWord_8557
  · exact g32p_row31_cosetWord_8558
  · exact g32p_row31_cosetWord_8559

theorem g32p_row31_cosetGeneratorBlock_0534 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 534 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 534 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 534 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8544 s
  · exact g32p_row31_cosetGeneratorStep_8545 s
  · exact g32p_row31_cosetGeneratorStep_8546 s
  · exact g32p_row31_cosetGeneratorStep_8547 s
  · exact g32p_row31_cosetGeneratorStep_8548 s
  · exact g32p_row31_cosetGeneratorStep_8549 s
  · exact g32p_row31_cosetGeneratorStep_8550 s
  · exact g32p_row31_cosetGeneratorStep_8551 s
  · exact g32p_row31_cosetGeneratorStep_8552 s
  · exact g32p_row31_cosetGeneratorStep_8553 s
  · exact g32p_row31_cosetGeneratorStep_8554 s
  · exact g32p_row31_cosetGeneratorStep_8555 s
  · exact g32p_row31_cosetGeneratorStep_8556 s
  · exact g32p_row31_cosetGeneratorStep_8557 s
  · exact g32p_row31_cosetGeneratorStep_8558 s
  · exact g32p_row31_cosetGeneratorStep_8559 s

theorem g32p_row31_cosetBranchBlock_0534 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 534 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 534 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 534 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8544 s
  · exact g32p_row31_cosetBranchStep_8545 s
  · exact g32p_row31_cosetBranchStep_8546 s
  · exact g32p_row31_cosetBranchStep_8547 s
  · exact g32p_row31_cosetBranchStep_8548 s
  · exact g32p_row31_cosetBranchStep_8549 s
  · exact g32p_row31_cosetBranchStep_8550 s
  · exact g32p_row31_cosetBranchStep_8551 s
  · exact g32p_row31_cosetBranchStep_8552 s
  · exact g32p_row31_cosetBranchStep_8553 s
  · exact g32p_row31_cosetBranchStep_8554 s
  · exact g32p_row31_cosetBranchStep_8555 s
  · exact g32p_row31_cosetBranchStep_8556 s
  · exact g32p_row31_cosetBranchStep_8557 s
  · exact g32p_row31_cosetBranchStep_8558 s
  · exact g32p_row31_cosetBranchStep_8559 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8560 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8560) = g32p_row31_cosetRepresentatives 8560 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8560 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8560) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8560))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8560)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8560 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8560) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8560))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8560)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8561 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8561) = g32p_row31_cosetRepresentatives 8561 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8561 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8561) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8561))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8561)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8561 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8561) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8561))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8561)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8562 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8562) = g32p_row31_cosetRepresentatives 8562 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8562 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8562) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8562))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8562)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8562 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8562) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8562))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8562)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8563 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8563) = g32p_row31_cosetRepresentatives 8563 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8563 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8563) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8563))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8563)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8563 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8563) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8563))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8563)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8564 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8564) = g32p_row31_cosetRepresentatives 8564 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8564 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8564) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8564))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8564)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8564 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8564) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8564))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8564)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8565 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8565) = g32p_row31_cosetRepresentatives 8565 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8565 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8565) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8565))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8565)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8565 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8565) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8565))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8565)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8566 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8566) = g32p_row31_cosetRepresentatives 8566 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8566 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8566) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8566))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8566)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8566 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8566) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8566))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8566)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8567 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8567) = g32p_row31_cosetRepresentatives 8567 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8567 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8567) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8567))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8567)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8567 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8567) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8567))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8567)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8568 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8568) = g32p_row31_cosetRepresentatives 8568 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8568 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8568) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8568))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8568)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8568 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8568) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8568))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8568)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8569 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8569) = g32p_row31_cosetRepresentatives 8569 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8569 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8569) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8569))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8569)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8569 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8569) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8569))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8569)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8570 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8570) = g32p_row31_cosetRepresentatives 8570 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8570 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8570) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8570))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8570)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8570 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8570) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8570))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8570)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8571 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8571) = g32p_row31_cosetRepresentatives 8571 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8571 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8571) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8571))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8571)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8571 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8571) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8571))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8571)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8572 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8572) = g32p_row31_cosetRepresentatives 8572 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8572 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8572) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8572))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8572)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8572 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8572) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8572))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8572)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8573 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8573) = g32p_row31_cosetRepresentatives 8573 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8573 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8573) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8573))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8573)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8573 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8573) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8573))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8573)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8574 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8574) = g32p_row31_cosetRepresentatives 8574 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8574 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8574) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8574))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8574)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8574 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8574) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8574))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8574)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8575 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8575) = g32p_row31_cosetRepresentatives 8575 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8575 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8575) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8575))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8575)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8575 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8575) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8575))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8575)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0535 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 535 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 535 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8560
  · exact g32p_row31_cosetWord_8561
  · exact g32p_row31_cosetWord_8562
  · exact g32p_row31_cosetWord_8563
  · exact g32p_row31_cosetWord_8564
  · exact g32p_row31_cosetWord_8565
  · exact g32p_row31_cosetWord_8566
  · exact g32p_row31_cosetWord_8567
  · exact g32p_row31_cosetWord_8568
  · exact g32p_row31_cosetWord_8569
  · exact g32p_row31_cosetWord_8570
  · exact g32p_row31_cosetWord_8571
  · exact g32p_row31_cosetWord_8572
  · exact g32p_row31_cosetWord_8573
  · exact g32p_row31_cosetWord_8574
  · exact g32p_row31_cosetWord_8575

theorem g32p_row31_cosetGeneratorBlock_0535 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 535 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 535 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 535 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8560 s
  · exact g32p_row31_cosetGeneratorStep_8561 s
  · exact g32p_row31_cosetGeneratorStep_8562 s
  · exact g32p_row31_cosetGeneratorStep_8563 s
  · exact g32p_row31_cosetGeneratorStep_8564 s
  · exact g32p_row31_cosetGeneratorStep_8565 s
  · exact g32p_row31_cosetGeneratorStep_8566 s
  · exact g32p_row31_cosetGeneratorStep_8567 s
  · exact g32p_row31_cosetGeneratorStep_8568 s
  · exact g32p_row31_cosetGeneratorStep_8569 s
  · exact g32p_row31_cosetGeneratorStep_8570 s
  · exact g32p_row31_cosetGeneratorStep_8571 s
  · exact g32p_row31_cosetGeneratorStep_8572 s
  · exact g32p_row31_cosetGeneratorStep_8573 s
  · exact g32p_row31_cosetGeneratorStep_8574 s
  · exact g32p_row31_cosetGeneratorStep_8575 s

theorem g32p_row31_cosetBranchBlock_0535 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 535 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 535 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 535 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8560 s
  · exact g32p_row31_cosetBranchStep_8561 s
  · exact g32p_row31_cosetBranchStep_8562 s
  · exact g32p_row31_cosetBranchStep_8563 s
  · exact g32p_row31_cosetBranchStep_8564 s
  · exact g32p_row31_cosetBranchStep_8565 s
  · exact g32p_row31_cosetBranchStep_8566 s
  · exact g32p_row31_cosetBranchStep_8567 s
  · exact g32p_row31_cosetBranchStep_8568 s
  · exact g32p_row31_cosetBranchStep_8569 s
  · exact g32p_row31_cosetBranchStep_8570 s
  · exact g32p_row31_cosetBranchStep_8571 s
  · exact g32p_row31_cosetBranchStep_8572 s
  · exact g32p_row31_cosetBranchStep_8573 s
  · exact g32p_row31_cosetBranchStep_8574 s
  · exact g32p_row31_cosetBranchStep_8575 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8576 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8576) = g32p_row31_cosetRepresentatives 8576 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8576 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8576) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8576))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8576)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8576 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8576) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8576))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8576)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8577 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8577) = g32p_row31_cosetRepresentatives 8577 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8577 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8577) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8577))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8577)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8577 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8577) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8577))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8577)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8578 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8578) = g32p_row31_cosetRepresentatives 8578 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8578 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8578) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8578))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8578)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8578 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8578) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8578))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8578)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8579 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8579) = g32p_row31_cosetRepresentatives 8579 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8579 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8579) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8579))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8579)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8579 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8579) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8579))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8579)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8580 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8580) = g32p_row31_cosetRepresentatives 8580 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8580 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8580) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8580))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8580)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8580 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8580) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8580))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8580)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8581 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8581) = g32p_row31_cosetRepresentatives 8581 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8581 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8581) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8581))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8581)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8581 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8581) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8581))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8581)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8582 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8582) = g32p_row31_cosetRepresentatives 8582 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8582 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8582) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8582))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8582)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8582 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8582) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8582))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8582)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8583 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8583) = g32p_row31_cosetRepresentatives 8583 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8583 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8583) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8583))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8583)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8583 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8583) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8583))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8583)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8584 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8584) = g32p_row31_cosetRepresentatives 8584 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8584 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8584) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8584))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8584)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8584 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8584) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8584))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8584)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8585 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8585) = g32p_row31_cosetRepresentatives 8585 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8585 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8585) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8585))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8585)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8585 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8585) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8585))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8585)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8586 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8586) = g32p_row31_cosetRepresentatives 8586 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8586 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8586) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8586))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8586)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8586 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8586) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8586))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8586)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8587 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8587) = g32p_row31_cosetRepresentatives 8587 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8587 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8587) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8587))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8587)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8587 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8587) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8587))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8587)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8588 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8588) = g32p_row31_cosetRepresentatives 8588 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8588 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8588) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8588))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8588)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8588 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8588) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8588))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8588)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8589 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8589) = g32p_row31_cosetRepresentatives 8589 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8589 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8589) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8589))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8589)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8589 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8589) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8589))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8589)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8590 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8590) = g32p_row31_cosetRepresentatives 8590 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8590 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8590) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8590))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8590)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8590 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8590) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8590))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8590)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8591 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8591) = g32p_row31_cosetRepresentatives 8591 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8591 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8591) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8591))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8591)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8591 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8591) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8591))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8591)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0536 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 536 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 536 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8576
  · exact g32p_row31_cosetWord_8577
  · exact g32p_row31_cosetWord_8578
  · exact g32p_row31_cosetWord_8579
  · exact g32p_row31_cosetWord_8580
  · exact g32p_row31_cosetWord_8581
  · exact g32p_row31_cosetWord_8582
  · exact g32p_row31_cosetWord_8583
  · exact g32p_row31_cosetWord_8584
  · exact g32p_row31_cosetWord_8585
  · exact g32p_row31_cosetWord_8586
  · exact g32p_row31_cosetWord_8587
  · exact g32p_row31_cosetWord_8588
  · exact g32p_row31_cosetWord_8589
  · exact g32p_row31_cosetWord_8590
  · exact g32p_row31_cosetWord_8591

theorem g32p_row31_cosetGeneratorBlock_0536 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 536 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 536 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 536 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8576 s
  · exact g32p_row31_cosetGeneratorStep_8577 s
  · exact g32p_row31_cosetGeneratorStep_8578 s
  · exact g32p_row31_cosetGeneratorStep_8579 s
  · exact g32p_row31_cosetGeneratorStep_8580 s
  · exact g32p_row31_cosetGeneratorStep_8581 s
  · exact g32p_row31_cosetGeneratorStep_8582 s
  · exact g32p_row31_cosetGeneratorStep_8583 s
  · exact g32p_row31_cosetGeneratorStep_8584 s
  · exact g32p_row31_cosetGeneratorStep_8585 s
  · exact g32p_row31_cosetGeneratorStep_8586 s
  · exact g32p_row31_cosetGeneratorStep_8587 s
  · exact g32p_row31_cosetGeneratorStep_8588 s
  · exact g32p_row31_cosetGeneratorStep_8589 s
  · exact g32p_row31_cosetGeneratorStep_8590 s
  · exact g32p_row31_cosetGeneratorStep_8591 s

theorem g32p_row31_cosetBranchBlock_0536 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 536 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 536 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 536 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8576 s
  · exact g32p_row31_cosetBranchStep_8577 s
  · exact g32p_row31_cosetBranchStep_8578 s
  · exact g32p_row31_cosetBranchStep_8579 s
  · exact g32p_row31_cosetBranchStep_8580 s
  · exact g32p_row31_cosetBranchStep_8581 s
  · exact g32p_row31_cosetBranchStep_8582 s
  · exact g32p_row31_cosetBranchStep_8583 s
  · exact g32p_row31_cosetBranchStep_8584 s
  · exact g32p_row31_cosetBranchStep_8585 s
  · exact g32p_row31_cosetBranchStep_8586 s
  · exact g32p_row31_cosetBranchStep_8587 s
  · exact g32p_row31_cosetBranchStep_8588 s
  · exact g32p_row31_cosetBranchStep_8589 s
  · exact g32p_row31_cosetBranchStep_8590 s
  · exact g32p_row31_cosetBranchStep_8591 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8592 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8592) = g32p_row31_cosetRepresentatives 8592 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8592 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8592) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8592))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8592)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8592 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8592) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8592))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8592)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8593 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8593) = g32p_row31_cosetRepresentatives 8593 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8593 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8593) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8593))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8593)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8593 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8593) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8593))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8593)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8594 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8594) = g32p_row31_cosetRepresentatives 8594 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8594 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8594) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8594))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8594)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8594 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8594) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8594))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8594)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8595 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8595) = g32p_row31_cosetRepresentatives 8595 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8595 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8595) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8595))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8595)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8595 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8595) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8595))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8595)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8596 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8596) = g32p_row31_cosetRepresentatives 8596 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8596 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8596) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8596))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8596)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8596 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8596) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8596))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8596)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8597 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8597) = g32p_row31_cosetRepresentatives 8597 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8597 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8597) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8597))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8597)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8597 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8597) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8597))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8597)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8598 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8598) = g32p_row31_cosetRepresentatives 8598 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8598 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8598) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8598))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8598)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8598 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8598) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8598))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8598)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8599 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8599) = g32p_row31_cosetRepresentatives 8599 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8599 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8599) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8599))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8599)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8599 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8599) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8599))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8599)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8600 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8600) = g32p_row31_cosetRepresentatives 8600 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8600 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8600) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8600))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8600)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8600 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8600) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8600))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8600)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8601 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8601) = g32p_row31_cosetRepresentatives 8601 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8601 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8601) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8601))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8601)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8601 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8601) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8601))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8601)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8602 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8602) = g32p_row31_cosetRepresentatives 8602 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8602 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8602) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8602))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8602)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8602 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8602) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8602))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8602)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8603 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8603) = g32p_row31_cosetRepresentatives 8603 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8603 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8603) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8603))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8603)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8603 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8603) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8603))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8603)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8604 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8604) = g32p_row31_cosetRepresentatives 8604 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8604 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8604) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8604))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8604)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8604 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8604) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8604))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8604)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8605 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8605) = g32p_row31_cosetRepresentatives 8605 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8605 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8605) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8605))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8605)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8605 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8605) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8605))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8605)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8606 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8606) = g32p_row31_cosetRepresentatives 8606 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8606 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8606) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8606))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8606)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8606 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8606) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8606))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8606)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8607 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8607) = g32p_row31_cosetRepresentatives 8607 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8607 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8607) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8607))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8607)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8607 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8607) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8607))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8607)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0537 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 537 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 537 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8592
  · exact g32p_row31_cosetWord_8593
  · exact g32p_row31_cosetWord_8594
  · exact g32p_row31_cosetWord_8595
  · exact g32p_row31_cosetWord_8596
  · exact g32p_row31_cosetWord_8597
  · exact g32p_row31_cosetWord_8598
  · exact g32p_row31_cosetWord_8599
  · exact g32p_row31_cosetWord_8600
  · exact g32p_row31_cosetWord_8601
  · exact g32p_row31_cosetWord_8602
  · exact g32p_row31_cosetWord_8603
  · exact g32p_row31_cosetWord_8604
  · exact g32p_row31_cosetWord_8605
  · exact g32p_row31_cosetWord_8606
  · exact g32p_row31_cosetWord_8607

theorem g32p_row31_cosetGeneratorBlock_0537 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 537 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 537 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 537 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8592 s
  · exact g32p_row31_cosetGeneratorStep_8593 s
  · exact g32p_row31_cosetGeneratorStep_8594 s
  · exact g32p_row31_cosetGeneratorStep_8595 s
  · exact g32p_row31_cosetGeneratorStep_8596 s
  · exact g32p_row31_cosetGeneratorStep_8597 s
  · exact g32p_row31_cosetGeneratorStep_8598 s
  · exact g32p_row31_cosetGeneratorStep_8599 s
  · exact g32p_row31_cosetGeneratorStep_8600 s
  · exact g32p_row31_cosetGeneratorStep_8601 s
  · exact g32p_row31_cosetGeneratorStep_8602 s
  · exact g32p_row31_cosetGeneratorStep_8603 s
  · exact g32p_row31_cosetGeneratorStep_8604 s
  · exact g32p_row31_cosetGeneratorStep_8605 s
  · exact g32p_row31_cosetGeneratorStep_8606 s
  · exact g32p_row31_cosetGeneratorStep_8607 s

theorem g32p_row31_cosetBranchBlock_0537 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 537 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 537 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 537 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8592 s
  · exact g32p_row31_cosetBranchStep_8593 s
  · exact g32p_row31_cosetBranchStep_8594 s
  · exact g32p_row31_cosetBranchStep_8595 s
  · exact g32p_row31_cosetBranchStep_8596 s
  · exact g32p_row31_cosetBranchStep_8597 s
  · exact g32p_row31_cosetBranchStep_8598 s
  · exact g32p_row31_cosetBranchStep_8599 s
  · exact g32p_row31_cosetBranchStep_8600 s
  · exact g32p_row31_cosetBranchStep_8601 s
  · exact g32p_row31_cosetBranchStep_8602 s
  · exact g32p_row31_cosetBranchStep_8603 s
  · exact g32p_row31_cosetBranchStep_8604 s
  · exact g32p_row31_cosetBranchStep_8605 s
  · exact g32p_row31_cosetBranchStep_8606 s
  · exact g32p_row31_cosetBranchStep_8607 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8608 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8608) = g32p_row31_cosetRepresentatives 8608 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8608 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8608) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8608))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8608)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8608 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8608) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8608))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8608)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8609 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8609) = g32p_row31_cosetRepresentatives 8609 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8609 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8609) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8609))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8609)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8609 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8609) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8609))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8609)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8610 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8610) = g32p_row31_cosetRepresentatives 8610 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8610 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8610) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8610))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8610)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8610 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8610) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8610))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8610)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8611 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8611) = g32p_row31_cosetRepresentatives 8611 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8611 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8611) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8611))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8611)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8611 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8611) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8611))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8611)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8612 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8612) = g32p_row31_cosetRepresentatives 8612 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8612 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8612) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8612))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8612)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8612 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8612) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8612))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8612)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8613 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8613) = g32p_row31_cosetRepresentatives 8613 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8613 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8613) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8613))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8613)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8613 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8613) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8613))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8613)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8614 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8614) = g32p_row31_cosetRepresentatives 8614 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8614 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8614) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8614))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8614)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8614 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8614) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8614))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8614)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8615 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8615) = g32p_row31_cosetRepresentatives 8615 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8615 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8615) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8615))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8615)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8615 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8615) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8615))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8615)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8616 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8616) = g32p_row31_cosetRepresentatives 8616 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8616 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8616) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8616))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8616)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8616 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8616) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8616))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8616)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8617 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8617) = g32p_row31_cosetRepresentatives 8617 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8617 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8617) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8617))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8617)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8617 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8617) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8617))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8617)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8618 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8618) = g32p_row31_cosetRepresentatives 8618 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8618 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8618) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8618))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8618)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8618 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8618) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8618))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8618)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8619 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8619) = g32p_row31_cosetRepresentatives 8619 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8619 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8619) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8619))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8619)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8619 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8619) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8619))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8619)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8620 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8620) = g32p_row31_cosetRepresentatives 8620 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8620 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8620) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8620))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8620)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8620 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8620) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8620))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8620)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8621 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8621) = g32p_row31_cosetRepresentatives 8621 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8621 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8621) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8621))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8621)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8621 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8621) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8621))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8621)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8622 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8622) = g32p_row31_cosetRepresentatives 8622 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8622 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8622) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8622))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8622)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8622 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8622) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8622))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8622)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8623 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8623) = g32p_row31_cosetRepresentatives 8623 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8623 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8623) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8623))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8623)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8623 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8623) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8623))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8623)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0538 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 538 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 538 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8608
  · exact g32p_row31_cosetWord_8609
  · exact g32p_row31_cosetWord_8610
  · exact g32p_row31_cosetWord_8611
  · exact g32p_row31_cosetWord_8612
  · exact g32p_row31_cosetWord_8613
  · exact g32p_row31_cosetWord_8614
  · exact g32p_row31_cosetWord_8615
  · exact g32p_row31_cosetWord_8616
  · exact g32p_row31_cosetWord_8617
  · exact g32p_row31_cosetWord_8618
  · exact g32p_row31_cosetWord_8619
  · exact g32p_row31_cosetWord_8620
  · exact g32p_row31_cosetWord_8621
  · exact g32p_row31_cosetWord_8622
  · exact g32p_row31_cosetWord_8623

theorem g32p_row31_cosetGeneratorBlock_0538 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 538 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 538 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 538 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8608 s
  · exact g32p_row31_cosetGeneratorStep_8609 s
  · exact g32p_row31_cosetGeneratorStep_8610 s
  · exact g32p_row31_cosetGeneratorStep_8611 s
  · exact g32p_row31_cosetGeneratorStep_8612 s
  · exact g32p_row31_cosetGeneratorStep_8613 s
  · exact g32p_row31_cosetGeneratorStep_8614 s
  · exact g32p_row31_cosetGeneratorStep_8615 s
  · exact g32p_row31_cosetGeneratorStep_8616 s
  · exact g32p_row31_cosetGeneratorStep_8617 s
  · exact g32p_row31_cosetGeneratorStep_8618 s
  · exact g32p_row31_cosetGeneratorStep_8619 s
  · exact g32p_row31_cosetGeneratorStep_8620 s
  · exact g32p_row31_cosetGeneratorStep_8621 s
  · exact g32p_row31_cosetGeneratorStep_8622 s
  · exact g32p_row31_cosetGeneratorStep_8623 s

theorem g32p_row31_cosetBranchBlock_0538 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 538 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 538 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 538 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8608 s
  · exact g32p_row31_cosetBranchStep_8609 s
  · exact g32p_row31_cosetBranchStep_8610 s
  · exact g32p_row31_cosetBranchStep_8611 s
  · exact g32p_row31_cosetBranchStep_8612 s
  · exact g32p_row31_cosetBranchStep_8613 s
  · exact g32p_row31_cosetBranchStep_8614 s
  · exact g32p_row31_cosetBranchStep_8615 s
  · exact g32p_row31_cosetBranchStep_8616 s
  · exact g32p_row31_cosetBranchStep_8617 s
  · exact g32p_row31_cosetBranchStep_8618 s
  · exact g32p_row31_cosetBranchStep_8619 s
  · exact g32p_row31_cosetBranchStep_8620 s
  · exact g32p_row31_cosetBranchStep_8621 s
  · exact g32p_row31_cosetBranchStep_8622 s
  · exact g32p_row31_cosetBranchStep_8623 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8624 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8624) = g32p_row31_cosetRepresentatives 8624 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8624 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8624) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8624))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8624)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8624 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8624) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8624))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8624)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8625 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8625) = g32p_row31_cosetRepresentatives 8625 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8625 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8625) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8625))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8625)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8625 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8625) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8625))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8625)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8626 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8626) = g32p_row31_cosetRepresentatives 8626 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8626 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8626) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8626))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8626)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8626 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8626) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8626))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8626)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8627 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8627) = g32p_row31_cosetRepresentatives 8627 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8627 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8627) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8627))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8627)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8627 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8627) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8627))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8627)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8628 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8628) = g32p_row31_cosetRepresentatives 8628 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8628 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8628) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8628))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8628)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8628 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8628) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8628))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8628)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8629 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8629) = g32p_row31_cosetRepresentatives 8629 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8629 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8629) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8629))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8629)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8629 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8629) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8629))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8629)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8630 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8630) = g32p_row31_cosetRepresentatives 8630 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8630 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8630) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8630))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8630)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8630 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8630) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8630))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8630)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8631 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8631) = g32p_row31_cosetRepresentatives 8631 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8631 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8631) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8631))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8631)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8631 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8631) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8631))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8631)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8632 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8632) = g32p_row31_cosetRepresentatives 8632 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8632 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8632) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8632))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8632)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8632 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8632) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8632))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8632)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8633 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8633) = g32p_row31_cosetRepresentatives 8633 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8633 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8633) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8633))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8633)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8633 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8633) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8633))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8633)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8634 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8634) = g32p_row31_cosetRepresentatives 8634 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8634 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8634) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8634))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8634)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8634 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8634) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8634))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8634)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8635 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8635) = g32p_row31_cosetRepresentatives 8635 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8635 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8635) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8635))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8635)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8635 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8635) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8635))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8635)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8636 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8636) = g32p_row31_cosetRepresentatives 8636 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8636 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8636) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8636))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8636)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8636 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8636) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8636))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8636)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8637 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8637) = g32p_row31_cosetRepresentatives 8637 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8637 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8637) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8637))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8637)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8637 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8637) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8637))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8637)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8638 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8638) = g32p_row31_cosetRepresentatives 8638 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8638 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8638) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8638))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8638)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8638 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8638) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8638))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8638)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8639 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8639) = g32p_row31_cosetRepresentatives 8639 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8639 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8639) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8639))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8639)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8639 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8639) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8639))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8639)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0539 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 539 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 539 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8624
  · exact g32p_row31_cosetWord_8625
  · exact g32p_row31_cosetWord_8626
  · exact g32p_row31_cosetWord_8627
  · exact g32p_row31_cosetWord_8628
  · exact g32p_row31_cosetWord_8629
  · exact g32p_row31_cosetWord_8630
  · exact g32p_row31_cosetWord_8631
  · exact g32p_row31_cosetWord_8632
  · exact g32p_row31_cosetWord_8633
  · exact g32p_row31_cosetWord_8634
  · exact g32p_row31_cosetWord_8635
  · exact g32p_row31_cosetWord_8636
  · exact g32p_row31_cosetWord_8637
  · exact g32p_row31_cosetWord_8638
  · exact g32p_row31_cosetWord_8639

theorem g32p_row31_cosetGeneratorBlock_0539 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 539 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 539 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 539 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8624 s
  · exact g32p_row31_cosetGeneratorStep_8625 s
  · exact g32p_row31_cosetGeneratorStep_8626 s
  · exact g32p_row31_cosetGeneratorStep_8627 s
  · exact g32p_row31_cosetGeneratorStep_8628 s
  · exact g32p_row31_cosetGeneratorStep_8629 s
  · exact g32p_row31_cosetGeneratorStep_8630 s
  · exact g32p_row31_cosetGeneratorStep_8631 s
  · exact g32p_row31_cosetGeneratorStep_8632 s
  · exact g32p_row31_cosetGeneratorStep_8633 s
  · exact g32p_row31_cosetGeneratorStep_8634 s
  · exact g32p_row31_cosetGeneratorStep_8635 s
  · exact g32p_row31_cosetGeneratorStep_8636 s
  · exact g32p_row31_cosetGeneratorStep_8637 s
  · exact g32p_row31_cosetGeneratorStep_8638 s
  · exact g32p_row31_cosetGeneratorStep_8639 s

theorem g32p_row31_cosetBranchBlock_0539 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 539 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 539 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 539 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8624 s
  · exact g32p_row31_cosetBranchStep_8625 s
  · exact g32p_row31_cosetBranchStep_8626 s
  · exact g32p_row31_cosetBranchStep_8627 s
  · exact g32p_row31_cosetBranchStep_8628 s
  · exact g32p_row31_cosetBranchStep_8629 s
  · exact g32p_row31_cosetBranchStep_8630 s
  · exact g32p_row31_cosetBranchStep_8631 s
  · exact g32p_row31_cosetBranchStep_8632 s
  · exact g32p_row31_cosetBranchStep_8633 s
  · exact g32p_row31_cosetBranchStep_8634 s
  · exact g32p_row31_cosetBranchStep_8635 s
  · exact g32p_row31_cosetBranchStep_8636 s
  · exact g32p_row31_cosetBranchStep_8637 s
  · exact g32p_row31_cosetBranchStep_8638 s
  · exact g32p_row31_cosetBranchStep_8639 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

theorem g32p_row31_cosetWord (i : Fin 8640) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords i) = g32p_row31_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row31_cosetWordBlock_0000
  · exact g32p_row31_cosetWordBlock_0001
  · exact g32p_row31_cosetWordBlock_0002
  · exact g32p_row31_cosetWordBlock_0003
  · exact g32p_row31_cosetWordBlock_0004
  · exact g32p_row31_cosetWordBlock_0005
  · exact g32p_row31_cosetWordBlock_0006
  · exact g32p_row31_cosetWordBlock_0007
  · exact g32p_row31_cosetWordBlock_0008
  · exact g32p_row31_cosetWordBlock_0009
  · exact g32p_row31_cosetWordBlock_0010
  · exact g32p_row31_cosetWordBlock_0011
  · exact g32p_row31_cosetWordBlock_0012
  · exact g32p_row31_cosetWordBlock_0013
  · exact g32p_row31_cosetWordBlock_0014
  · exact g32p_row31_cosetWordBlock_0015
  · exact g32p_row31_cosetWordBlock_0016
  · exact g32p_row31_cosetWordBlock_0017
  · exact g32p_row31_cosetWordBlock_0018
  · exact g32p_row31_cosetWordBlock_0019
  · exact g32p_row31_cosetWordBlock_0020
  · exact g32p_row31_cosetWordBlock_0021
  · exact g32p_row31_cosetWordBlock_0022
  · exact g32p_row31_cosetWordBlock_0023
  · exact g32p_row31_cosetWordBlock_0024
  · exact g32p_row31_cosetWordBlock_0025
  · exact g32p_row31_cosetWordBlock_0026
  · exact g32p_row31_cosetWordBlock_0027
  · exact g32p_row31_cosetWordBlock_0028
  · exact g32p_row31_cosetWordBlock_0029
  · exact g32p_row31_cosetWordBlock_0030
  · exact g32p_row31_cosetWordBlock_0031
  · exact g32p_row31_cosetWordBlock_0032
  · exact g32p_row31_cosetWordBlock_0033
  · exact g32p_row31_cosetWordBlock_0034
  · exact g32p_row31_cosetWordBlock_0035
  · exact g32p_row31_cosetWordBlock_0036
  · exact g32p_row31_cosetWordBlock_0037
  · exact g32p_row31_cosetWordBlock_0038
  · exact g32p_row31_cosetWordBlock_0039
  · exact g32p_row31_cosetWordBlock_0040
  · exact g32p_row31_cosetWordBlock_0041
  · exact g32p_row31_cosetWordBlock_0042
  · exact g32p_row31_cosetWordBlock_0043
  · exact g32p_row31_cosetWordBlock_0044
  · exact g32p_row31_cosetWordBlock_0045
  · exact g32p_row31_cosetWordBlock_0046
  · exact g32p_row31_cosetWordBlock_0047
  · exact g32p_row31_cosetWordBlock_0048
  · exact g32p_row31_cosetWordBlock_0049
  · exact g32p_row31_cosetWordBlock_0050
  · exact g32p_row31_cosetWordBlock_0051
  · exact g32p_row31_cosetWordBlock_0052
  · exact g32p_row31_cosetWordBlock_0053
  · exact g32p_row31_cosetWordBlock_0054
  · exact g32p_row31_cosetWordBlock_0055
  · exact g32p_row31_cosetWordBlock_0056
  · exact g32p_row31_cosetWordBlock_0057
  · exact g32p_row31_cosetWordBlock_0058
  · exact g32p_row31_cosetWordBlock_0059
  · exact g32p_row31_cosetWordBlock_0060
  · exact g32p_row31_cosetWordBlock_0061
  · exact g32p_row31_cosetWordBlock_0062
  · exact g32p_row31_cosetWordBlock_0063
  · exact g32p_row31_cosetWordBlock_0064
  · exact g32p_row31_cosetWordBlock_0065
  · exact g32p_row31_cosetWordBlock_0066
  · exact g32p_row31_cosetWordBlock_0067
  · exact g32p_row31_cosetWordBlock_0068
  · exact g32p_row31_cosetWordBlock_0069
  · exact g32p_row31_cosetWordBlock_0070
  · exact g32p_row31_cosetWordBlock_0071
  · exact g32p_row31_cosetWordBlock_0072
  · exact g32p_row31_cosetWordBlock_0073
  · exact g32p_row31_cosetWordBlock_0074
  · exact g32p_row31_cosetWordBlock_0075
  · exact g32p_row31_cosetWordBlock_0076
  · exact g32p_row31_cosetWordBlock_0077
  · exact g32p_row31_cosetWordBlock_0078
  · exact g32p_row31_cosetWordBlock_0079
  · exact g32p_row31_cosetWordBlock_0080
  · exact g32p_row31_cosetWordBlock_0081
  · exact g32p_row31_cosetWordBlock_0082
  · exact g32p_row31_cosetWordBlock_0083
  · exact g32p_row31_cosetWordBlock_0084
  · exact g32p_row31_cosetWordBlock_0085
  · exact g32p_row31_cosetWordBlock_0086
  · exact g32p_row31_cosetWordBlock_0087
  · exact g32p_row31_cosetWordBlock_0088
  · exact g32p_row31_cosetWordBlock_0089
  · exact g32p_row31_cosetWordBlock_0090
  · exact g32p_row31_cosetWordBlock_0091
  · exact g32p_row31_cosetWordBlock_0092
  · exact g32p_row31_cosetWordBlock_0093
  · exact g32p_row31_cosetWordBlock_0094
  · exact g32p_row31_cosetWordBlock_0095
  · exact g32p_row31_cosetWordBlock_0096
  · exact g32p_row31_cosetWordBlock_0097
  · exact g32p_row31_cosetWordBlock_0098
  · exact g32p_row31_cosetWordBlock_0099
  · exact g32p_row31_cosetWordBlock_0100
  · exact g32p_row31_cosetWordBlock_0101
  · exact g32p_row31_cosetWordBlock_0102
  · exact g32p_row31_cosetWordBlock_0103
  · exact g32p_row31_cosetWordBlock_0104
  · exact g32p_row31_cosetWordBlock_0105
  · exact g32p_row31_cosetWordBlock_0106
  · exact g32p_row31_cosetWordBlock_0107
  · exact g32p_row31_cosetWordBlock_0108
  · exact g32p_row31_cosetWordBlock_0109
  · exact g32p_row31_cosetWordBlock_0110
  · exact g32p_row31_cosetWordBlock_0111
  · exact g32p_row31_cosetWordBlock_0112
  · exact g32p_row31_cosetWordBlock_0113
  · exact g32p_row31_cosetWordBlock_0114
  · exact g32p_row31_cosetWordBlock_0115
  · exact g32p_row31_cosetWordBlock_0116
  · exact g32p_row31_cosetWordBlock_0117
  · exact g32p_row31_cosetWordBlock_0118
  · exact g32p_row31_cosetWordBlock_0119
  · exact g32p_row31_cosetWordBlock_0120
  · exact g32p_row31_cosetWordBlock_0121
  · exact g32p_row31_cosetWordBlock_0122
  · exact g32p_row31_cosetWordBlock_0123
  · exact g32p_row31_cosetWordBlock_0124
  · exact g32p_row31_cosetWordBlock_0125
  · exact g32p_row31_cosetWordBlock_0126
  · exact g32p_row31_cosetWordBlock_0127
  · exact g32p_row31_cosetWordBlock_0128
  · exact g32p_row31_cosetWordBlock_0129
  · exact g32p_row31_cosetWordBlock_0130
  · exact g32p_row31_cosetWordBlock_0131
  · exact g32p_row31_cosetWordBlock_0132
  · exact g32p_row31_cosetWordBlock_0133
  · exact g32p_row31_cosetWordBlock_0134
  · exact g32p_row31_cosetWordBlock_0135
  · exact g32p_row31_cosetWordBlock_0136
  · exact g32p_row31_cosetWordBlock_0137
  · exact g32p_row31_cosetWordBlock_0138
  · exact g32p_row31_cosetWordBlock_0139
  · exact g32p_row31_cosetWordBlock_0140
  · exact g32p_row31_cosetWordBlock_0141
  · exact g32p_row31_cosetWordBlock_0142
  · exact g32p_row31_cosetWordBlock_0143
  · exact g32p_row31_cosetWordBlock_0144
  · exact g32p_row31_cosetWordBlock_0145
  · exact g32p_row31_cosetWordBlock_0146
  · exact g32p_row31_cosetWordBlock_0147
  · exact g32p_row31_cosetWordBlock_0148
  · exact g32p_row31_cosetWordBlock_0149
  · exact g32p_row31_cosetWordBlock_0150
  · exact g32p_row31_cosetWordBlock_0151
  · exact g32p_row31_cosetWordBlock_0152
  · exact g32p_row31_cosetWordBlock_0153
  · exact g32p_row31_cosetWordBlock_0154
  · exact g32p_row31_cosetWordBlock_0155
  · exact g32p_row31_cosetWordBlock_0156
  · exact g32p_row31_cosetWordBlock_0157
  · exact g32p_row31_cosetWordBlock_0158
  · exact g32p_row31_cosetWordBlock_0159
  · exact g32p_row31_cosetWordBlock_0160
  · exact g32p_row31_cosetWordBlock_0161
  · exact g32p_row31_cosetWordBlock_0162
  · exact g32p_row31_cosetWordBlock_0163
  · exact g32p_row31_cosetWordBlock_0164
  · exact g32p_row31_cosetWordBlock_0165
  · exact g32p_row31_cosetWordBlock_0166
  · exact g32p_row31_cosetWordBlock_0167
  · exact g32p_row31_cosetWordBlock_0168
  · exact g32p_row31_cosetWordBlock_0169
  · exact g32p_row31_cosetWordBlock_0170
  · exact g32p_row31_cosetWordBlock_0171
  · exact g32p_row31_cosetWordBlock_0172
  · exact g32p_row31_cosetWordBlock_0173
  · exact g32p_row31_cosetWordBlock_0174
  · exact g32p_row31_cosetWordBlock_0175
  · exact g32p_row31_cosetWordBlock_0176
  · exact g32p_row31_cosetWordBlock_0177
  · exact g32p_row31_cosetWordBlock_0178
  · exact g32p_row31_cosetWordBlock_0179
  · exact g32p_row31_cosetWordBlock_0180
  · exact g32p_row31_cosetWordBlock_0181
  · exact g32p_row31_cosetWordBlock_0182
  · exact g32p_row31_cosetWordBlock_0183
  · exact g32p_row31_cosetWordBlock_0184
  · exact g32p_row31_cosetWordBlock_0185
  · exact g32p_row31_cosetWordBlock_0186
  · exact g32p_row31_cosetWordBlock_0187
  · exact g32p_row31_cosetWordBlock_0188
  · exact g32p_row31_cosetWordBlock_0189
  · exact g32p_row31_cosetWordBlock_0190
  · exact g32p_row31_cosetWordBlock_0191
  · exact g32p_row31_cosetWordBlock_0192
  · exact g32p_row31_cosetWordBlock_0193
  · exact g32p_row31_cosetWordBlock_0194
  · exact g32p_row31_cosetWordBlock_0195
  · exact g32p_row31_cosetWordBlock_0196
  · exact g32p_row31_cosetWordBlock_0197
  · exact g32p_row31_cosetWordBlock_0198
  · exact g32p_row31_cosetWordBlock_0199
  · exact g32p_row31_cosetWordBlock_0200
  · exact g32p_row31_cosetWordBlock_0201
  · exact g32p_row31_cosetWordBlock_0202
  · exact g32p_row31_cosetWordBlock_0203
  · exact g32p_row31_cosetWordBlock_0204
  · exact g32p_row31_cosetWordBlock_0205
  · exact g32p_row31_cosetWordBlock_0206
  · exact g32p_row31_cosetWordBlock_0207
  · exact g32p_row31_cosetWordBlock_0208
  · exact g32p_row31_cosetWordBlock_0209
  · exact g32p_row31_cosetWordBlock_0210
  · exact g32p_row31_cosetWordBlock_0211
  · exact g32p_row31_cosetWordBlock_0212
  · exact g32p_row31_cosetWordBlock_0213
  · exact g32p_row31_cosetWordBlock_0214
  · exact g32p_row31_cosetWordBlock_0215
  · exact g32p_row31_cosetWordBlock_0216
  · exact g32p_row31_cosetWordBlock_0217
  · exact g32p_row31_cosetWordBlock_0218
  · exact g32p_row31_cosetWordBlock_0219
  · exact g32p_row31_cosetWordBlock_0220
  · exact g32p_row31_cosetWordBlock_0221
  · exact g32p_row31_cosetWordBlock_0222
  · exact g32p_row31_cosetWordBlock_0223
  · exact g32p_row31_cosetWordBlock_0224
  · exact g32p_row31_cosetWordBlock_0225
  · exact g32p_row31_cosetWordBlock_0226
  · exact g32p_row31_cosetWordBlock_0227
  · exact g32p_row31_cosetWordBlock_0228
  · exact g32p_row31_cosetWordBlock_0229
  · exact g32p_row31_cosetWordBlock_0230
  · exact g32p_row31_cosetWordBlock_0231
  · exact g32p_row31_cosetWordBlock_0232
  · exact g32p_row31_cosetWordBlock_0233
  · exact g32p_row31_cosetWordBlock_0234
  · exact g32p_row31_cosetWordBlock_0235
  · exact g32p_row31_cosetWordBlock_0236
  · exact g32p_row31_cosetWordBlock_0237
  · exact g32p_row31_cosetWordBlock_0238
  · exact g32p_row31_cosetWordBlock_0239
  · exact g32p_row31_cosetWordBlock_0240
  · exact g32p_row31_cosetWordBlock_0241
  · exact g32p_row31_cosetWordBlock_0242
  · exact g32p_row31_cosetWordBlock_0243
  · exact g32p_row31_cosetWordBlock_0244
  · exact g32p_row31_cosetWordBlock_0245
  · exact g32p_row31_cosetWordBlock_0246
  · exact g32p_row31_cosetWordBlock_0247
  · exact g32p_row31_cosetWordBlock_0248
  · exact g32p_row31_cosetWordBlock_0249
  · exact g32p_row31_cosetWordBlock_0250
  · exact g32p_row31_cosetWordBlock_0251
  · exact g32p_row31_cosetWordBlock_0252
  · exact g32p_row31_cosetWordBlock_0253
  · exact g32p_row31_cosetWordBlock_0254
  · exact g32p_row31_cosetWordBlock_0255
  · exact g32p_row31_cosetWordBlock_0256
  · exact g32p_row31_cosetWordBlock_0257
  · exact g32p_row31_cosetWordBlock_0258
  · exact g32p_row31_cosetWordBlock_0259
  · exact g32p_row31_cosetWordBlock_0260
  · exact g32p_row31_cosetWordBlock_0261
  · exact g32p_row31_cosetWordBlock_0262
  · exact g32p_row31_cosetWordBlock_0263
  · exact g32p_row31_cosetWordBlock_0264
  · exact g32p_row31_cosetWordBlock_0265
  · exact g32p_row31_cosetWordBlock_0266
  · exact g32p_row31_cosetWordBlock_0267
  · exact g32p_row31_cosetWordBlock_0268
  · exact g32p_row31_cosetWordBlock_0269
  · exact g32p_row31_cosetWordBlock_0270
  · exact g32p_row31_cosetWordBlock_0271
  · exact g32p_row31_cosetWordBlock_0272
  · exact g32p_row31_cosetWordBlock_0273
  · exact g32p_row31_cosetWordBlock_0274
  · exact g32p_row31_cosetWordBlock_0275
  · exact g32p_row31_cosetWordBlock_0276
  · exact g32p_row31_cosetWordBlock_0277
  · exact g32p_row31_cosetWordBlock_0278
  · exact g32p_row31_cosetWordBlock_0279
  · exact g32p_row31_cosetWordBlock_0280
  · exact g32p_row31_cosetWordBlock_0281
  · exact g32p_row31_cosetWordBlock_0282
  · exact g32p_row31_cosetWordBlock_0283
  · exact g32p_row31_cosetWordBlock_0284
  · exact g32p_row31_cosetWordBlock_0285
  · exact g32p_row31_cosetWordBlock_0286
  · exact g32p_row31_cosetWordBlock_0287
  · exact g32p_row31_cosetWordBlock_0288
  · exact g32p_row31_cosetWordBlock_0289
  · exact g32p_row31_cosetWordBlock_0290
  · exact g32p_row31_cosetWordBlock_0291
  · exact g32p_row31_cosetWordBlock_0292
  · exact g32p_row31_cosetWordBlock_0293
  · exact g32p_row31_cosetWordBlock_0294
  · exact g32p_row31_cosetWordBlock_0295
  · exact g32p_row31_cosetWordBlock_0296
  · exact g32p_row31_cosetWordBlock_0297
  · exact g32p_row31_cosetWordBlock_0298
  · exact g32p_row31_cosetWordBlock_0299
  · exact g32p_row31_cosetWordBlock_0300
  · exact g32p_row31_cosetWordBlock_0301
  · exact g32p_row31_cosetWordBlock_0302
  · exact g32p_row31_cosetWordBlock_0303
  · exact g32p_row31_cosetWordBlock_0304
  · exact g32p_row31_cosetWordBlock_0305
  · exact g32p_row31_cosetWordBlock_0306
  · exact g32p_row31_cosetWordBlock_0307
  · exact g32p_row31_cosetWordBlock_0308
  · exact g32p_row31_cosetWordBlock_0309
  · exact g32p_row31_cosetWordBlock_0310
  · exact g32p_row31_cosetWordBlock_0311
  · exact g32p_row31_cosetWordBlock_0312
  · exact g32p_row31_cosetWordBlock_0313
  · exact g32p_row31_cosetWordBlock_0314
  · exact g32p_row31_cosetWordBlock_0315
  · exact g32p_row31_cosetWordBlock_0316
  · exact g32p_row31_cosetWordBlock_0317
  · exact g32p_row31_cosetWordBlock_0318
  · exact g32p_row31_cosetWordBlock_0319
  · exact g32p_row31_cosetWordBlock_0320
  · exact g32p_row31_cosetWordBlock_0321
  · exact g32p_row31_cosetWordBlock_0322
  · exact g32p_row31_cosetWordBlock_0323
  · exact g32p_row31_cosetWordBlock_0324
  · exact g32p_row31_cosetWordBlock_0325
  · exact g32p_row31_cosetWordBlock_0326
  · exact g32p_row31_cosetWordBlock_0327
  · exact g32p_row31_cosetWordBlock_0328
  · exact g32p_row31_cosetWordBlock_0329
  · exact g32p_row31_cosetWordBlock_0330
  · exact g32p_row31_cosetWordBlock_0331
  · exact g32p_row31_cosetWordBlock_0332
  · exact g32p_row31_cosetWordBlock_0333
  · exact g32p_row31_cosetWordBlock_0334
  · exact g32p_row31_cosetWordBlock_0335
  · exact g32p_row31_cosetWordBlock_0336
  · exact g32p_row31_cosetWordBlock_0337
  · exact g32p_row31_cosetWordBlock_0338
  · exact g32p_row31_cosetWordBlock_0339
  · exact g32p_row31_cosetWordBlock_0340
  · exact g32p_row31_cosetWordBlock_0341
  · exact g32p_row31_cosetWordBlock_0342
  · exact g32p_row31_cosetWordBlock_0343
  · exact g32p_row31_cosetWordBlock_0344
  · exact g32p_row31_cosetWordBlock_0345
  · exact g32p_row31_cosetWordBlock_0346
  · exact g32p_row31_cosetWordBlock_0347
  · exact g32p_row31_cosetWordBlock_0348
  · exact g32p_row31_cosetWordBlock_0349
  · exact g32p_row31_cosetWordBlock_0350
  · exact g32p_row31_cosetWordBlock_0351
  · exact g32p_row31_cosetWordBlock_0352
  · exact g32p_row31_cosetWordBlock_0353
  · exact g32p_row31_cosetWordBlock_0354
  · exact g32p_row31_cosetWordBlock_0355
  · exact g32p_row31_cosetWordBlock_0356
  · exact g32p_row31_cosetWordBlock_0357
  · exact g32p_row31_cosetWordBlock_0358
  · exact g32p_row31_cosetWordBlock_0359
  · exact g32p_row31_cosetWordBlock_0360
  · exact g32p_row31_cosetWordBlock_0361
  · exact g32p_row31_cosetWordBlock_0362
  · exact g32p_row31_cosetWordBlock_0363
  · exact g32p_row31_cosetWordBlock_0364
  · exact g32p_row31_cosetWordBlock_0365
  · exact g32p_row31_cosetWordBlock_0366
  · exact g32p_row31_cosetWordBlock_0367
  · exact g32p_row31_cosetWordBlock_0368
  · exact g32p_row31_cosetWordBlock_0369
  · exact g32p_row31_cosetWordBlock_0370
  · exact g32p_row31_cosetWordBlock_0371
  · exact g32p_row31_cosetWordBlock_0372
  · exact g32p_row31_cosetWordBlock_0373
  · exact g32p_row31_cosetWordBlock_0374
  · exact g32p_row31_cosetWordBlock_0375
  · exact g32p_row31_cosetWordBlock_0376
  · exact g32p_row31_cosetWordBlock_0377
  · exact g32p_row31_cosetWordBlock_0378
  · exact g32p_row31_cosetWordBlock_0379
  · exact g32p_row31_cosetWordBlock_0380
  · exact g32p_row31_cosetWordBlock_0381
  · exact g32p_row31_cosetWordBlock_0382
  · exact g32p_row31_cosetWordBlock_0383
  · exact g32p_row31_cosetWordBlock_0384
  · exact g32p_row31_cosetWordBlock_0385
  · exact g32p_row31_cosetWordBlock_0386
  · exact g32p_row31_cosetWordBlock_0387
  · exact g32p_row31_cosetWordBlock_0388
  · exact g32p_row31_cosetWordBlock_0389
  · exact g32p_row31_cosetWordBlock_0390
  · exact g32p_row31_cosetWordBlock_0391
  · exact g32p_row31_cosetWordBlock_0392
  · exact g32p_row31_cosetWordBlock_0393
  · exact g32p_row31_cosetWordBlock_0394
  · exact g32p_row31_cosetWordBlock_0395
  · exact g32p_row31_cosetWordBlock_0396
  · exact g32p_row31_cosetWordBlock_0397
  · exact g32p_row31_cosetWordBlock_0398
  · exact g32p_row31_cosetWordBlock_0399
  · exact g32p_row31_cosetWordBlock_0400
  · exact g32p_row31_cosetWordBlock_0401
  · exact g32p_row31_cosetWordBlock_0402
  · exact g32p_row31_cosetWordBlock_0403
  · exact g32p_row31_cosetWordBlock_0404
  · exact g32p_row31_cosetWordBlock_0405
  · exact g32p_row31_cosetWordBlock_0406
  · exact g32p_row31_cosetWordBlock_0407
  · exact g32p_row31_cosetWordBlock_0408
  · exact g32p_row31_cosetWordBlock_0409
  · exact g32p_row31_cosetWordBlock_0410
  · exact g32p_row31_cosetWordBlock_0411
  · exact g32p_row31_cosetWordBlock_0412
  · exact g32p_row31_cosetWordBlock_0413
  · exact g32p_row31_cosetWordBlock_0414
  · exact g32p_row31_cosetWordBlock_0415
  · exact g32p_row31_cosetWordBlock_0416
  · exact g32p_row31_cosetWordBlock_0417
  · exact g32p_row31_cosetWordBlock_0418
  · exact g32p_row31_cosetWordBlock_0419
  · exact g32p_row31_cosetWordBlock_0420
  · exact g32p_row31_cosetWordBlock_0421
  · exact g32p_row31_cosetWordBlock_0422
  · exact g32p_row31_cosetWordBlock_0423
  · exact g32p_row31_cosetWordBlock_0424
  · exact g32p_row31_cosetWordBlock_0425
  · exact g32p_row31_cosetWordBlock_0426
  · exact g32p_row31_cosetWordBlock_0427
  · exact g32p_row31_cosetWordBlock_0428
  · exact g32p_row31_cosetWordBlock_0429
  · exact g32p_row31_cosetWordBlock_0430
  · exact g32p_row31_cosetWordBlock_0431
  · exact g32p_row31_cosetWordBlock_0432
  · exact g32p_row31_cosetWordBlock_0433
  · exact g32p_row31_cosetWordBlock_0434
  · exact g32p_row31_cosetWordBlock_0435
  · exact g32p_row31_cosetWordBlock_0436
  · exact g32p_row31_cosetWordBlock_0437
  · exact g32p_row31_cosetWordBlock_0438
  · exact g32p_row31_cosetWordBlock_0439
  · exact g32p_row31_cosetWordBlock_0440
  · exact g32p_row31_cosetWordBlock_0441
  · exact g32p_row31_cosetWordBlock_0442
  · exact g32p_row31_cosetWordBlock_0443
  · exact g32p_row31_cosetWordBlock_0444
  · exact g32p_row31_cosetWordBlock_0445
  · exact g32p_row31_cosetWordBlock_0446
  · exact g32p_row31_cosetWordBlock_0447
  · exact g32p_row31_cosetWordBlock_0448
  · exact g32p_row31_cosetWordBlock_0449
  · exact g32p_row31_cosetWordBlock_0450
  · exact g32p_row31_cosetWordBlock_0451
  · exact g32p_row31_cosetWordBlock_0452
  · exact g32p_row31_cosetWordBlock_0453
  · exact g32p_row31_cosetWordBlock_0454
  · exact g32p_row31_cosetWordBlock_0455
  · exact g32p_row31_cosetWordBlock_0456
  · exact g32p_row31_cosetWordBlock_0457
  · exact g32p_row31_cosetWordBlock_0458
  · exact g32p_row31_cosetWordBlock_0459
  · exact g32p_row31_cosetWordBlock_0460
  · exact g32p_row31_cosetWordBlock_0461
  · exact g32p_row31_cosetWordBlock_0462
  · exact g32p_row31_cosetWordBlock_0463
  · exact g32p_row31_cosetWordBlock_0464
  · exact g32p_row31_cosetWordBlock_0465
  · exact g32p_row31_cosetWordBlock_0466
  · exact g32p_row31_cosetWordBlock_0467
  · exact g32p_row31_cosetWordBlock_0468
  · exact g32p_row31_cosetWordBlock_0469
  · exact g32p_row31_cosetWordBlock_0470
  · exact g32p_row31_cosetWordBlock_0471
  · exact g32p_row31_cosetWordBlock_0472
  · exact g32p_row31_cosetWordBlock_0473
  · exact g32p_row31_cosetWordBlock_0474
  · exact g32p_row31_cosetWordBlock_0475
  · exact g32p_row31_cosetWordBlock_0476
  · exact g32p_row31_cosetWordBlock_0477
  · exact g32p_row31_cosetWordBlock_0478
  · exact g32p_row31_cosetWordBlock_0479
  · exact g32p_row31_cosetWordBlock_0480
  · exact g32p_row31_cosetWordBlock_0481
  · exact g32p_row31_cosetWordBlock_0482
  · exact g32p_row31_cosetWordBlock_0483
  · exact g32p_row31_cosetWordBlock_0484
  · exact g32p_row31_cosetWordBlock_0485
  · exact g32p_row31_cosetWordBlock_0486
  · exact g32p_row31_cosetWordBlock_0487
  · exact g32p_row31_cosetWordBlock_0488
  · exact g32p_row31_cosetWordBlock_0489
  · exact g32p_row31_cosetWordBlock_0490
  · exact g32p_row31_cosetWordBlock_0491
  · exact g32p_row31_cosetWordBlock_0492
  · exact g32p_row31_cosetWordBlock_0493
  · exact g32p_row31_cosetWordBlock_0494
  · exact g32p_row31_cosetWordBlock_0495
  · exact g32p_row31_cosetWordBlock_0496
  · exact g32p_row31_cosetWordBlock_0497
  · exact g32p_row31_cosetWordBlock_0498
  · exact g32p_row31_cosetWordBlock_0499
  · exact g32p_row31_cosetWordBlock_0500
  · exact g32p_row31_cosetWordBlock_0501
  · exact g32p_row31_cosetWordBlock_0502
  · exact g32p_row31_cosetWordBlock_0503
  · exact g32p_row31_cosetWordBlock_0504
  · exact g32p_row31_cosetWordBlock_0505
  · exact g32p_row31_cosetWordBlock_0506
  · exact g32p_row31_cosetWordBlock_0507
  · exact g32p_row31_cosetWordBlock_0508
  · exact g32p_row31_cosetWordBlock_0509
  · exact g32p_row31_cosetWordBlock_0510
  · exact g32p_row31_cosetWordBlock_0511
  · exact g32p_row31_cosetWordBlock_0512
  · exact g32p_row31_cosetWordBlock_0513
  · exact g32p_row31_cosetWordBlock_0514
  · exact g32p_row31_cosetWordBlock_0515
  · exact g32p_row31_cosetWordBlock_0516
  · exact g32p_row31_cosetWordBlock_0517
  · exact g32p_row31_cosetWordBlock_0518
  · exact g32p_row31_cosetWordBlock_0519
  · exact g32p_row31_cosetWordBlock_0520
  · exact g32p_row31_cosetWordBlock_0521
  · exact g32p_row31_cosetWordBlock_0522
  · exact g32p_row31_cosetWordBlock_0523
  · exact g32p_row31_cosetWordBlock_0524
  · exact g32p_row31_cosetWordBlock_0525
  · exact g32p_row31_cosetWordBlock_0526
  · exact g32p_row31_cosetWordBlock_0527
  · exact g32p_row31_cosetWordBlock_0528
  · exact g32p_row31_cosetWordBlock_0529
  · exact g32p_row31_cosetWordBlock_0530
  · exact g32p_row31_cosetWordBlock_0531
  · exact g32p_row31_cosetWordBlock_0532
  · exact g32p_row31_cosetWordBlock_0533
  · exact g32p_row31_cosetWordBlock_0534
  · exact g32p_row31_cosetWordBlock_0535
  · exact g32p_row31_cosetWordBlock_0536
  · exact g32p_row31_cosetWordBlock_0537
  · exact g32p_row31_cosetWordBlock_0538
  · exact g32p_row31_cosetWordBlock_0539


def g32p_row31_cosetActualRepresentatives (i : Fin 8640) : g32p_G := g32p_archiveWord (g32p_row31_cosetWords i)

theorem g32p_row31_cosetActualRepresentatives_map (i : Fin 8640) :
    b4b_toMatrix (g32p_row31_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row31_cosetRepresentatives i)) := by
  rw [g32p_row31_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row31_cosetWord]

theorem g32p_row31_cosetGeneratorStep (s : Fin 4) (i : Fin 8640) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s i))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row31_cosetGeneratorBlock_0000 s
  · exact g32p_row31_cosetGeneratorBlock_0001 s
  · exact g32p_row31_cosetGeneratorBlock_0002 s
  · exact g32p_row31_cosetGeneratorBlock_0003 s
  · exact g32p_row31_cosetGeneratorBlock_0004 s
  · exact g32p_row31_cosetGeneratorBlock_0005 s
  · exact g32p_row31_cosetGeneratorBlock_0006 s
  · exact g32p_row31_cosetGeneratorBlock_0007 s
  · exact g32p_row31_cosetGeneratorBlock_0008 s
  · exact g32p_row31_cosetGeneratorBlock_0009 s
  · exact g32p_row31_cosetGeneratorBlock_0010 s
  · exact g32p_row31_cosetGeneratorBlock_0011 s
  · exact g32p_row31_cosetGeneratorBlock_0012 s
  · exact g32p_row31_cosetGeneratorBlock_0013 s
  · exact g32p_row31_cosetGeneratorBlock_0014 s
  · exact g32p_row31_cosetGeneratorBlock_0015 s
  · exact g32p_row31_cosetGeneratorBlock_0016 s
  · exact g32p_row31_cosetGeneratorBlock_0017 s
  · exact g32p_row31_cosetGeneratorBlock_0018 s
  · exact g32p_row31_cosetGeneratorBlock_0019 s
  · exact g32p_row31_cosetGeneratorBlock_0020 s
  · exact g32p_row31_cosetGeneratorBlock_0021 s
  · exact g32p_row31_cosetGeneratorBlock_0022 s
  · exact g32p_row31_cosetGeneratorBlock_0023 s
  · exact g32p_row31_cosetGeneratorBlock_0024 s
  · exact g32p_row31_cosetGeneratorBlock_0025 s
  · exact g32p_row31_cosetGeneratorBlock_0026 s
  · exact g32p_row31_cosetGeneratorBlock_0027 s
  · exact g32p_row31_cosetGeneratorBlock_0028 s
  · exact g32p_row31_cosetGeneratorBlock_0029 s
  · exact g32p_row31_cosetGeneratorBlock_0030 s
  · exact g32p_row31_cosetGeneratorBlock_0031 s
  · exact g32p_row31_cosetGeneratorBlock_0032 s
  · exact g32p_row31_cosetGeneratorBlock_0033 s
  · exact g32p_row31_cosetGeneratorBlock_0034 s
  · exact g32p_row31_cosetGeneratorBlock_0035 s
  · exact g32p_row31_cosetGeneratorBlock_0036 s
  · exact g32p_row31_cosetGeneratorBlock_0037 s
  · exact g32p_row31_cosetGeneratorBlock_0038 s
  · exact g32p_row31_cosetGeneratorBlock_0039 s
  · exact g32p_row31_cosetGeneratorBlock_0040 s
  · exact g32p_row31_cosetGeneratorBlock_0041 s
  · exact g32p_row31_cosetGeneratorBlock_0042 s
  · exact g32p_row31_cosetGeneratorBlock_0043 s
  · exact g32p_row31_cosetGeneratorBlock_0044 s
  · exact g32p_row31_cosetGeneratorBlock_0045 s
  · exact g32p_row31_cosetGeneratorBlock_0046 s
  · exact g32p_row31_cosetGeneratorBlock_0047 s
  · exact g32p_row31_cosetGeneratorBlock_0048 s
  · exact g32p_row31_cosetGeneratorBlock_0049 s
  · exact g32p_row31_cosetGeneratorBlock_0050 s
  · exact g32p_row31_cosetGeneratorBlock_0051 s
  · exact g32p_row31_cosetGeneratorBlock_0052 s
  · exact g32p_row31_cosetGeneratorBlock_0053 s
  · exact g32p_row31_cosetGeneratorBlock_0054 s
  · exact g32p_row31_cosetGeneratorBlock_0055 s
  · exact g32p_row31_cosetGeneratorBlock_0056 s
  · exact g32p_row31_cosetGeneratorBlock_0057 s
  · exact g32p_row31_cosetGeneratorBlock_0058 s
  · exact g32p_row31_cosetGeneratorBlock_0059 s
  · exact g32p_row31_cosetGeneratorBlock_0060 s
  · exact g32p_row31_cosetGeneratorBlock_0061 s
  · exact g32p_row31_cosetGeneratorBlock_0062 s
  · exact g32p_row31_cosetGeneratorBlock_0063 s
  · exact g32p_row31_cosetGeneratorBlock_0064 s
  · exact g32p_row31_cosetGeneratorBlock_0065 s
  · exact g32p_row31_cosetGeneratorBlock_0066 s
  · exact g32p_row31_cosetGeneratorBlock_0067 s
  · exact g32p_row31_cosetGeneratorBlock_0068 s
  · exact g32p_row31_cosetGeneratorBlock_0069 s
  · exact g32p_row31_cosetGeneratorBlock_0070 s
  · exact g32p_row31_cosetGeneratorBlock_0071 s
  · exact g32p_row31_cosetGeneratorBlock_0072 s
  · exact g32p_row31_cosetGeneratorBlock_0073 s
  · exact g32p_row31_cosetGeneratorBlock_0074 s
  · exact g32p_row31_cosetGeneratorBlock_0075 s
  · exact g32p_row31_cosetGeneratorBlock_0076 s
  · exact g32p_row31_cosetGeneratorBlock_0077 s
  · exact g32p_row31_cosetGeneratorBlock_0078 s
  · exact g32p_row31_cosetGeneratorBlock_0079 s
  · exact g32p_row31_cosetGeneratorBlock_0080 s
  · exact g32p_row31_cosetGeneratorBlock_0081 s
  · exact g32p_row31_cosetGeneratorBlock_0082 s
  · exact g32p_row31_cosetGeneratorBlock_0083 s
  · exact g32p_row31_cosetGeneratorBlock_0084 s
  · exact g32p_row31_cosetGeneratorBlock_0085 s
  · exact g32p_row31_cosetGeneratorBlock_0086 s
  · exact g32p_row31_cosetGeneratorBlock_0087 s
  · exact g32p_row31_cosetGeneratorBlock_0088 s
  · exact g32p_row31_cosetGeneratorBlock_0089 s
  · exact g32p_row31_cosetGeneratorBlock_0090 s
  · exact g32p_row31_cosetGeneratorBlock_0091 s
  · exact g32p_row31_cosetGeneratorBlock_0092 s
  · exact g32p_row31_cosetGeneratorBlock_0093 s
  · exact g32p_row31_cosetGeneratorBlock_0094 s
  · exact g32p_row31_cosetGeneratorBlock_0095 s
  · exact g32p_row31_cosetGeneratorBlock_0096 s
  · exact g32p_row31_cosetGeneratorBlock_0097 s
  · exact g32p_row31_cosetGeneratorBlock_0098 s
  · exact g32p_row31_cosetGeneratorBlock_0099 s
  · exact g32p_row31_cosetGeneratorBlock_0100 s
  · exact g32p_row31_cosetGeneratorBlock_0101 s
  · exact g32p_row31_cosetGeneratorBlock_0102 s
  · exact g32p_row31_cosetGeneratorBlock_0103 s
  · exact g32p_row31_cosetGeneratorBlock_0104 s
  · exact g32p_row31_cosetGeneratorBlock_0105 s
  · exact g32p_row31_cosetGeneratorBlock_0106 s
  · exact g32p_row31_cosetGeneratorBlock_0107 s
  · exact g32p_row31_cosetGeneratorBlock_0108 s
  · exact g32p_row31_cosetGeneratorBlock_0109 s
  · exact g32p_row31_cosetGeneratorBlock_0110 s
  · exact g32p_row31_cosetGeneratorBlock_0111 s
  · exact g32p_row31_cosetGeneratorBlock_0112 s
  · exact g32p_row31_cosetGeneratorBlock_0113 s
  · exact g32p_row31_cosetGeneratorBlock_0114 s
  · exact g32p_row31_cosetGeneratorBlock_0115 s
  · exact g32p_row31_cosetGeneratorBlock_0116 s
  · exact g32p_row31_cosetGeneratorBlock_0117 s
  · exact g32p_row31_cosetGeneratorBlock_0118 s
  · exact g32p_row31_cosetGeneratorBlock_0119 s
  · exact g32p_row31_cosetGeneratorBlock_0120 s
  · exact g32p_row31_cosetGeneratorBlock_0121 s
  · exact g32p_row31_cosetGeneratorBlock_0122 s
  · exact g32p_row31_cosetGeneratorBlock_0123 s
  · exact g32p_row31_cosetGeneratorBlock_0124 s
  · exact g32p_row31_cosetGeneratorBlock_0125 s
  · exact g32p_row31_cosetGeneratorBlock_0126 s
  · exact g32p_row31_cosetGeneratorBlock_0127 s
  · exact g32p_row31_cosetGeneratorBlock_0128 s
  · exact g32p_row31_cosetGeneratorBlock_0129 s
  · exact g32p_row31_cosetGeneratorBlock_0130 s
  · exact g32p_row31_cosetGeneratorBlock_0131 s
  · exact g32p_row31_cosetGeneratorBlock_0132 s
  · exact g32p_row31_cosetGeneratorBlock_0133 s
  · exact g32p_row31_cosetGeneratorBlock_0134 s
  · exact g32p_row31_cosetGeneratorBlock_0135 s
  · exact g32p_row31_cosetGeneratorBlock_0136 s
  · exact g32p_row31_cosetGeneratorBlock_0137 s
  · exact g32p_row31_cosetGeneratorBlock_0138 s
  · exact g32p_row31_cosetGeneratorBlock_0139 s
  · exact g32p_row31_cosetGeneratorBlock_0140 s
  · exact g32p_row31_cosetGeneratorBlock_0141 s
  · exact g32p_row31_cosetGeneratorBlock_0142 s
  · exact g32p_row31_cosetGeneratorBlock_0143 s
  · exact g32p_row31_cosetGeneratorBlock_0144 s
  · exact g32p_row31_cosetGeneratorBlock_0145 s
  · exact g32p_row31_cosetGeneratorBlock_0146 s
  · exact g32p_row31_cosetGeneratorBlock_0147 s
  · exact g32p_row31_cosetGeneratorBlock_0148 s
  · exact g32p_row31_cosetGeneratorBlock_0149 s
  · exact g32p_row31_cosetGeneratorBlock_0150 s
  · exact g32p_row31_cosetGeneratorBlock_0151 s
  · exact g32p_row31_cosetGeneratorBlock_0152 s
  · exact g32p_row31_cosetGeneratorBlock_0153 s
  · exact g32p_row31_cosetGeneratorBlock_0154 s
  · exact g32p_row31_cosetGeneratorBlock_0155 s
  · exact g32p_row31_cosetGeneratorBlock_0156 s
  · exact g32p_row31_cosetGeneratorBlock_0157 s
  · exact g32p_row31_cosetGeneratorBlock_0158 s
  · exact g32p_row31_cosetGeneratorBlock_0159 s
  · exact g32p_row31_cosetGeneratorBlock_0160 s
  · exact g32p_row31_cosetGeneratorBlock_0161 s
  · exact g32p_row31_cosetGeneratorBlock_0162 s
  · exact g32p_row31_cosetGeneratorBlock_0163 s
  · exact g32p_row31_cosetGeneratorBlock_0164 s
  · exact g32p_row31_cosetGeneratorBlock_0165 s
  · exact g32p_row31_cosetGeneratorBlock_0166 s
  · exact g32p_row31_cosetGeneratorBlock_0167 s
  · exact g32p_row31_cosetGeneratorBlock_0168 s
  · exact g32p_row31_cosetGeneratorBlock_0169 s
  · exact g32p_row31_cosetGeneratorBlock_0170 s
  · exact g32p_row31_cosetGeneratorBlock_0171 s
  · exact g32p_row31_cosetGeneratorBlock_0172 s
  · exact g32p_row31_cosetGeneratorBlock_0173 s
  · exact g32p_row31_cosetGeneratorBlock_0174 s
  · exact g32p_row31_cosetGeneratorBlock_0175 s
  · exact g32p_row31_cosetGeneratorBlock_0176 s
  · exact g32p_row31_cosetGeneratorBlock_0177 s
  · exact g32p_row31_cosetGeneratorBlock_0178 s
  · exact g32p_row31_cosetGeneratorBlock_0179 s
  · exact g32p_row31_cosetGeneratorBlock_0180 s
  · exact g32p_row31_cosetGeneratorBlock_0181 s
  · exact g32p_row31_cosetGeneratorBlock_0182 s
  · exact g32p_row31_cosetGeneratorBlock_0183 s
  · exact g32p_row31_cosetGeneratorBlock_0184 s
  · exact g32p_row31_cosetGeneratorBlock_0185 s
  · exact g32p_row31_cosetGeneratorBlock_0186 s
  · exact g32p_row31_cosetGeneratorBlock_0187 s
  · exact g32p_row31_cosetGeneratorBlock_0188 s
  · exact g32p_row31_cosetGeneratorBlock_0189 s
  · exact g32p_row31_cosetGeneratorBlock_0190 s
  · exact g32p_row31_cosetGeneratorBlock_0191 s
  · exact g32p_row31_cosetGeneratorBlock_0192 s
  · exact g32p_row31_cosetGeneratorBlock_0193 s
  · exact g32p_row31_cosetGeneratorBlock_0194 s
  · exact g32p_row31_cosetGeneratorBlock_0195 s
  · exact g32p_row31_cosetGeneratorBlock_0196 s
  · exact g32p_row31_cosetGeneratorBlock_0197 s
  · exact g32p_row31_cosetGeneratorBlock_0198 s
  · exact g32p_row31_cosetGeneratorBlock_0199 s
  · exact g32p_row31_cosetGeneratorBlock_0200 s
  · exact g32p_row31_cosetGeneratorBlock_0201 s
  · exact g32p_row31_cosetGeneratorBlock_0202 s
  · exact g32p_row31_cosetGeneratorBlock_0203 s
  · exact g32p_row31_cosetGeneratorBlock_0204 s
  · exact g32p_row31_cosetGeneratorBlock_0205 s
  · exact g32p_row31_cosetGeneratorBlock_0206 s
  · exact g32p_row31_cosetGeneratorBlock_0207 s
  · exact g32p_row31_cosetGeneratorBlock_0208 s
  · exact g32p_row31_cosetGeneratorBlock_0209 s
  · exact g32p_row31_cosetGeneratorBlock_0210 s
  · exact g32p_row31_cosetGeneratorBlock_0211 s
  · exact g32p_row31_cosetGeneratorBlock_0212 s
  · exact g32p_row31_cosetGeneratorBlock_0213 s
  · exact g32p_row31_cosetGeneratorBlock_0214 s
  · exact g32p_row31_cosetGeneratorBlock_0215 s
  · exact g32p_row31_cosetGeneratorBlock_0216 s
  · exact g32p_row31_cosetGeneratorBlock_0217 s
  · exact g32p_row31_cosetGeneratorBlock_0218 s
  · exact g32p_row31_cosetGeneratorBlock_0219 s
  · exact g32p_row31_cosetGeneratorBlock_0220 s
  · exact g32p_row31_cosetGeneratorBlock_0221 s
  · exact g32p_row31_cosetGeneratorBlock_0222 s
  · exact g32p_row31_cosetGeneratorBlock_0223 s
  · exact g32p_row31_cosetGeneratorBlock_0224 s
  · exact g32p_row31_cosetGeneratorBlock_0225 s
  · exact g32p_row31_cosetGeneratorBlock_0226 s
  · exact g32p_row31_cosetGeneratorBlock_0227 s
  · exact g32p_row31_cosetGeneratorBlock_0228 s
  · exact g32p_row31_cosetGeneratorBlock_0229 s
  · exact g32p_row31_cosetGeneratorBlock_0230 s
  · exact g32p_row31_cosetGeneratorBlock_0231 s
  · exact g32p_row31_cosetGeneratorBlock_0232 s
  · exact g32p_row31_cosetGeneratorBlock_0233 s
  · exact g32p_row31_cosetGeneratorBlock_0234 s
  · exact g32p_row31_cosetGeneratorBlock_0235 s
  · exact g32p_row31_cosetGeneratorBlock_0236 s
  · exact g32p_row31_cosetGeneratorBlock_0237 s
  · exact g32p_row31_cosetGeneratorBlock_0238 s
  · exact g32p_row31_cosetGeneratorBlock_0239 s
  · exact g32p_row31_cosetGeneratorBlock_0240 s
  · exact g32p_row31_cosetGeneratorBlock_0241 s
  · exact g32p_row31_cosetGeneratorBlock_0242 s
  · exact g32p_row31_cosetGeneratorBlock_0243 s
  · exact g32p_row31_cosetGeneratorBlock_0244 s
  · exact g32p_row31_cosetGeneratorBlock_0245 s
  · exact g32p_row31_cosetGeneratorBlock_0246 s
  · exact g32p_row31_cosetGeneratorBlock_0247 s
  · exact g32p_row31_cosetGeneratorBlock_0248 s
  · exact g32p_row31_cosetGeneratorBlock_0249 s
  · exact g32p_row31_cosetGeneratorBlock_0250 s
  · exact g32p_row31_cosetGeneratorBlock_0251 s
  · exact g32p_row31_cosetGeneratorBlock_0252 s
  · exact g32p_row31_cosetGeneratorBlock_0253 s
  · exact g32p_row31_cosetGeneratorBlock_0254 s
  · exact g32p_row31_cosetGeneratorBlock_0255 s
  · exact g32p_row31_cosetGeneratorBlock_0256 s
  · exact g32p_row31_cosetGeneratorBlock_0257 s
  · exact g32p_row31_cosetGeneratorBlock_0258 s
  · exact g32p_row31_cosetGeneratorBlock_0259 s
  · exact g32p_row31_cosetGeneratorBlock_0260 s
  · exact g32p_row31_cosetGeneratorBlock_0261 s
  · exact g32p_row31_cosetGeneratorBlock_0262 s
  · exact g32p_row31_cosetGeneratorBlock_0263 s
  · exact g32p_row31_cosetGeneratorBlock_0264 s
  · exact g32p_row31_cosetGeneratorBlock_0265 s
  · exact g32p_row31_cosetGeneratorBlock_0266 s
  · exact g32p_row31_cosetGeneratorBlock_0267 s
  · exact g32p_row31_cosetGeneratorBlock_0268 s
  · exact g32p_row31_cosetGeneratorBlock_0269 s
  · exact g32p_row31_cosetGeneratorBlock_0270 s
  · exact g32p_row31_cosetGeneratorBlock_0271 s
  · exact g32p_row31_cosetGeneratorBlock_0272 s
  · exact g32p_row31_cosetGeneratorBlock_0273 s
  · exact g32p_row31_cosetGeneratorBlock_0274 s
  · exact g32p_row31_cosetGeneratorBlock_0275 s
  · exact g32p_row31_cosetGeneratorBlock_0276 s
  · exact g32p_row31_cosetGeneratorBlock_0277 s
  · exact g32p_row31_cosetGeneratorBlock_0278 s
  · exact g32p_row31_cosetGeneratorBlock_0279 s
  · exact g32p_row31_cosetGeneratorBlock_0280 s
  · exact g32p_row31_cosetGeneratorBlock_0281 s
  · exact g32p_row31_cosetGeneratorBlock_0282 s
  · exact g32p_row31_cosetGeneratorBlock_0283 s
  · exact g32p_row31_cosetGeneratorBlock_0284 s
  · exact g32p_row31_cosetGeneratorBlock_0285 s
  · exact g32p_row31_cosetGeneratorBlock_0286 s
  · exact g32p_row31_cosetGeneratorBlock_0287 s
  · exact g32p_row31_cosetGeneratorBlock_0288 s
  · exact g32p_row31_cosetGeneratorBlock_0289 s
  · exact g32p_row31_cosetGeneratorBlock_0290 s
  · exact g32p_row31_cosetGeneratorBlock_0291 s
  · exact g32p_row31_cosetGeneratorBlock_0292 s
  · exact g32p_row31_cosetGeneratorBlock_0293 s
  · exact g32p_row31_cosetGeneratorBlock_0294 s
  · exact g32p_row31_cosetGeneratorBlock_0295 s
  · exact g32p_row31_cosetGeneratorBlock_0296 s
  · exact g32p_row31_cosetGeneratorBlock_0297 s
  · exact g32p_row31_cosetGeneratorBlock_0298 s
  · exact g32p_row31_cosetGeneratorBlock_0299 s
  · exact g32p_row31_cosetGeneratorBlock_0300 s
  · exact g32p_row31_cosetGeneratorBlock_0301 s
  · exact g32p_row31_cosetGeneratorBlock_0302 s
  · exact g32p_row31_cosetGeneratorBlock_0303 s
  · exact g32p_row31_cosetGeneratorBlock_0304 s
  · exact g32p_row31_cosetGeneratorBlock_0305 s
  · exact g32p_row31_cosetGeneratorBlock_0306 s
  · exact g32p_row31_cosetGeneratorBlock_0307 s
  · exact g32p_row31_cosetGeneratorBlock_0308 s
  · exact g32p_row31_cosetGeneratorBlock_0309 s
  · exact g32p_row31_cosetGeneratorBlock_0310 s
  · exact g32p_row31_cosetGeneratorBlock_0311 s
  · exact g32p_row31_cosetGeneratorBlock_0312 s
  · exact g32p_row31_cosetGeneratorBlock_0313 s
  · exact g32p_row31_cosetGeneratorBlock_0314 s
  · exact g32p_row31_cosetGeneratorBlock_0315 s
  · exact g32p_row31_cosetGeneratorBlock_0316 s
  · exact g32p_row31_cosetGeneratorBlock_0317 s
  · exact g32p_row31_cosetGeneratorBlock_0318 s
  · exact g32p_row31_cosetGeneratorBlock_0319 s
  · exact g32p_row31_cosetGeneratorBlock_0320 s
  · exact g32p_row31_cosetGeneratorBlock_0321 s
  · exact g32p_row31_cosetGeneratorBlock_0322 s
  · exact g32p_row31_cosetGeneratorBlock_0323 s
  · exact g32p_row31_cosetGeneratorBlock_0324 s
  · exact g32p_row31_cosetGeneratorBlock_0325 s
  · exact g32p_row31_cosetGeneratorBlock_0326 s
  · exact g32p_row31_cosetGeneratorBlock_0327 s
  · exact g32p_row31_cosetGeneratorBlock_0328 s
  · exact g32p_row31_cosetGeneratorBlock_0329 s
  · exact g32p_row31_cosetGeneratorBlock_0330 s
  · exact g32p_row31_cosetGeneratorBlock_0331 s
  · exact g32p_row31_cosetGeneratorBlock_0332 s
  · exact g32p_row31_cosetGeneratorBlock_0333 s
  · exact g32p_row31_cosetGeneratorBlock_0334 s
  · exact g32p_row31_cosetGeneratorBlock_0335 s
  · exact g32p_row31_cosetGeneratorBlock_0336 s
  · exact g32p_row31_cosetGeneratorBlock_0337 s
  · exact g32p_row31_cosetGeneratorBlock_0338 s
  · exact g32p_row31_cosetGeneratorBlock_0339 s
  · exact g32p_row31_cosetGeneratorBlock_0340 s
  · exact g32p_row31_cosetGeneratorBlock_0341 s
  · exact g32p_row31_cosetGeneratorBlock_0342 s
  · exact g32p_row31_cosetGeneratorBlock_0343 s
  · exact g32p_row31_cosetGeneratorBlock_0344 s
  · exact g32p_row31_cosetGeneratorBlock_0345 s
  · exact g32p_row31_cosetGeneratorBlock_0346 s
  · exact g32p_row31_cosetGeneratorBlock_0347 s
  · exact g32p_row31_cosetGeneratorBlock_0348 s
  · exact g32p_row31_cosetGeneratorBlock_0349 s
  · exact g32p_row31_cosetGeneratorBlock_0350 s
  · exact g32p_row31_cosetGeneratorBlock_0351 s
  · exact g32p_row31_cosetGeneratorBlock_0352 s
  · exact g32p_row31_cosetGeneratorBlock_0353 s
  · exact g32p_row31_cosetGeneratorBlock_0354 s
  · exact g32p_row31_cosetGeneratorBlock_0355 s
  · exact g32p_row31_cosetGeneratorBlock_0356 s
  · exact g32p_row31_cosetGeneratorBlock_0357 s
  · exact g32p_row31_cosetGeneratorBlock_0358 s
  · exact g32p_row31_cosetGeneratorBlock_0359 s
  · exact g32p_row31_cosetGeneratorBlock_0360 s
  · exact g32p_row31_cosetGeneratorBlock_0361 s
  · exact g32p_row31_cosetGeneratorBlock_0362 s
  · exact g32p_row31_cosetGeneratorBlock_0363 s
  · exact g32p_row31_cosetGeneratorBlock_0364 s
  · exact g32p_row31_cosetGeneratorBlock_0365 s
  · exact g32p_row31_cosetGeneratorBlock_0366 s
  · exact g32p_row31_cosetGeneratorBlock_0367 s
  · exact g32p_row31_cosetGeneratorBlock_0368 s
  · exact g32p_row31_cosetGeneratorBlock_0369 s
  · exact g32p_row31_cosetGeneratorBlock_0370 s
  · exact g32p_row31_cosetGeneratorBlock_0371 s
  · exact g32p_row31_cosetGeneratorBlock_0372 s
  · exact g32p_row31_cosetGeneratorBlock_0373 s
  · exact g32p_row31_cosetGeneratorBlock_0374 s
  · exact g32p_row31_cosetGeneratorBlock_0375 s
  · exact g32p_row31_cosetGeneratorBlock_0376 s
  · exact g32p_row31_cosetGeneratorBlock_0377 s
  · exact g32p_row31_cosetGeneratorBlock_0378 s
  · exact g32p_row31_cosetGeneratorBlock_0379 s
  · exact g32p_row31_cosetGeneratorBlock_0380 s
  · exact g32p_row31_cosetGeneratorBlock_0381 s
  · exact g32p_row31_cosetGeneratorBlock_0382 s
  · exact g32p_row31_cosetGeneratorBlock_0383 s
  · exact g32p_row31_cosetGeneratorBlock_0384 s
  · exact g32p_row31_cosetGeneratorBlock_0385 s
  · exact g32p_row31_cosetGeneratorBlock_0386 s
  · exact g32p_row31_cosetGeneratorBlock_0387 s
  · exact g32p_row31_cosetGeneratorBlock_0388 s
  · exact g32p_row31_cosetGeneratorBlock_0389 s
  · exact g32p_row31_cosetGeneratorBlock_0390 s
  · exact g32p_row31_cosetGeneratorBlock_0391 s
  · exact g32p_row31_cosetGeneratorBlock_0392 s
  · exact g32p_row31_cosetGeneratorBlock_0393 s
  · exact g32p_row31_cosetGeneratorBlock_0394 s
  · exact g32p_row31_cosetGeneratorBlock_0395 s
  · exact g32p_row31_cosetGeneratorBlock_0396 s
  · exact g32p_row31_cosetGeneratorBlock_0397 s
  · exact g32p_row31_cosetGeneratorBlock_0398 s
  · exact g32p_row31_cosetGeneratorBlock_0399 s
  · exact g32p_row31_cosetGeneratorBlock_0400 s
  · exact g32p_row31_cosetGeneratorBlock_0401 s
  · exact g32p_row31_cosetGeneratorBlock_0402 s
  · exact g32p_row31_cosetGeneratorBlock_0403 s
  · exact g32p_row31_cosetGeneratorBlock_0404 s
  · exact g32p_row31_cosetGeneratorBlock_0405 s
  · exact g32p_row31_cosetGeneratorBlock_0406 s
  · exact g32p_row31_cosetGeneratorBlock_0407 s
  · exact g32p_row31_cosetGeneratorBlock_0408 s
  · exact g32p_row31_cosetGeneratorBlock_0409 s
  · exact g32p_row31_cosetGeneratorBlock_0410 s
  · exact g32p_row31_cosetGeneratorBlock_0411 s
  · exact g32p_row31_cosetGeneratorBlock_0412 s
  · exact g32p_row31_cosetGeneratorBlock_0413 s
  · exact g32p_row31_cosetGeneratorBlock_0414 s
  · exact g32p_row31_cosetGeneratorBlock_0415 s
  · exact g32p_row31_cosetGeneratorBlock_0416 s
  · exact g32p_row31_cosetGeneratorBlock_0417 s
  · exact g32p_row31_cosetGeneratorBlock_0418 s
  · exact g32p_row31_cosetGeneratorBlock_0419 s
  · exact g32p_row31_cosetGeneratorBlock_0420 s
  · exact g32p_row31_cosetGeneratorBlock_0421 s
  · exact g32p_row31_cosetGeneratorBlock_0422 s
  · exact g32p_row31_cosetGeneratorBlock_0423 s
  · exact g32p_row31_cosetGeneratorBlock_0424 s
  · exact g32p_row31_cosetGeneratorBlock_0425 s
  · exact g32p_row31_cosetGeneratorBlock_0426 s
  · exact g32p_row31_cosetGeneratorBlock_0427 s
  · exact g32p_row31_cosetGeneratorBlock_0428 s
  · exact g32p_row31_cosetGeneratorBlock_0429 s
  · exact g32p_row31_cosetGeneratorBlock_0430 s
  · exact g32p_row31_cosetGeneratorBlock_0431 s
  · exact g32p_row31_cosetGeneratorBlock_0432 s
  · exact g32p_row31_cosetGeneratorBlock_0433 s
  · exact g32p_row31_cosetGeneratorBlock_0434 s
  · exact g32p_row31_cosetGeneratorBlock_0435 s
  · exact g32p_row31_cosetGeneratorBlock_0436 s
  · exact g32p_row31_cosetGeneratorBlock_0437 s
  · exact g32p_row31_cosetGeneratorBlock_0438 s
  · exact g32p_row31_cosetGeneratorBlock_0439 s
  · exact g32p_row31_cosetGeneratorBlock_0440 s
  · exact g32p_row31_cosetGeneratorBlock_0441 s
  · exact g32p_row31_cosetGeneratorBlock_0442 s
  · exact g32p_row31_cosetGeneratorBlock_0443 s
  · exact g32p_row31_cosetGeneratorBlock_0444 s
  · exact g32p_row31_cosetGeneratorBlock_0445 s
  · exact g32p_row31_cosetGeneratorBlock_0446 s
  · exact g32p_row31_cosetGeneratorBlock_0447 s
  · exact g32p_row31_cosetGeneratorBlock_0448 s
  · exact g32p_row31_cosetGeneratorBlock_0449 s
  · exact g32p_row31_cosetGeneratorBlock_0450 s
  · exact g32p_row31_cosetGeneratorBlock_0451 s
  · exact g32p_row31_cosetGeneratorBlock_0452 s
  · exact g32p_row31_cosetGeneratorBlock_0453 s
  · exact g32p_row31_cosetGeneratorBlock_0454 s
  · exact g32p_row31_cosetGeneratorBlock_0455 s
  · exact g32p_row31_cosetGeneratorBlock_0456 s
  · exact g32p_row31_cosetGeneratorBlock_0457 s
  · exact g32p_row31_cosetGeneratorBlock_0458 s
  · exact g32p_row31_cosetGeneratorBlock_0459 s
  · exact g32p_row31_cosetGeneratorBlock_0460 s
  · exact g32p_row31_cosetGeneratorBlock_0461 s
  · exact g32p_row31_cosetGeneratorBlock_0462 s
  · exact g32p_row31_cosetGeneratorBlock_0463 s
  · exact g32p_row31_cosetGeneratorBlock_0464 s
  · exact g32p_row31_cosetGeneratorBlock_0465 s
  · exact g32p_row31_cosetGeneratorBlock_0466 s
  · exact g32p_row31_cosetGeneratorBlock_0467 s
  · exact g32p_row31_cosetGeneratorBlock_0468 s
  · exact g32p_row31_cosetGeneratorBlock_0469 s
  · exact g32p_row31_cosetGeneratorBlock_0470 s
  · exact g32p_row31_cosetGeneratorBlock_0471 s
  · exact g32p_row31_cosetGeneratorBlock_0472 s
  · exact g32p_row31_cosetGeneratorBlock_0473 s
  · exact g32p_row31_cosetGeneratorBlock_0474 s
  · exact g32p_row31_cosetGeneratorBlock_0475 s
  · exact g32p_row31_cosetGeneratorBlock_0476 s
  · exact g32p_row31_cosetGeneratorBlock_0477 s
  · exact g32p_row31_cosetGeneratorBlock_0478 s
  · exact g32p_row31_cosetGeneratorBlock_0479 s
  · exact g32p_row31_cosetGeneratorBlock_0480 s
  · exact g32p_row31_cosetGeneratorBlock_0481 s
  · exact g32p_row31_cosetGeneratorBlock_0482 s
  · exact g32p_row31_cosetGeneratorBlock_0483 s
  · exact g32p_row31_cosetGeneratorBlock_0484 s
  · exact g32p_row31_cosetGeneratorBlock_0485 s
  · exact g32p_row31_cosetGeneratorBlock_0486 s
  · exact g32p_row31_cosetGeneratorBlock_0487 s
  · exact g32p_row31_cosetGeneratorBlock_0488 s
  · exact g32p_row31_cosetGeneratorBlock_0489 s
  · exact g32p_row31_cosetGeneratorBlock_0490 s
  · exact g32p_row31_cosetGeneratorBlock_0491 s
  · exact g32p_row31_cosetGeneratorBlock_0492 s
  · exact g32p_row31_cosetGeneratorBlock_0493 s
  · exact g32p_row31_cosetGeneratorBlock_0494 s
  · exact g32p_row31_cosetGeneratorBlock_0495 s
  · exact g32p_row31_cosetGeneratorBlock_0496 s
  · exact g32p_row31_cosetGeneratorBlock_0497 s
  · exact g32p_row31_cosetGeneratorBlock_0498 s
  · exact g32p_row31_cosetGeneratorBlock_0499 s
  · exact g32p_row31_cosetGeneratorBlock_0500 s
  · exact g32p_row31_cosetGeneratorBlock_0501 s
  · exact g32p_row31_cosetGeneratorBlock_0502 s
  · exact g32p_row31_cosetGeneratorBlock_0503 s
  · exact g32p_row31_cosetGeneratorBlock_0504 s
  · exact g32p_row31_cosetGeneratorBlock_0505 s
  · exact g32p_row31_cosetGeneratorBlock_0506 s
  · exact g32p_row31_cosetGeneratorBlock_0507 s
  · exact g32p_row31_cosetGeneratorBlock_0508 s
  · exact g32p_row31_cosetGeneratorBlock_0509 s
  · exact g32p_row31_cosetGeneratorBlock_0510 s
  · exact g32p_row31_cosetGeneratorBlock_0511 s
  · exact g32p_row31_cosetGeneratorBlock_0512 s
  · exact g32p_row31_cosetGeneratorBlock_0513 s
  · exact g32p_row31_cosetGeneratorBlock_0514 s
  · exact g32p_row31_cosetGeneratorBlock_0515 s
  · exact g32p_row31_cosetGeneratorBlock_0516 s
  · exact g32p_row31_cosetGeneratorBlock_0517 s
  · exact g32p_row31_cosetGeneratorBlock_0518 s
  · exact g32p_row31_cosetGeneratorBlock_0519 s
  · exact g32p_row31_cosetGeneratorBlock_0520 s
  · exact g32p_row31_cosetGeneratorBlock_0521 s
  · exact g32p_row31_cosetGeneratorBlock_0522 s
  · exact g32p_row31_cosetGeneratorBlock_0523 s
  · exact g32p_row31_cosetGeneratorBlock_0524 s
  · exact g32p_row31_cosetGeneratorBlock_0525 s
  · exact g32p_row31_cosetGeneratorBlock_0526 s
  · exact g32p_row31_cosetGeneratorBlock_0527 s
  · exact g32p_row31_cosetGeneratorBlock_0528 s
  · exact g32p_row31_cosetGeneratorBlock_0529 s
  · exact g32p_row31_cosetGeneratorBlock_0530 s
  · exact g32p_row31_cosetGeneratorBlock_0531 s
  · exact g32p_row31_cosetGeneratorBlock_0532 s
  · exact g32p_row31_cosetGeneratorBlock_0533 s
  · exact g32p_row31_cosetGeneratorBlock_0534 s
  · exact g32p_row31_cosetGeneratorBlock_0535 s
  · exact g32p_row31_cosetGeneratorBlock_0536 s
  · exact g32p_row31_cosetGeneratorBlock_0537 s
  · exact g32p_row31_cosetGeneratorBlock_0538 s
  · exact g32p_row31_cosetGeneratorBlock_0539 s


theorem g32p_row31_cosetActualStep (s : Fin 4) (i : Fin 8640) :
    g32p_word (g32p_archiveWords s) * g32p_row31_cosetActualRepresentatives i =
      g32p_row31_cosetActualRepresentatives (g32p_row31_cosetGeneratorNext s i) *
        (g32p_row31_groupEquiv (g32p_row31_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row31_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row31_cosetActualRepresentatives (g32p_row31_cosetGeneratorNext s i) *
      (g32p_row31_groupEquiv (g32p_row31_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row31_cosetActualRepresentatives_map,
    g32p_row31_cosetActualRepresentatives_map, g32p_row31_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row31_cosetGeneratorStep]

theorem g32p_row31_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row31_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row31_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row31_cosetGeneratorNext
      (fun s i => g32p_row31_groupEquiv (g32p_row31_cosetGeneratorFactor s i))
    exact g32p_row31_cosetActualStep
  · rw [g32p_row31_finiteSupplier_order]
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

theorem g32p_row31_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 0)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 0)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 0) = g32p_row31_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 1)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 1)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 1) = g32p_row31_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 2)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 2)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 2) = g32p_row31_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 3)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 3)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 3) = g32p_row31_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 4)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 4)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 4) = g32p_row31_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 5)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 5)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 5) = g32p_row31_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 6)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 6)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 6) = g32p_row31_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 7)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 7)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 7) = g32p_row31_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 8)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 8)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 8) = g32p_row31_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 9)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 9)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 9) = g32p_row31_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 10)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 10)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 10) = g32p_row31_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 11)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 11)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 11) = g32p_row31_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 12)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 12)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 12) = g32p_row31_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 13)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 13)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 13) = g32p_row31_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 14)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 14)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 14) = g32p_row31_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 15)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 15)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 15) = g32p_row31_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row31_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row31_cosetBranchMatrices 0) (g32p_row31_cosetLengths0 (g32p_finBlockIndex 2880 0 r)))
      (g32p_row31_cosetRepresentatives (g32p_row31_cosetRoots0 (g32p_finBlockIndex 2880 0 r))) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetRoots0 (g32p_finBlockIndex 2880 0 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 (g32p_finBlockIndex 2880 0 r))) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 (g32p_finBlockIndex 2880 0 r)) = g32p_row31_cosetExponents0 (g32p_finBlockIndex 2880 0 r) := by
  fin_cases r
  · exact g32p_row31_cosetMonodromy_0_0000
  · exact g32p_row31_cosetMonodromy_0_0001
  · exact g32p_row31_cosetMonodromy_0_0002
  · exact g32p_row31_cosetMonodromy_0_0003
  · exact g32p_row31_cosetMonodromy_0_0004
  · exact g32p_row31_cosetMonodromy_0_0005
  · exact g32p_row31_cosetMonodromy_0_0006
  · exact g32p_row31_cosetMonodromy_0_0007
  · exact g32p_row31_cosetMonodromy_0_0008
  · exact g32p_row31_cosetMonodromy_0_0009
  · exact g32p_row31_cosetMonodromy_0_0010
  · exact g32p_row31_cosetMonodromy_0_0011
  · exact g32p_row31_cosetMonodromy_0_0012
  · exact g32p_row31_cosetMonodromy_0_0013
  · exact g32p_row31_cosetMonodromy_0_0014
  · exact g32p_row31_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 16)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 16)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 16) = g32p_row31_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 17)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 17)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 17) = g32p_row31_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 18)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 18)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 18) = g32p_row31_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 19)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 19)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 19) = g32p_row31_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 20)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 20)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 20) = g32p_row31_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 21)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 21)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 21) = g32p_row31_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 22)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 22)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 22) = g32p_row31_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 23)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 23)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 23) = g32p_row31_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 24)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 24)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 24) = g32p_row31_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 25)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 25)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 25) = g32p_row31_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 26)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 26)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 26) = g32p_row31_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 27)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 27)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 27) = g32p_row31_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 28)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 28)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 28) = g32p_row31_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 29)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 29)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 29) = g32p_row31_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 30)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 30)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 30) = g32p_row31_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 31)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 31)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 31) = g32p_row31_cosetExponents0 31 := by
  decide +kernel

theorem g32p_row31_cosetMonodromyBlock0_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row31_cosetBranchMatrices 0) (g32p_row31_cosetLengths0 (g32p_finBlockIndex 2880 1 r)))
      (g32p_row31_cosetRepresentatives (g32p_row31_cosetRoots0 (g32p_finBlockIndex 2880 1 r))) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetRoots0 (g32p_finBlockIndex 2880 1 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 (g32p_finBlockIndex 2880 1 r))) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 (g32p_finBlockIndex 2880 1 r)) = g32p_row31_cosetExponents0 (g32p_finBlockIndex 2880 1 r) := by
  fin_cases r
  · exact g32p_row31_cosetMonodromy_0_0016
  · exact g32p_row31_cosetMonodromy_0_0017
  · exact g32p_row31_cosetMonodromy_0_0018
  · exact g32p_row31_cosetMonodromy_0_0019
  · exact g32p_row31_cosetMonodromy_0_0020
  · exact g32p_row31_cosetMonodromy_0_0021
  · exact g32p_row31_cosetMonodromy_0_0022
  · exact g32p_row31_cosetMonodromy_0_0023
  · exact g32p_row31_cosetMonodromy_0_0024
  · exact g32p_row31_cosetMonodromy_0_0025
  · exact g32p_row31_cosetMonodromy_0_0026
  · exact g32p_row31_cosetMonodromy_0_0027
  · exact g32p_row31_cosetMonodromy_0_0028
  · exact g32p_row31_cosetMonodromy_0_0029
  · exact g32p_row31_cosetMonodromy_0_0030
  · exact g32p_row31_cosetMonodromy_0_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetMonodromy_0_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 32)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 32)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 32) = g32p_row31_cosetExponents0 32 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 33)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 33)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 33) = g32p_row31_cosetExponents0 33 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 34)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 34)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 34) = g32p_row31_cosetExponents0 34 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 35)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 35)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 35) = g32p_row31_cosetExponents0 35 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 36)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 36)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 36) = g32p_row31_cosetExponents0 36 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 37)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 37)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 37) = g32p_row31_cosetExponents0 37 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 38)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 38)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 38) = g32p_row31_cosetExponents0 38 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 39)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 39)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 39) = g32p_row31_cosetExponents0 39 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 40)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 40)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 40) = g32p_row31_cosetExponents0 40 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 41)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 41)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 41) = g32p_row31_cosetExponents0 41 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 42)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 42)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 42) = g32p_row31_cosetExponents0 42 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 43)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 43)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 43) = g32p_row31_cosetExponents0 43 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 44)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 44)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 44) = g32p_row31_cosetExponents0 44 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 45)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 45)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 45) = g32p_row31_cosetExponents0 45 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 46)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 46)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 46) = g32p_row31_cosetExponents0 46 := by
  decide +kernel

theorem g32p_row31_cosetMonodromy_0_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row31_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives 47)
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 47)) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 47) = g32p_row31_cosetExponents0 47 := by
  decide +kernel

theorem g32p_row31_cosetMonodromyBlock0_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row31_cosetBranchMatrices 0) (g32p_row31_cosetLengths0 (g32p_finBlockIndex 2880 2 r)))
      (g32p_row31_cosetRepresentatives (g32p_row31_cosetRoots0 (g32p_finBlockIndex 2880 2 r))) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetRoots0 (g32p_finBlockIndex 2880 2 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetMonodromies0 (g32p_finBlockIndex 2880 2 r))) ∧
    g32p_row31_characterValues (g32p_row31_cosetMonodromies0 (g32p_finBlockIndex 2880 2 r)) = g32p_row31_cosetExponents0 (g32p_finBlockIndex 2880 2 r) := by
  fin_cases r
  · exact g32p_row31_cosetMonodromy_0_0032
  · exact g32p_row31_cosetMonodromy_0_0033
  · exact g32p_row31_cosetMonodromy_0_0034
  · exact g32p_row31_cosetMonodromy_0_0035
  · exact g32p_row31_cosetMonodromy_0_0036
  · exact g32p_row31_cosetMonodromy_0_0037
  · exact g32p_row31_cosetMonodromy_0_0038
  · exact g32p_row31_cosetMonodromy_0_0039
  · exact g32p_row31_cosetMonodromy_0_0040
  · exact g32p_row31_cosetMonodromy_0_0041
  · exact g32p_row31_cosetMonodromy_0_0042
  · exact g32p_row31_cosetMonodromy_0_0043
  · exact g32p_row31_cosetMonodromy_0_0044
  · exact g32p_row31_cosetMonodromy_0_0045
  · exact g32p_row31_cosetMonodromy_0_0046
  · exact g32p_row31_cosetMonodromy_0_0047


end HodgeLean.Foundations.Program

end
