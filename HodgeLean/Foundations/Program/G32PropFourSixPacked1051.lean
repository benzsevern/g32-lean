import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked1044

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1536 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1536) = g32p_row13_cosetRepresentatives 1536 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1536 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1536) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1536))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1536)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1536 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1536) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1536))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1536)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1537 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1537) = g32p_row13_cosetRepresentatives 1537 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1537 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1537) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1537))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1537)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1537 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1537) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1537))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1537)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1538 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1538) = g32p_row13_cosetRepresentatives 1538 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1538 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1538) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1538))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1538)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1538 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1538) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1538))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1538)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1539 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1539) = g32p_row13_cosetRepresentatives 1539 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1539 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1539) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1539))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1539)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1539 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1539) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1539))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1539)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1540 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1540) = g32p_row13_cosetRepresentatives 1540 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1540 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1540) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1540))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1540)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1540 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1540) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1540))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1540)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1541 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1541) = g32p_row13_cosetRepresentatives 1541 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1541 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1541) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1541))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1541)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1541 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1541) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1541))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1541)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1542 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1542) = g32p_row13_cosetRepresentatives 1542 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1542 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1542) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1542))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1542)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1542 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1542) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1542))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1542)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1543 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1543) = g32p_row13_cosetRepresentatives 1543 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1543 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1543) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1543))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1543)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1543 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1543) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1543))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1543)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1544 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1544) = g32p_row13_cosetRepresentatives 1544 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1544 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1544) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1544))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1544)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1544 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1544) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1544))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1544)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1545 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1545) = g32p_row13_cosetRepresentatives 1545 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1545 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1545) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1545))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1545)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1545 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1545) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1545))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1545)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1546 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1546) = g32p_row13_cosetRepresentatives 1546 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1546 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1546) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1546))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1546)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1546 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1546) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1546))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1546)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1547 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1547) = g32p_row13_cosetRepresentatives 1547 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1547 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1547) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1547))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1547)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1547 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1547) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1547))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1547)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1548 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1548) = g32p_row13_cosetRepresentatives 1548 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1548 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1548) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1548))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1548)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1548 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1548) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1548))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1548)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1549 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1549) = g32p_row13_cosetRepresentatives 1549 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1549 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1549) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1549))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1549)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1549 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1549) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1549))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1549)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1550 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1550) = g32p_row13_cosetRepresentatives 1550 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1550 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1550) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1550))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1550)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1550 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1550) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1550))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1550)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1551 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1551) = g32p_row13_cosetRepresentatives 1551 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1551 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1551) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1551))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1551)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1551 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1551) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1551))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1551)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0096 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 96 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 96 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1536
  · exact g32p_row13_cosetWord_1537
  · exact g32p_row13_cosetWord_1538
  · exact g32p_row13_cosetWord_1539
  · exact g32p_row13_cosetWord_1540
  · exact g32p_row13_cosetWord_1541
  · exact g32p_row13_cosetWord_1542
  · exact g32p_row13_cosetWord_1543
  · exact g32p_row13_cosetWord_1544
  · exact g32p_row13_cosetWord_1545
  · exact g32p_row13_cosetWord_1546
  · exact g32p_row13_cosetWord_1547
  · exact g32p_row13_cosetWord_1548
  · exact g32p_row13_cosetWord_1549
  · exact g32p_row13_cosetWord_1550
  · exact g32p_row13_cosetWord_1551

theorem g32p_row13_cosetGeneratorBlock_0096 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 96 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 96 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 96 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1536 s
  · exact g32p_row13_cosetGeneratorStep_1537 s
  · exact g32p_row13_cosetGeneratorStep_1538 s
  · exact g32p_row13_cosetGeneratorStep_1539 s
  · exact g32p_row13_cosetGeneratorStep_1540 s
  · exact g32p_row13_cosetGeneratorStep_1541 s
  · exact g32p_row13_cosetGeneratorStep_1542 s
  · exact g32p_row13_cosetGeneratorStep_1543 s
  · exact g32p_row13_cosetGeneratorStep_1544 s
  · exact g32p_row13_cosetGeneratorStep_1545 s
  · exact g32p_row13_cosetGeneratorStep_1546 s
  · exact g32p_row13_cosetGeneratorStep_1547 s
  · exact g32p_row13_cosetGeneratorStep_1548 s
  · exact g32p_row13_cosetGeneratorStep_1549 s
  · exact g32p_row13_cosetGeneratorStep_1550 s
  · exact g32p_row13_cosetGeneratorStep_1551 s

theorem g32p_row13_cosetBranchBlock_0096 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 96 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 96 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 96 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1536 s
  · exact g32p_row13_cosetBranchStep_1537 s
  · exact g32p_row13_cosetBranchStep_1538 s
  · exact g32p_row13_cosetBranchStep_1539 s
  · exact g32p_row13_cosetBranchStep_1540 s
  · exact g32p_row13_cosetBranchStep_1541 s
  · exact g32p_row13_cosetBranchStep_1542 s
  · exact g32p_row13_cosetBranchStep_1543 s
  · exact g32p_row13_cosetBranchStep_1544 s
  · exact g32p_row13_cosetBranchStep_1545 s
  · exact g32p_row13_cosetBranchStep_1546 s
  · exact g32p_row13_cosetBranchStep_1547 s
  · exact g32p_row13_cosetBranchStep_1548 s
  · exact g32p_row13_cosetBranchStep_1549 s
  · exact g32p_row13_cosetBranchStep_1550 s
  · exact g32p_row13_cosetBranchStep_1551 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1552 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1552) = g32p_row13_cosetRepresentatives 1552 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1552 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1552) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1552))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1552)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1552 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1552) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1552))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1552)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1553 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1553) = g32p_row13_cosetRepresentatives 1553 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1553 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1553) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1553))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1553)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1553 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1553) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1553))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1553)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1554 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1554) = g32p_row13_cosetRepresentatives 1554 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1554 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1554) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1554))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1554)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1554 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1554) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1554))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1554)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1555 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1555) = g32p_row13_cosetRepresentatives 1555 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1555 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1555) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1555))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1555)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1555 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1555) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1555))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1555)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1556 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1556) = g32p_row13_cosetRepresentatives 1556 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1556 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1556) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1556))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1556)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1556 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1556) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1556))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1556)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1557 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1557) = g32p_row13_cosetRepresentatives 1557 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1557 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1557) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1557))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1557)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1557 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1557) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1557))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1557)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1558 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1558) = g32p_row13_cosetRepresentatives 1558 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1558 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1558) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1558))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1558)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1558 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1558) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1558))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1558)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1559 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1559) = g32p_row13_cosetRepresentatives 1559 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1559 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1559) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1559))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1559)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1559 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1559) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1559))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1559)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1560 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1560) = g32p_row13_cosetRepresentatives 1560 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1560 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1560) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1560))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1560)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1560 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1560) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1560))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1560)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1561 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1561) = g32p_row13_cosetRepresentatives 1561 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1561 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1561) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1561))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1561)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1561 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1561) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1561))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1561)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1562 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1562) = g32p_row13_cosetRepresentatives 1562 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1562 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1562) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1562))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1562)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1562 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1562) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1562))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1562)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1563 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1563) = g32p_row13_cosetRepresentatives 1563 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1563 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1563) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1563))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1563)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1563 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1563) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1563))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1563)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1564 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1564) = g32p_row13_cosetRepresentatives 1564 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1564 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1564) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1564))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1564)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1564 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1564) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1564))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1564)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1565 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1565) = g32p_row13_cosetRepresentatives 1565 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1565 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1565) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1565))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1565)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1565 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1565) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1565))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1565)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1566 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1566) = g32p_row13_cosetRepresentatives 1566 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1566 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1566) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1566))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1566)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1566 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1566) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1566))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1566)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1567 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1567) = g32p_row13_cosetRepresentatives 1567 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1567 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1567) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1567))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1567)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1567 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1567) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1567))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1567)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0097 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 97 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 97 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1552
  · exact g32p_row13_cosetWord_1553
  · exact g32p_row13_cosetWord_1554
  · exact g32p_row13_cosetWord_1555
  · exact g32p_row13_cosetWord_1556
  · exact g32p_row13_cosetWord_1557
  · exact g32p_row13_cosetWord_1558
  · exact g32p_row13_cosetWord_1559
  · exact g32p_row13_cosetWord_1560
  · exact g32p_row13_cosetWord_1561
  · exact g32p_row13_cosetWord_1562
  · exact g32p_row13_cosetWord_1563
  · exact g32p_row13_cosetWord_1564
  · exact g32p_row13_cosetWord_1565
  · exact g32p_row13_cosetWord_1566
  · exact g32p_row13_cosetWord_1567

theorem g32p_row13_cosetGeneratorBlock_0097 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 97 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 97 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 97 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1552 s
  · exact g32p_row13_cosetGeneratorStep_1553 s
  · exact g32p_row13_cosetGeneratorStep_1554 s
  · exact g32p_row13_cosetGeneratorStep_1555 s
  · exact g32p_row13_cosetGeneratorStep_1556 s
  · exact g32p_row13_cosetGeneratorStep_1557 s
  · exact g32p_row13_cosetGeneratorStep_1558 s
  · exact g32p_row13_cosetGeneratorStep_1559 s
  · exact g32p_row13_cosetGeneratorStep_1560 s
  · exact g32p_row13_cosetGeneratorStep_1561 s
  · exact g32p_row13_cosetGeneratorStep_1562 s
  · exact g32p_row13_cosetGeneratorStep_1563 s
  · exact g32p_row13_cosetGeneratorStep_1564 s
  · exact g32p_row13_cosetGeneratorStep_1565 s
  · exact g32p_row13_cosetGeneratorStep_1566 s
  · exact g32p_row13_cosetGeneratorStep_1567 s

theorem g32p_row13_cosetBranchBlock_0097 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 97 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 97 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 97 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1552 s
  · exact g32p_row13_cosetBranchStep_1553 s
  · exact g32p_row13_cosetBranchStep_1554 s
  · exact g32p_row13_cosetBranchStep_1555 s
  · exact g32p_row13_cosetBranchStep_1556 s
  · exact g32p_row13_cosetBranchStep_1557 s
  · exact g32p_row13_cosetBranchStep_1558 s
  · exact g32p_row13_cosetBranchStep_1559 s
  · exact g32p_row13_cosetBranchStep_1560 s
  · exact g32p_row13_cosetBranchStep_1561 s
  · exact g32p_row13_cosetBranchStep_1562 s
  · exact g32p_row13_cosetBranchStep_1563 s
  · exact g32p_row13_cosetBranchStep_1564 s
  · exact g32p_row13_cosetBranchStep_1565 s
  · exact g32p_row13_cosetBranchStep_1566 s
  · exact g32p_row13_cosetBranchStep_1567 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1568 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1568) = g32p_row13_cosetRepresentatives 1568 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1568 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1568) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1568))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1568)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1568 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1568) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1568))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1568)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1569 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1569) = g32p_row13_cosetRepresentatives 1569 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1569 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1569) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1569))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1569)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1569 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1569) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1569))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1569)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1570 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1570) = g32p_row13_cosetRepresentatives 1570 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1570 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1570) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1570))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1570)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1570 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1570) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1570))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1570)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1571 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1571) = g32p_row13_cosetRepresentatives 1571 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1571 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1571) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1571))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1571)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1571 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1571) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1571))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1571)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1572 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1572) = g32p_row13_cosetRepresentatives 1572 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1572 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1572) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1572))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1572)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1572 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1572) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1572))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1572)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1573 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1573) = g32p_row13_cosetRepresentatives 1573 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1573 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1573) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1573))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1573)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1573 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1573) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1573))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1573)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1574 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1574) = g32p_row13_cosetRepresentatives 1574 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1574 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1574) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1574))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1574)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1574 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1574) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1574))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1574)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1575 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1575) = g32p_row13_cosetRepresentatives 1575 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1575 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1575) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1575))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1575)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1575 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1575) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1575))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1575)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1576 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1576) = g32p_row13_cosetRepresentatives 1576 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1576 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1576) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1576))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1576)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1576 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1576) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1576))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1576)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1577 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1577) = g32p_row13_cosetRepresentatives 1577 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1577 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1577) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1577))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1577)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1577 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1577) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1577))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1577)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1578 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1578) = g32p_row13_cosetRepresentatives 1578 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1578 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1578) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1578))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1578)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1578 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1578) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1578))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1578)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1579 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1579) = g32p_row13_cosetRepresentatives 1579 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1579 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1579) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1579))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1579)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1579 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1579) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1579))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1579)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1580 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1580) = g32p_row13_cosetRepresentatives 1580 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1580 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1580) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1580))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1580)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1580 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1580) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1580))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1580)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1581 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1581) = g32p_row13_cosetRepresentatives 1581 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1581 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1581) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1581))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1581)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1581 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1581) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1581))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1581)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1582 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1582) = g32p_row13_cosetRepresentatives 1582 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1582 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1582) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1582))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1582)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1582 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1582) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1582))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1582)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1583 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1583) = g32p_row13_cosetRepresentatives 1583 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1583 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1583) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1583))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1583)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1583 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1583) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1583))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1583)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0098 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 98 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 98 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1568
  · exact g32p_row13_cosetWord_1569
  · exact g32p_row13_cosetWord_1570
  · exact g32p_row13_cosetWord_1571
  · exact g32p_row13_cosetWord_1572
  · exact g32p_row13_cosetWord_1573
  · exact g32p_row13_cosetWord_1574
  · exact g32p_row13_cosetWord_1575
  · exact g32p_row13_cosetWord_1576
  · exact g32p_row13_cosetWord_1577
  · exact g32p_row13_cosetWord_1578
  · exact g32p_row13_cosetWord_1579
  · exact g32p_row13_cosetWord_1580
  · exact g32p_row13_cosetWord_1581
  · exact g32p_row13_cosetWord_1582
  · exact g32p_row13_cosetWord_1583

theorem g32p_row13_cosetGeneratorBlock_0098 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 98 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 98 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 98 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1568 s
  · exact g32p_row13_cosetGeneratorStep_1569 s
  · exact g32p_row13_cosetGeneratorStep_1570 s
  · exact g32p_row13_cosetGeneratorStep_1571 s
  · exact g32p_row13_cosetGeneratorStep_1572 s
  · exact g32p_row13_cosetGeneratorStep_1573 s
  · exact g32p_row13_cosetGeneratorStep_1574 s
  · exact g32p_row13_cosetGeneratorStep_1575 s
  · exact g32p_row13_cosetGeneratorStep_1576 s
  · exact g32p_row13_cosetGeneratorStep_1577 s
  · exact g32p_row13_cosetGeneratorStep_1578 s
  · exact g32p_row13_cosetGeneratorStep_1579 s
  · exact g32p_row13_cosetGeneratorStep_1580 s
  · exact g32p_row13_cosetGeneratorStep_1581 s
  · exact g32p_row13_cosetGeneratorStep_1582 s
  · exact g32p_row13_cosetGeneratorStep_1583 s

theorem g32p_row13_cosetBranchBlock_0098 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 98 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 98 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 98 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1568 s
  · exact g32p_row13_cosetBranchStep_1569 s
  · exact g32p_row13_cosetBranchStep_1570 s
  · exact g32p_row13_cosetBranchStep_1571 s
  · exact g32p_row13_cosetBranchStep_1572 s
  · exact g32p_row13_cosetBranchStep_1573 s
  · exact g32p_row13_cosetBranchStep_1574 s
  · exact g32p_row13_cosetBranchStep_1575 s
  · exact g32p_row13_cosetBranchStep_1576 s
  · exact g32p_row13_cosetBranchStep_1577 s
  · exact g32p_row13_cosetBranchStep_1578 s
  · exact g32p_row13_cosetBranchStep_1579 s
  · exact g32p_row13_cosetBranchStep_1580 s
  · exact g32p_row13_cosetBranchStep_1581 s
  · exact g32p_row13_cosetBranchStep_1582 s
  · exact g32p_row13_cosetBranchStep_1583 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1584 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1584) = g32p_row13_cosetRepresentatives 1584 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1584 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1584) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1584))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1584)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1584 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1584) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1584))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1584)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1585 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1585) = g32p_row13_cosetRepresentatives 1585 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1585 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1585) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1585))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1585)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1585 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1585) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1585))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1585)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1586 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1586) = g32p_row13_cosetRepresentatives 1586 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1586 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1586) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1586))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1586)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1586 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1586) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1586))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1586)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1587 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1587) = g32p_row13_cosetRepresentatives 1587 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1587 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1587) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1587))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1587)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1587 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1587) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1587))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1587)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1588 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1588) = g32p_row13_cosetRepresentatives 1588 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1588 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1588) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1588))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1588)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1588 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1588) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1588))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1588)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1589 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1589) = g32p_row13_cosetRepresentatives 1589 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1589 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1589) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1589))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1589)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1589 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1589) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1589))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1589)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1590 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1590) = g32p_row13_cosetRepresentatives 1590 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1590 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1590) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1590))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1590)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1590 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1590) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1590))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1590)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1591 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1591) = g32p_row13_cosetRepresentatives 1591 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1591 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1591) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1591))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1591)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1591 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1591) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1591))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1591)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1592 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1592) = g32p_row13_cosetRepresentatives 1592 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1592 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1592) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1592))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1592)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1592 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1592) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1592))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1592)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1593 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1593) = g32p_row13_cosetRepresentatives 1593 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1593 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1593) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1593))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1593)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1593 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1593) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1593))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1593)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1594 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1594) = g32p_row13_cosetRepresentatives 1594 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1594 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1594) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1594))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1594)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1594 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1594) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1594))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1594)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1595 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1595) = g32p_row13_cosetRepresentatives 1595 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1595 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1595) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1595))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1595)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1595 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1595) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1595))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1595)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1596 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1596) = g32p_row13_cosetRepresentatives 1596 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1596 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1596) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1596))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1596)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1596 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1596) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1596))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1596)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1597 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1597) = g32p_row13_cosetRepresentatives 1597 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1597 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1597) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1597))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1597)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1597 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1597) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1597))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1597)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1598 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1598) = g32p_row13_cosetRepresentatives 1598 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1598 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1598) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1598))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1598)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1598 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1598) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1598))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1598)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1599 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1599) = g32p_row13_cosetRepresentatives 1599 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1599 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1599) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1599))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1599)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1599 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1599) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1599))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1599)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0099 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 99 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 99 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1584
  · exact g32p_row13_cosetWord_1585
  · exact g32p_row13_cosetWord_1586
  · exact g32p_row13_cosetWord_1587
  · exact g32p_row13_cosetWord_1588
  · exact g32p_row13_cosetWord_1589
  · exact g32p_row13_cosetWord_1590
  · exact g32p_row13_cosetWord_1591
  · exact g32p_row13_cosetWord_1592
  · exact g32p_row13_cosetWord_1593
  · exact g32p_row13_cosetWord_1594
  · exact g32p_row13_cosetWord_1595
  · exact g32p_row13_cosetWord_1596
  · exact g32p_row13_cosetWord_1597
  · exact g32p_row13_cosetWord_1598
  · exact g32p_row13_cosetWord_1599

theorem g32p_row13_cosetGeneratorBlock_0099 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 99 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 99 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 99 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1584 s
  · exact g32p_row13_cosetGeneratorStep_1585 s
  · exact g32p_row13_cosetGeneratorStep_1586 s
  · exact g32p_row13_cosetGeneratorStep_1587 s
  · exact g32p_row13_cosetGeneratorStep_1588 s
  · exact g32p_row13_cosetGeneratorStep_1589 s
  · exact g32p_row13_cosetGeneratorStep_1590 s
  · exact g32p_row13_cosetGeneratorStep_1591 s
  · exact g32p_row13_cosetGeneratorStep_1592 s
  · exact g32p_row13_cosetGeneratorStep_1593 s
  · exact g32p_row13_cosetGeneratorStep_1594 s
  · exact g32p_row13_cosetGeneratorStep_1595 s
  · exact g32p_row13_cosetGeneratorStep_1596 s
  · exact g32p_row13_cosetGeneratorStep_1597 s
  · exact g32p_row13_cosetGeneratorStep_1598 s
  · exact g32p_row13_cosetGeneratorStep_1599 s

theorem g32p_row13_cosetBranchBlock_0099 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 99 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 99 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 99 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1584 s
  · exact g32p_row13_cosetBranchStep_1585 s
  · exact g32p_row13_cosetBranchStep_1586 s
  · exact g32p_row13_cosetBranchStep_1587 s
  · exact g32p_row13_cosetBranchStep_1588 s
  · exact g32p_row13_cosetBranchStep_1589 s
  · exact g32p_row13_cosetBranchStep_1590 s
  · exact g32p_row13_cosetBranchStep_1591 s
  · exact g32p_row13_cosetBranchStep_1592 s
  · exact g32p_row13_cosetBranchStep_1593 s
  · exact g32p_row13_cosetBranchStep_1594 s
  · exact g32p_row13_cosetBranchStep_1595 s
  · exact g32p_row13_cosetBranchStep_1596 s
  · exact g32p_row13_cosetBranchStep_1597 s
  · exact g32p_row13_cosetBranchStep_1598 s
  · exact g32p_row13_cosetBranchStep_1599 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1600 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1600) = g32p_row13_cosetRepresentatives 1600 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1600 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1600) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1600))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1600)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1600 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1600) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1600))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1600)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1601 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1601) = g32p_row13_cosetRepresentatives 1601 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1601 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1601) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1601))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1601)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1601 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1601) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1601))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1601)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1602 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1602) = g32p_row13_cosetRepresentatives 1602 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1602 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1602) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1602))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1602)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1602 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1602) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1602))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1602)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1603 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1603) = g32p_row13_cosetRepresentatives 1603 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1603 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1603) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1603))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1603)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1603 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1603) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1603))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1603)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1604 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1604) = g32p_row13_cosetRepresentatives 1604 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1604 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1604) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1604))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1604)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1604 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1604) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1604))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1604)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1605 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1605) = g32p_row13_cosetRepresentatives 1605 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1605 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1605) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1605))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1605)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1605 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1605) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1605))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1605)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1606 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1606) = g32p_row13_cosetRepresentatives 1606 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1606 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1606) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1606))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1606)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1606 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1606) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1606))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1606)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1607 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1607) = g32p_row13_cosetRepresentatives 1607 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1607 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1607) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1607))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1607)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1607 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1607) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1607))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1607)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1608 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1608) = g32p_row13_cosetRepresentatives 1608 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1608 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1608) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1608))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1608)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1608 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1608) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1608))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1608)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1609 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1609) = g32p_row13_cosetRepresentatives 1609 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1609 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1609) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1609))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1609)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1609 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1609) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1609))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1609)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1610 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1610) = g32p_row13_cosetRepresentatives 1610 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1610 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1610) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1610))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1610)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1610 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1610) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1610))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1610)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1611 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1611) = g32p_row13_cosetRepresentatives 1611 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1611 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1611) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1611))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1611)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1611 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1611) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1611))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1611)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1612 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1612) = g32p_row13_cosetRepresentatives 1612 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1612 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1612) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1612))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1612)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1612 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1612) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1612))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1612)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1613 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1613) = g32p_row13_cosetRepresentatives 1613 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1613 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1613) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1613))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1613)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1613 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1613) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1613))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1613)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1614 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1614) = g32p_row13_cosetRepresentatives 1614 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1614 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1614) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1614))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1614)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1614 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1614) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1614))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1614)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1615 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1615) = g32p_row13_cosetRepresentatives 1615 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1615 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1615) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1615))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1615)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1615 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1615) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1615))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1615)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0100 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 100 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 100 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1600
  · exact g32p_row13_cosetWord_1601
  · exact g32p_row13_cosetWord_1602
  · exact g32p_row13_cosetWord_1603
  · exact g32p_row13_cosetWord_1604
  · exact g32p_row13_cosetWord_1605
  · exact g32p_row13_cosetWord_1606
  · exact g32p_row13_cosetWord_1607
  · exact g32p_row13_cosetWord_1608
  · exact g32p_row13_cosetWord_1609
  · exact g32p_row13_cosetWord_1610
  · exact g32p_row13_cosetWord_1611
  · exact g32p_row13_cosetWord_1612
  · exact g32p_row13_cosetWord_1613
  · exact g32p_row13_cosetWord_1614
  · exact g32p_row13_cosetWord_1615

theorem g32p_row13_cosetGeneratorBlock_0100 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 100 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 100 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 100 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1600 s
  · exact g32p_row13_cosetGeneratorStep_1601 s
  · exact g32p_row13_cosetGeneratorStep_1602 s
  · exact g32p_row13_cosetGeneratorStep_1603 s
  · exact g32p_row13_cosetGeneratorStep_1604 s
  · exact g32p_row13_cosetGeneratorStep_1605 s
  · exact g32p_row13_cosetGeneratorStep_1606 s
  · exact g32p_row13_cosetGeneratorStep_1607 s
  · exact g32p_row13_cosetGeneratorStep_1608 s
  · exact g32p_row13_cosetGeneratorStep_1609 s
  · exact g32p_row13_cosetGeneratorStep_1610 s
  · exact g32p_row13_cosetGeneratorStep_1611 s
  · exact g32p_row13_cosetGeneratorStep_1612 s
  · exact g32p_row13_cosetGeneratorStep_1613 s
  · exact g32p_row13_cosetGeneratorStep_1614 s
  · exact g32p_row13_cosetGeneratorStep_1615 s

theorem g32p_row13_cosetBranchBlock_0100 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 100 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 100 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 100 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1600 s
  · exact g32p_row13_cosetBranchStep_1601 s
  · exact g32p_row13_cosetBranchStep_1602 s
  · exact g32p_row13_cosetBranchStep_1603 s
  · exact g32p_row13_cosetBranchStep_1604 s
  · exact g32p_row13_cosetBranchStep_1605 s
  · exact g32p_row13_cosetBranchStep_1606 s
  · exact g32p_row13_cosetBranchStep_1607 s
  · exact g32p_row13_cosetBranchStep_1608 s
  · exact g32p_row13_cosetBranchStep_1609 s
  · exact g32p_row13_cosetBranchStep_1610 s
  · exact g32p_row13_cosetBranchStep_1611 s
  · exact g32p_row13_cosetBranchStep_1612 s
  · exact g32p_row13_cosetBranchStep_1613 s
  · exact g32p_row13_cosetBranchStep_1614 s
  · exact g32p_row13_cosetBranchStep_1615 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1616 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1616) = g32p_row13_cosetRepresentatives 1616 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1616 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1616) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1616))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1616)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1616 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1616) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1616))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1616)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1617 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1617) = g32p_row13_cosetRepresentatives 1617 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1617 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1617) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1617))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1617)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1617 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1617) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1617))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1617)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1618 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1618) = g32p_row13_cosetRepresentatives 1618 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1618 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1618) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1618))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1618)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1618 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1618) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1618))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1618)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1619 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1619) = g32p_row13_cosetRepresentatives 1619 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1619 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1619) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1619))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1619)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1619 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1619) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1619))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1619)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1620 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1620) = g32p_row13_cosetRepresentatives 1620 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1620 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1620) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1620))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1620)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1620 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1620) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1620))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1620)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1621 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1621) = g32p_row13_cosetRepresentatives 1621 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1621 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1621) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1621))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1621)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1621 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1621) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1621))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1621)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1622 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1622) = g32p_row13_cosetRepresentatives 1622 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1622 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1622) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1622))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1622)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1622 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1622) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1622))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1622)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1623 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1623) = g32p_row13_cosetRepresentatives 1623 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1623 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1623) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1623))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1623)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1623 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1623) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1623))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1623)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1624 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1624) = g32p_row13_cosetRepresentatives 1624 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1624 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1624) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1624))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1624)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1624 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1624) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1624))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1624)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1625 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1625) = g32p_row13_cosetRepresentatives 1625 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1625 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1625) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1625))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1625)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1625 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1625) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1625))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1625)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1626 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1626) = g32p_row13_cosetRepresentatives 1626 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1626 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1626) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1626))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1626)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1626 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1626) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1626))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1626)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1627 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1627) = g32p_row13_cosetRepresentatives 1627 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1627 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1627) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1627))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1627)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1627 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1627) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1627))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1627)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1628 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1628) = g32p_row13_cosetRepresentatives 1628 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1628 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1628) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1628))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1628)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1628 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1628) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1628))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1628)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1629 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1629) = g32p_row13_cosetRepresentatives 1629 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1629 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1629) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1629))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1629)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1629 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1629) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1629))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1629)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1630 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1630) = g32p_row13_cosetRepresentatives 1630 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1630 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1630) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1630))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1630)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1630 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1630) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1630))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1630)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1631 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1631) = g32p_row13_cosetRepresentatives 1631 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1631 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1631) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1631))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1631)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1631 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1631) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1631))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1631)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0101 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 101 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 101 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1616
  · exact g32p_row13_cosetWord_1617
  · exact g32p_row13_cosetWord_1618
  · exact g32p_row13_cosetWord_1619
  · exact g32p_row13_cosetWord_1620
  · exact g32p_row13_cosetWord_1621
  · exact g32p_row13_cosetWord_1622
  · exact g32p_row13_cosetWord_1623
  · exact g32p_row13_cosetWord_1624
  · exact g32p_row13_cosetWord_1625
  · exact g32p_row13_cosetWord_1626
  · exact g32p_row13_cosetWord_1627
  · exact g32p_row13_cosetWord_1628
  · exact g32p_row13_cosetWord_1629
  · exact g32p_row13_cosetWord_1630
  · exact g32p_row13_cosetWord_1631

theorem g32p_row13_cosetGeneratorBlock_0101 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 101 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 101 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 101 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1616 s
  · exact g32p_row13_cosetGeneratorStep_1617 s
  · exact g32p_row13_cosetGeneratorStep_1618 s
  · exact g32p_row13_cosetGeneratorStep_1619 s
  · exact g32p_row13_cosetGeneratorStep_1620 s
  · exact g32p_row13_cosetGeneratorStep_1621 s
  · exact g32p_row13_cosetGeneratorStep_1622 s
  · exact g32p_row13_cosetGeneratorStep_1623 s
  · exact g32p_row13_cosetGeneratorStep_1624 s
  · exact g32p_row13_cosetGeneratorStep_1625 s
  · exact g32p_row13_cosetGeneratorStep_1626 s
  · exact g32p_row13_cosetGeneratorStep_1627 s
  · exact g32p_row13_cosetGeneratorStep_1628 s
  · exact g32p_row13_cosetGeneratorStep_1629 s
  · exact g32p_row13_cosetGeneratorStep_1630 s
  · exact g32p_row13_cosetGeneratorStep_1631 s

theorem g32p_row13_cosetBranchBlock_0101 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 101 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 101 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 101 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1616 s
  · exact g32p_row13_cosetBranchStep_1617 s
  · exact g32p_row13_cosetBranchStep_1618 s
  · exact g32p_row13_cosetBranchStep_1619 s
  · exact g32p_row13_cosetBranchStep_1620 s
  · exact g32p_row13_cosetBranchStep_1621 s
  · exact g32p_row13_cosetBranchStep_1622 s
  · exact g32p_row13_cosetBranchStep_1623 s
  · exact g32p_row13_cosetBranchStep_1624 s
  · exact g32p_row13_cosetBranchStep_1625 s
  · exact g32p_row13_cosetBranchStep_1626 s
  · exact g32p_row13_cosetBranchStep_1627 s
  · exact g32p_row13_cosetBranchStep_1628 s
  · exact g32p_row13_cosetBranchStep_1629 s
  · exact g32p_row13_cosetBranchStep_1630 s
  · exact g32p_row13_cosetBranchStep_1631 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1632 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1632) = g32p_row13_cosetRepresentatives 1632 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1632 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1632) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1632))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1632)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1632 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1632) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1632))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1632)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1633 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1633) = g32p_row13_cosetRepresentatives 1633 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1633 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1633) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1633))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1633)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1633 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1633) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1633))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1633)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1634 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1634) = g32p_row13_cosetRepresentatives 1634 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1634 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1634) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1634))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1634)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1634 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1634) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1634))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1634)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1635 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1635) = g32p_row13_cosetRepresentatives 1635 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1635 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1635) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1635))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1635)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1635 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1635) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1635))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1635)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1636 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1636) = g32p_row13_cosetRepresentatives 1636 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1636 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1636) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1636))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1636)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1636 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1636) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1636))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1636)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1637 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1637) = g32p_row13_cosetRepresentatives 1637 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1637 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1637) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1637))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1637)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1637 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1637) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1637))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1637)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1638 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1638) = g32p_row13_cosetRepresentatives 1638 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1638 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1638) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1638))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1638)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1638 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1638) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1638))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1638)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1639 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1639) = g32p_row13_cosetRepresentatives 1639 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1639 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1639) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1639))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1639)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1639 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1639) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1639))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1639)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1640 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1640) = g32p_row13_cosetRepresentatives 1640 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1640 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1640) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1640))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1640)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1640 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1640) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1640))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1640)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1641 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1641) = g32p_row13_cosetRepresentatives 1641 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1641 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1641) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1641))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1641)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1641 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1641) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1641))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1641)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1642 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1642) = g32p_row13_cosetRepresentatives 1642 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1642 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1642) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1642))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1642)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1642 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1642) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1642))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1642)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1643 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1643) = g32p_row13_cosetRepresentatives 1643 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1643 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1643) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1643))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1643)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1643 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1643) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1643))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1643)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1644 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1644) = g32p_row13_cosetRepresentatives 1644 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1644 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1644) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1644))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1644)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1644 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1644) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1644))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1644)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1645 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1645) = g32p_row13_cosetRepresentatives 1645 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1645 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1645) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1645))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1645)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1645 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1645) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1645))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1645)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1646 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1646) = g32p_row13_cosetRepresentatives 1646 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1646 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1646) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1646))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1646)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1646 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1646) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1646))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1646)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1647 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1647) = g32p_row13_cosetRepresentatives 1647 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1647 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1647) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1647))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1647)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1647 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1647) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1647))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1647)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0102 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 102 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 102 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1632
  · exact g32p_row13_cosetWord_1633
  · exact g32p_row13_cosetWord_1634
  · exact g32p_row13_cosetWord_1635
  · exact g32p_row13_cosetWord_1636
  · exact g32p_row13_cosetWord_1637
  · exact g32p_row13_cosetWord_1638
  · exact g32p_row13_cosetWord_1639
  · exact g32p_row13_cosetWord_1640
  · exact g32p_row13_cosetWord_1641
  · exact g32p_row13_cosetWord_1642
  · exact g32p_row13_cosetWord_1643
  · exact g32p_row13_cosetWord_1644
  · exact g32p_row13_cosetWord_1645
  · exact g32p_row13_cosetWord_1646
  · exact g32p_row13_cosetWord_1647

theorem g32p_row13_cosetGeneratorBlock_0102 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 102 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 102 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 102 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1632 s
  · exact g32p_row13_cosetGeneratorStep_1633 s
  · exact g32p_row13_cosetGeneratorStep_1634 s
  · exact g32p_row13_cosetGeneratorStep_1635 s
  · exact g32p_row13_cosetGeneratorStep_1636 s
  · exact g32p_row13_cosetGeneratorStep_1637 s
  · exact g32p_row13_cosetGeneratorStep_1638 s
  · exact g32p_row13_cosetGeneratorStep_1639 s
  · exact g32p_row13_cosetGeneratorStep_1640 s
  · exact g32p_row13_cosetGeneratorStep_1641 s
  · exact g32p_row13_cosetGeneratorStep_1642 s
  · exact g32p_row13_cosetGeneratorStep_1643 s
  · exact g32p_row13_cosetGeneratorStep_1644 s
  · exact g32p_row13_cosetGeneratorStep_1645 s
  · exact g32p_row13_cosetGeneratorStep_1646 s
  · exact g32p_row13_cosetGeneratorStep_1647 s

theorem g32p_row13_cosetBranchBlock_0102 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 102 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 102 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 102 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1632 s
  · exact g32p_row13_cosetBranchStep_1633 s
  · exact g32p_row13_cosetBranchStep_1634 s
  · exact g32p_row13_cosetBranchStep_1635 s
  · exact g32p_row13_cosetBranchStep_1636 s
  · exact g32p_row13_cosetBranchStep_1637 s
  · exact g32p_row13_cosetBranchStep_1638 s
  · exact g32p_row13_cosetBranchStep_1639 s
  · exact g32p_row13_cosetBranchStep_1640 s
  · exact g32p_row13_cosetBranchStep_1641 s
  · exact g32p_row13_cosetBranchStep_1642 s
  · exact g32p_row13_cosetBranchStep_1643 s
  · exact g32p_row13_cosetBranchStep_1644 s
  · exact g32p_row13_cosetBranchStep_1645 s
  · exact g32p_row13_cosetBranchStep_1646 s
  · exact g32p_row13_cosetBranchStep_1647 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1648 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1648) = g32p_row13_cosetRepresentatives 1648 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1648 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1648) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1648))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1648)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1648 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1648) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1648))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1648)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1649 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1649) = g32p_row13_cosetRepresentatives 1649 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1649 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1649) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1649))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1649)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1649 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1649) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1649))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1649)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1650 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1650) = g32p_row13_cosetRepresentatives 1650 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1650 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1650) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1650))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1650)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1650 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1650) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1650))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1650)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1651 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1651) = g32p_row13_cosetRepresentatives 1651 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1651 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1651) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1651))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1651)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1651 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1651) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1651))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1651)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1652 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1652) = g32p_row13_cosetRepresentatives 1652 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1652 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1652) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1652))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1652)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1652 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1652) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1652))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1652)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1653 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1653) = g32p_row13_cosetRepresentatives 1653 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1653 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1653) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1653))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1653)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1653 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1653) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1653))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1653)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1654 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1654) = g32p_row13_cosetRepresentatives 1654 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1654 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1654) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1654))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1654)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1654 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1654) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1654))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1654)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1655 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1655) = g32p_row13_cosetRepresentatives 1655 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1655 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1655) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1655))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1655)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1655 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1655) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1655))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1655)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1656 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1656) = g32p_row13_cosetRepresentatives 1656 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1656 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1656) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1656))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1656)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1656 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1656) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1656))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1656)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1657 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1657) = g32p_row13_cosetRepresentatives 1657 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1657 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1657) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1657))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1657)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1657 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1657) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1657))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1657)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1658 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1658) = g32p_row13_cosetRepresentatives 1658 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1658 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1658) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1658))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1658)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1658 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1658) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1658))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1658)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1659 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1659) = g32p_row13_cosetRepresentatives 1659 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1659 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1659) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1659))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1659)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1659 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1659) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1659))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1659)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1660 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1660) = g32p_row13_cosetRepresentatives 1660 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1660 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1660) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1660))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1660)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1660 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1660) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1660))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1660)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1661 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1661) = g32p_row13_cosetRepresentatives 1661 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1661 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1661) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1661))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1661)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1661 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1661) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1661))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1661)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1662 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1662) = g32p_row13_cosetRepresentatives 1662 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1662 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1662) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1662))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1662)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1662 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1662) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1662))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1662)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1663 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1663) = g32p_row13_cosetRepresentatives 1663 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1663 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1663) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1663))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1663)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1663 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1663) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1663))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1663)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0103 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 103 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 103 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1648
  · exact g32p_row13_cosetWord_1649
  · exact g32p_row13_cosetWord_1650
  · exact g32p_row13_cosetWord_1651
  · exact g32p_row13_cosetWord_1652
  · exact g32p_row13_cosetWord_1653
  · exact g32p_row13_cosetWord_1654
  · exact g32p_row13_cosetWord_1655
  · exact g32p_row13_cosetWord_1656
  · exact g32p_row13_cosetWord_1657
  · exact g32p_row13_cosetWord_1658
  · exact g32p_row13_cosetWord_1659
  · exact g32p_row13_cosetWord_1660
  · exact g32p_row13_cosetWord_1661
  · exact g32p_row13_cosetWord_1662
  · exact g32p_row13_cosetWord_1663

theorem g32p_row13_cosetGeneratorBlock_0103 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 103 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 103 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 103 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1648 s
  · exact g32p_row13_cosetGeneratorStep_1649 s
  · exact g32p_row13_cosetGeneratorStep_1650 s
  · exact g32p_row13_cosetGeneratorStep_1651 s
  · exact g32p_row13_cosetGeneratorStep_1652 s
  · exact g32p_row13_cosetGeneratorStep_1653 s
  · exact g32p_row13_cosetGeneratorStep_1654 s
  · exact g32p_row13_cosetGeneratorStep_1655 s
  · exact g32p_row13_cosetGeneratorStep_1656 s
  · exact g32p_row13_cosetGeneratorStep_1657 s
  · exact g32p_row13_cosetGeneratorStep_1658 s
  · exact g32p_row13_cosetGeneratorStep_1659 s
  · exact g32p_row13_cosetGeneratorStep_1660 s
  · exact g32p_row13_cosetGeneratorStep_1661 s
  · exact g32p_row13_cosetGeneratorStep_1662 s
  · exact g32p_row13_cosetGeneratorStep_1663 s

theorem g32p_row13_cosetBranchBlock_0103 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 103 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 103 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 103 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1648 s
  · exact g32p_row13_cosetBranchStep_1649 s
  · exact g32p_row13_cosetBranchStep_1650 s
  · exact g32p_row13_cosetBranchStep_1651 s
  · exact g32p_row13_cosetBranchStep_1652 s
  · exact g32p_row13_cosetBranchStep_1653 s
  · exact g32p_row13_cosetBranchStep_1654 s
  · exact g32p_row13_cosetBranchStep_1655 s
  · exact g32p_row13_cosetBranchStep_1656 s
  · exact g32p_row13_cosetBranchStep_1657 s
  · exact g32p_row13_cosetBranchStep_1658 s
  · exact g32p_row13_cosetBranchStep_1659 s
  · exact g32p_row13_cosetBranchStep_1660 s
  · exact g32p_row13_cosetBranchStep_1661 s
  · exact g32p_row13_cosetBranchStep_1662 s
  · exact g32p_row13_cosetBranchStep_1663 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1664 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1664) = g32p_row13_cosetRepresentatives 1664 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1664 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1664) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1664))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1664)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1664 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1664) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1664))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1664)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1665 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1665) = g32p_row13_cosetRepresentatives 1665 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1665 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1665) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1665))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1665)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1665 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1665) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1665))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1665)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1666 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1666) = g32p_row13_cosetRepresentatives 1666 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1666 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1666) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1666))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1666)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1666 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1666) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1666))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1666)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1667 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1667) = g32p_row13_cosetRepresentatives 1667 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1667 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1667) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1667))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1667)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1667 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1667) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1667))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1667)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1668 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1668) = g32p_row13_cosetRepresentatives 1668 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1668 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1668) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1668))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1668)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1668 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1668) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1668))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1668)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1669 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1669) = g32p_row13_cosetRepresentatives 1669 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1669 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1669) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1669))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1669)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1669 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1669) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1669))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1669)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1670 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1670) = g32p_row13_cosetRepresentatives 1670 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1670 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1670) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1670))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1670)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1670 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1670) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1670))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1670)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1671 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1671) = g32p_row13_cosetRepresentatives 1671 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1671 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1671) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1671))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1671)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1671 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1671) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1671))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1671)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1672 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1672) = g32p_row13_cosetRepresentatives 1672 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1672 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1672) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1672))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1672)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1672 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1672) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1672))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1672)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1673 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1673) = g32p_row13_cosetRepresentatives 1673 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1673 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1673) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1673))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1673)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1673 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1673) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1673))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1673)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1674 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1674) = g32p_row13_cosetRepresentatives 1674 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1674 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1674) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1674))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1674)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1674 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1674) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1674))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1674)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1675 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1675) = g32p_row13_cosetRepresentatives 1675 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1675 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1675) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1675))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1675)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1675 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1675) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1675))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1675)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1676 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1676) = g32p_row13_cosetRepresentatives 1676 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1676 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1676) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1676))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1676)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1676 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1676) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1676))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1676)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1677 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1677) = g32p_row13_cosetRepresentatives 1677 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1677 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1677) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1677))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1677)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1677 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1677) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1677))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1677)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1678 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1678) = g32p_row13_cosetRepresentatives 1678 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1678 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1678) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1678))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1678)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1678 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1678) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1678))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1678)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1679 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1679) = g32p_row13_cosetRepresentatives 1679 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1679 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1679) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1679))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1679)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1679 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1679) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1679))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1679)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0104 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 104 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 104 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1664
  · exact g32p_row13_cosetWord_1665
  · exact g32p_row13_cosetWord_1666
  · exact g32p_row13_cosetWord_1667
  · exact g32p_row13_cosetWord_1668
  · exact g32p_row13_cosetWord_1669
  · exact g32p_row13_cosetWord_1670
  · exact g32p_row13_cosetWord_1671
  · exact g32p_row13_cosetWord_1672
  · exact g32p_row13_cosetWord_1673
  · exact g32p_row13_cosetWord_1674
  · exact g32p_row13_cosetWord_1675
  · exact g32p_row13_cosetWord_1676
  · exact g32p_row13_cosetWord_1677
  · exact g32p_row13_cosetWord_1678
  · exact g32p_row13_cosetWord_1679

theorem g32p_row13_cosetGeneratorBlock_0104 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 104 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 104 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 104 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1664 s
  · exact g32p_row13_cosetGeneratorStep_1665 s
  · exact g32p_row13_cosetGeneratorStep_1666 s
  · exact g32p_row13_cosetGeneratorStep_1667 s
  · exact g32p_row13_cosetGeneratorStep_1668 s
  · exact g32p_row13_cosetGeneratorStep_1669 s
  · exact g32p_row13_cosetGeneratorStep_1670 s
  · exact g32p_row13_cosetGeneratorStep_1671 s
  · exact g32p_row13_cosetGeneratorStep_1672 s
  · exact g32p_row13_cosetGeneratorStep_1673 s
  · exact g32p_row13_cosetGeneratorStep_1674 s
  · exact g32p_row13_cosetGeneratorStep_1675 s
  · exact g32p_row13_cosetGeneratorStep_1676 s
  · exact g32p_row13_cosetGeneratorStep_1677 s
  · exact g32p_row13_cosetGeneratorStep_1678 s
  · exact g32p_row13_cosetGeneratorStep_1679 s

theorem g32p_row13_cosetBranchBlock_0104 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 104 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 104 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 104 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1664 s
  · exact g32p_row13_cosetBranchStep_1665 s
  · exact g32p_row13_cosetBranchStep_1666 s
  · exact g32p_row13_cosetBranchStep_1667 s
  · exact g32p_row13_cosetBranchStep_1668 s
  · exact g32p_row13_cosetBranchStep_1669 s
  · exact g32p_row13_cosetBranchStep_1670 s
  · exact g32p_row13_cosetBranchStep_1671 s
  · exact g32p_row13_cosetBranchStep_1672 s
  · exact g32p_row13_cosetBranchStep_1673 s
  · exact g32p_row13_cosetBranchStep_1674 s
  · exact g32p_row13_cosetBranchStep_1675 s
  · exact g32p_row13_cosetBranchStep_1676 s
  · exact g32p_row13_cosetBranchStep_1677 s
  · exact g32p_row13_cosetBranchStep_1678 s
  · exact g32p_row13_cosetBranchStep_1679 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1680 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1680) = g32p_row13_cosetRepresentatives 1680 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1680 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1680) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1680))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1680)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1680 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1680) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1680))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1680)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1681 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1681) = g32p_row13_cosetRepresentatives 1681 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1681 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1681) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1681))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1681)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1681 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1681) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1681))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1681)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1682 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1682) = g32p_row13_cosetRepresentatives 1682 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1682 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1682) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1682))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1682)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1682 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1682) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1682))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1682)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1683 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1683) = g32p_row13_cosetRepresentatives 1683 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1683 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1683) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1683))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1683)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1683 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1683) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1683))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1683)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1684 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1684) = g32p_row13_cosetRepresentatives 1684 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1684 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1684) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1684))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1684)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1684 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1684) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1684))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1684)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1685 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1685) = g32p_row13_cosetRepresentatives 1685 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1685 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1685) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1685))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1685)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1685 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1685) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1685))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1685)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1686 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1686) = g32p_row13_cosetRepresentatives 1686 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1686 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1686) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1686))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1686)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1686 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1686) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1686))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1686)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1687 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1687) = g32p_row13_cosetRepresentatives 1687 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1687 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1687) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1687))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1687)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1687 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1687) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1687))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1687)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1688 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1688) = g32p_row13_cosetRepresentatives 1688 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1688 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1688) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1688))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1688)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1688 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1688) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1688))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1688)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1689 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1689) = g32p_row13_cosetRepresentatives 1689 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1689 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1689) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1689))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1689)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1689 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1689) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1689))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1689)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1690 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1690) = g32p_row13_cosetRepresentatives 1690 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1690 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1690) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1690))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1690)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1690 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1690) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1690))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1690)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1691 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1691) = g32p_row13_cosetRepresentatives 1691 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1691 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1691) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1691))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1691)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1691 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1691) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1691))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1691)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1692 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1692) = g32p_row13_cosetRepresentatives 1692 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1692 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1692) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1692))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1692)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1692 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1692) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1692))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1692)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1693 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1693) = g32p_row13_cosetRepresentatives 1693 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1693 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1693) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1693))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1693)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1693 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1693) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1693))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1693)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1694 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1694) = g32p_row13_cosetRepresentatives 1694 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1694 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1694) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1694))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1694)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1694 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1694) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1694))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1694)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1695 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1695) = g32p_row13_cosetRepresentatives 1695 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1695 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1695) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1695))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1695)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1695 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1695) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1695))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1695)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0105 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 105 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 105 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1680
  · exact g32p_row13_cosetWord_1681
  · exact g32p_row13_cosetWord_1682
  · exact g32p_row13_cosetWord_1683
  · exact g32p_row13_cosetWord_1684
  · exact g32p_row13_cosetWord_1685
  · exact g32p_row13_cosetWord_1686
  · exact g32p_row13_cosetWord_1687
  · exact g32p_row13_cosetWord_1688
  · exact g32p_row13_cosetWord_1689
  · exact g32p_row13_cosetWord_1690
  · exact g32p_row13_cosetWord_1691
  · exact g32p_row13_cosetWord_1692
  · exact g32p_row13_cosetWord_1693
  · exact g32p_row13_cosetWord_1694
  · exact g32p_row13_cosetWord_1695

theorem g32p_row13_cosetGeneratorBlock_0105 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 105 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 105 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 105 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1680 s
  · exact g32p_row13_cosetGeneratorStep_1681 s
  · exact g32p_row13_cosetGeneratorStep_1682 s
  · exact g32p_row13_cosetGeneratorStep_1683 s
  · exact g32p_row13_cosetGeneratorStep_1684 s
  · exact g32p_row13_cosetGeneratorStep_1685 s
  · exact g32p_row13_cosetGeneratorStep_1686 s
  · exact g32p_row13_cosetGeneratorStep_1687 s
  · exact g32p_row13_cosetGeneratorStep_1688 s
  · exact g32p_row13_cosetGeneratorStep_1689 s
  · exact g32p_row13_cosetGeneratorStep_1690 s
  · exact g32p_row13_cosetGeneratorStep_1691 s
  · exact g32p_row13_cosetGeneratorStep_1692 s
  · exact g32p_row13_cosetGeneratorStep_1693 s
  · exact g32p_row13_cosetGeneratorStep_1694 s
  · exact g32p_row13_cosetGeneratorStep_1695 s

theorem g32p_row13_cosetBranchBlock_0105 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 105 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 105 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 105 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1680 s
  · exact g32p_row13_cosetBranchStep_1681 s
  · exact g32p_row13_cosetBranchStep_1682 s
  · exact g32p_row13_cosetBranchStep_1683 s
  · exact g32p_row13_cosetBranchStep_1684 s
  · exact g32p_row13_cosetBranchStep_1685 s
  · exact g32p_row13_cosetBranchStep_1686 s
  · exact g32p_row13_cosetBranchStep_1687 s
  · exact g32p_row13_cosetBranchStep_1688 s
  · exact g32p_row13_cosetBranchStep_1689 s
  · exact g32p_row13_cosetBranchStep_1690 s
  · exact g32p_row13_cosetBranchStep_1691 s
  · exact g32p_row13_cosetBranchStep_1692 s
  · exact g32p_row13_cosetBranchStep_1693 s
  · exact g32p_row13_cosetBranchStep_1694 s
  · exact g32p_row13_cosetBranchStep_1695 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1696 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1696) = g32p_row13_cosetRepresentatives 1696 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1696 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1696) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1696))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1696)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1696 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1696) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1696))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1696)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1697 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1697) = g32p_row13_cosetRepresentatives 1697 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1697 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1697) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1697))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1697)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1697 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1697) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1697))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1697)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1698 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1698) = g32p_row13_cosetRepresentatives 1698 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1698 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1698) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1698))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1698)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1698 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1698) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1698))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1698)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1699 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1699) = g32p_row13_cosetRepresentatives 1699 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1699 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1699) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1699))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1699)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1699 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1699) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1699))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1699)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1700 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1700) = g32p_row13_cosetRepresentatives 1700 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1700 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1700) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1700))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1700)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1700 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1700) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1700))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1700)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1701 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1701) = g32p_row13_cosetRepresentatives 1701 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1701 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1701) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1701))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1701)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1701 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1701) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1701))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1701)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1702 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1702) = g32p_row13_cosetRepresentatives 1702 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1702 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1702) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1702))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1702)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1702 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1702) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1702))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1702)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1703 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1703) = g32p_row13_cosetRepresentatives 1703 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1703 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1703) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1703))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1703)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1703 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1703) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1703))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1703)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1704 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1704) = g32p_row13_cosetRepresentatives 1704 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1704 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1704) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1704))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1704)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1704 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1704) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1704))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1704)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1705 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1705) = g32p_row13_cosetRepresentatives 1705 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1705 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1705) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1705))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1705)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1705 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1705) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1705))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1705)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1706 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1706) = g32p_row13_cosetRepresentatives 1706 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1706 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1706) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1706))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1706)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1706 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1706) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1706))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1706)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1707 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1707) = g32p_row13_cosetRepresentatives 1707 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1707 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1707) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1707))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1707)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1707 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1707) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1707))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1707)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1708 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1708) = g32p_row13_cosetRepresentatives 1708 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1708 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1708) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1708))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1708)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1708 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1708) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1708))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1708)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1709 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1709) = g32p_row13_cosetRepresentatives 1709 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1709 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1709) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1709))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1709)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1709 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1709) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1709))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1709)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1710 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1710) = g32p_row13_cosetRepresentatives 1710 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1710 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1710) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1710))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1710)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1710 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1710) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1710))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1710)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1711 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1711) = g32p_row13_cosetRepresentatives 1711 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1711 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1711) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1711))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1711)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1711 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1711) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1711))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1711)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0106 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 106 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 106 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1696
  · exact g32p_row13_cosetWord_1697
  · exact g32p_row13_cosetWord_1698
  · exact g32p_row13_cosetWord_1699
  · exact g32p_row13_cosetWord_1700
  · exact g32p_row13_cosetWord_1701
  · exact g32p_row13_cosetWord_1702
  · exact g32p_row13_cosetWord_1703
  · exact g32p_row13_cosetWord_1704
  · exact g32p_row13_cosetWord_1705
  · exact g32p_row13_cosetWord_1706
  · exact g32p_row13_cosetWord_1707
  · exact g32p_row13_cosetWord_1708
  · exact g32p_row13_cosetWord_1709
  · exact g32p_row13_cosetWord_1710
  · exact g32p_row13_cosetWord_1711

theorem g32p_row13_cosetGeneratorBlock_0106 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 106 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 106 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 106 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1696 s
  · exact g32p_row13_cosetGeneratorStep_1697 s
  · exact g32p_row13_cosetGeneratorStep_1698 s
  · exact g32p_row13_cosetGeneratorStep_1699 s
  · exact g32p_row13_cosetGeneratorStep_1700 s
  · exact g32p_row13_cosetGeneratorStep_1701 s
  · exact g32p_row13_cosetGeneratorStep_1702 s
  · exact g32p_row13_cosetGeneratorStep_1703 s
  · exact g32p_row13_cosetGeneratorStep_1704 s
  · exact g32p_row13_cosetGeneratorStep_1705 s
  · exact g32p_row13_cosetGeneratorStep_1706 s
  · exact g32p_row13_cosetGeneratorStep_1707 s
  · exact g32p_row13_cosetGeneratorStep_1708 s
  · exact g32p_row13_cosetGeneratorStep_1709 s
  · exact g32p_row13_cosetGeneratorStep_1710 s
  · exact g32p_row13_cosetGeneratorStep_1711 s

theorem g32p_row13_cosetBranchBlock_0106 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 106 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 106 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 106 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1696 s
  · exact g32p_row13_cosetBranchStep_1697 s
  · exact g32p_row13_cosetBranchStep_1698 s
  · exact g32p_row13_cosetBranchStep_1699 s
  · exact g32p_row13_cosetBranchStep_1700 s
  · exact g32p_row13_cosetBranchStep_1701 s
  · exact g32p_row13_cosetBranchStep_1702 s
  · exact g32p_row13_cosetBranchStep_1703 s
  · exact g32p_row13_cosetBranchStep_1704 s
  · exact g32p_row13_cosetBranchStep_1705 s
  · exact g32p_row13_cosetBranchStep_1706 s
  · exact g32p_row13_cosetBranchStep_1707 s
  · exact g32p_row13_cosetBranchStep_1708 s
  · exact g32p_row13_cosetBranchStep_1709 s
  · exact g32p_row13_cosetBranchStep_1710 s
  · exact g32p_row13_cosetBranchStep_1711 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1712 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1712) = g32p_row13_cosetRepresentatives 1712 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1712 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1712) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1712))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1712)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1712 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1712) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1712))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1712)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1713 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1713) = g32p_row13_cosetRepresentatives 1713 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1713 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1713) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1713))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1713)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1713 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1713) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1713))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1713)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1714 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1714) = g32p_row13_cosetRepresentatives 1714 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1714 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1714) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1714))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1714)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1714 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1714) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1714))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1714)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1715 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1715) = g32p_row13_cosetRepresentatives 1715 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1715 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1715) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1715))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1715)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1715 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1715) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1715))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1715)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1716 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1716) = g32p_row13_cosetRepresentatives 1716 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1716 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1716) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1716))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1716)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1716 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1716) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1716))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1716)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1717 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1717) = g32p_row13_cosetRepresentatives 1717 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1717 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1717) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1717))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1717)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1717 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1717) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1717))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1717)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1718 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1718) = g32p_row13_cosetRepresentatives 1718 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1718 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1718) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1718))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1718)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1718 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1718) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1718))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1718)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1719 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1719) = g32p_row13_cosetRepresentatives 1719 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1719 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1719) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1719))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1719)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1719 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1719) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1719))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1719)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1720 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1720) = g32p_row13_cosetRepresentatives 1720 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1720 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1720) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1720))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1720)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1720 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1720) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1720))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1720)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1721 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1721) = g32p_row13_cosetRepresentatives 1721 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1721 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1721) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1721))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1721)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1721 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1721) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1721))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1721)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1722 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1722) = g32p_row13_cosetRepresentatives 1722 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1722 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1722) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1722))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1722)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1722 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1722) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1722))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1722)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1723 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1723) = g32p_row13_cosetRepresentatives 1723 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1723 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1723) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1723))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1723)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1723 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1723) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1723))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1723)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1724 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1724) = g32p_row13_cosetRepresentatives 1724 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1724 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1724) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1724))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1724)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1724 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1724) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1724))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1724)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1725 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1725) = g32p_row13_cosetRepresentatives 1725 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1725 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1725) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1725))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1725)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1725 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1725) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1725))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1725)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1726 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1726) = g32p_row13_cosetRepresentatives 1726 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1726 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1726) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1726))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1726)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1726 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1726) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1726))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1726)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1727 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1727) = g32p_row13_cosetRepresentatives 1727 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1727 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1727) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1727))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1727)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1727 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1727) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1727))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1727)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0107 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 107 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 107 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1712
  · exact g32p_row13_cosetWord_1713
  · exact g32p_row13_cosetWord_1714
  · exact g32p_row13_cosetWord_1715
  · exact g32p_row13_cosetWord_1716
  · exact g32p_row13_cosetWord_1717
  · exact g32p_row13_cosetWord_1718
  · exact g32p_row13_cosetWord_1719
  · exact g32p_row13_cosetWord_1720
  · exact g32p_row13_cosetWord_1721
  · exact g32p_row13_cosetWord_1722
  · exact g32p_row13_cosetWord_1723
  · exact g32p_row13_cosetWord_1724
  · exact g32p_row13_cosetWord_1725
  · exact g32p_row13_cosetWord_1726
  · exact g32p_row13_cosetWord_1727

theorem g32p_row13_cosetGeneratorBlock_0107 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 107 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 107 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 107 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1712 s
  · exact g32p_row13_cosetGeneratorStep_1713 s
  · exact g32p_row13_cosetGeneratorStep_1714 s
  · exact g32p_row13_cosetGeneratorStep_1715 s
  · exact g32p_row13_cosetGeneratorStep_1716 s
  · exact g32p_row13_cosetGeneratorStep_1717 s
  · exact g32p_row13_cosetGeneratorStep_1718 s
  · exact g32p_row13_cosetGeneratorStep_1719 s
  · exact g32p_row13_cosetGeneratorStep_1720 s
  · exact g32p_row13_cosetGeneratorStep_1721 s
  · exact g32p_row13_cosetGeneratorStep_1722 s
  · exact g32p_row13_cosetGeneratorStep_1723 s
  · exact g32p_row13_cosetGeneratorStep_1724 s
  · exact g32p_row13_cosetGeneratorStep_1725 s
  · exact g32p_row13_cosetGeneratorStep_1726 s
  · exact g32p_row13_cosetGeneratorStep_1727 s

theorem g32p_row13_cosetBranchBlock_0107 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 107 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 107 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 107 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1712 s
  · exact g32p_row13_cosetBranchStep_1713 s
  · exact g32p_row13_cosetBranchStep_1714 s
  · exact g32p_row13_cosetBranchStep_1715 s
  · exact g32p_row13_cosetBranchStep_1716 s
  · exact g32p_row13_cosetBranchStep_1717 s
  · exact g32p_row13_cosetBranchStep_1718 s
  · exact g32p_row13_cosetBranchStep_1719 s
  · exact g32p_row13_cosetBranchStep_1720 s
  · exact g32p_row13_cosetBranchStep_1721 s
  · exact g32p_row13_cosetBranchStep_1722 s
  · exact g32p_row13_cosetBranchStep_1723 s
  · exact g32p_row13_cosetBranchStep_1724 s
  · exact g32p_row13_cosetBranchStep_1725 s
  · exact g32p_row13_cosetBranchStep_1726 s
  · exact g32p_row13_cosetBranchStep_1727 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1728 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1728) = g32p_row13_cosetRepresentatives 1728 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1728 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1728) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1728))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1728)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1728 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1728) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1728))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1728)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1729 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1729) = g32p_row13_cosetRepresentatives 1729 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1729 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1729) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1729))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1729)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1729 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1729) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1729))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1729)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1730 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1730) = g32p_row13_cosetRepresentatives 1730 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1730 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1730) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1730))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1730)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1730 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1730) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1730))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1730)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1731 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1731) = g32p_row13_cosetRepresentatives 1731 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1731 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1731) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1731))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1731)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1731 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1731) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1731))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1731)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1732 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1732) = g32p_row13_cosetRepresentatives 1732 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1732 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1732) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1732))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1732)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1732 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1732) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1732))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1732)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1733 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1733) = g32p_row13_cosetRepresentatives 1733 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1733 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1733) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1733))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1733)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1733 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1733) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1733))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1733)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1734 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1734) = g32p_row13_cosetRepresentatives 1734 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1734 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1734) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1734))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1734)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1734 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1734) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1734))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1734)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1735 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1735) = g32p_row13_cosetRepresentatives 1735 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1735 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1735) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1735))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1735)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1735 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1735) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1735))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1735)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1736 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1736) = g32p_row13_cosetRepresentatives 1736 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1736 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1736) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1736))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1736)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1736 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1736) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1736))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1736)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1737 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1737) = g32p_row13_cosetRepresentatives 1737 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1737 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1737) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1737))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1737)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1737 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1737) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1737))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1737)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1738 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1738) = g32p_row13_cosetRepresentatives 1738 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1738 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1738) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1738))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1738)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1738 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1738) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1738))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1738)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1739 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1739) = g32p_row13_cosetRepresentatives 1739 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1739 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1739) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1739))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1739)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1739 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1739) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1739))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1739)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1740 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1740) = g32p_row13_cosetRepresentatives 1740 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1740 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1740) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1740))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1740)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1740 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1740) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1740))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1740)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1741 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1741) = g32p_row13_cosetRepresentatives 1741 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1741 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1741) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1741))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1741)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1741 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1741) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1741))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1741)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1742 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1742) = g32p_row13_cosetRepresentatives 1742 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1742 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1742) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1742))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1742)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1742 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1742) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1742))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1742)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1743 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1743) = g32p_row13_cosetRepresentatives 1743 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1743 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1743) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1743))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1743)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1743 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1743) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1743))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1743)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0108 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 108 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 108 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1728
  · exact g32p_row13_cosetWord_1729
  · exact g32p_row13_cosetWord_1730
  · exact g32p_row13_cosetWord_1731
  · exact g32p_row13_cosetWord_1732
  · exact g32p_row13_cosetWord_1733
  · exact g32p_row13_cosetWord_1734
  · exact g32p_row13_cosetWord_1735
  · exact g32p_row13_cosetWord_1736
  · exact g32p_row13_cosetWord_1737
  · exact g32p_row13_cosetWord_1738
  · exact g32p_row13_cosetWord_1739
  · exact g32p_row13_cosetWord_1740
  · exact g32p_row13_cosetWord_1741
  · exact g32p_row13_cosetWord_1742
  · exact g32p_row13_cosetWord_1743

theorem g32p_row13_cosetGeneratorBlock_0108 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 108 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 108 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 108 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1728 s
  · exact g32p_row13_cosetGeneratorStep_1729 s
  · exact g32p_row13_cosetGeneratorStep_1730 s
  · exact g32p_row13_cosetGeneratorStep_1731 s
  · exact g32p_row13_cosetGeneratorStep_1732 s
  · exact g32p_row13_cosetGeneratorStep_1733 s
  · exact g32p_row13_cosetGeneratorStep_1734 s
  · exact g32p_row13_cosetGeneratorStep_1735 s
  · exact g32p_row13_cosetGeneratorStep_1736 s
  · exact g32p_row13_cosetGeneratorStep_1737 s
  · exact g32p_row13_cosetGeneratorStep_1738 s
  · exact g32p_row13_cosetGeneratorStep_1739 s
  · exact g32p_row13_cosetGeneratorStep_1740 s
  · exact g32p_row13_cosetGeneratorStep_1741 s
  · exact g32p_row13_cosetGeneratorStep_1742 s
  · exact g32p_row13_cosetGeneratorStep_1743 s

theorem g32p_row13_cosetBranchBlock_0108 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 108 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 108 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 108 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1728 s
  · exact g32p_row13_cosetBranchStep_1729 s
  · exact g32p_row13_cosetBranchStep_1730 s
  · exact g32p_row13_cosetBranchStep_1731 s
  · exact g32p_row13_cosetBranchStep_1732 s
  · exact g32p_row13_cosetBranchStep_1733 s
  · exact g32p_row13_cosetBranchStep_1734 s
  · exact g32p_row13_cosetBranchStep_1735 s
  · exact g32p_row13_cosetBranchStep_1736 s
  · exact g32p_row13_cosetBranchStep_1737 s
  · exact g32p_row13_cosetBranchStep_1738 s
  · exact g32p_row13_cosetBranchStep_1739 s
  · exact g32p_row13_cosetBranchStep_1740 s
  · exact g32p_row13_cosetBranchStep_1741 s
  · exact g32p_row13_cosetBranchStep_1742 s
  · exact g32p_row13_cosetBranchStep_1743 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1744 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1744) = g32p_row13_cosetRepresentatives 1744 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1744 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1744) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1744))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1744)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1744 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1744) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1744))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1744)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1745 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1745) = g32p_row13_cosetRepresentatives 1745 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1745 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1745) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1745))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1745)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1745 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1745) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1745))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1745)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1746 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1746) = g32p_row13_cosetRepresentatives 1746 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1746 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1746) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1746))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1746)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1746 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1746) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1746))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1746)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1747 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1747) = g32p_row13_cosetRepresentatives 1747 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1747 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1747) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1747))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1747)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1747 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1747) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1747))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1747)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1748 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1748) = g32p_row13_cosetRepresentatives 1748 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1748 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1748) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1748))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1748)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1748 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1748) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1748))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1748)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1749 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1749) = g32p_row13_cosetRepresentatives 1749 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1749 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1749) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1749))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1749)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1749 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1749) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1749))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1749)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1750 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1750) = g32p_row13_cosetRepresentatives 1750 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1750 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1750) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1750))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1750)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1750 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1750) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1750))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1750)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1751 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1751) = g32p_row13_cosetRepresentatives 1751 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1751 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1751) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1751))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1751)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1751 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1751) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1751))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1751)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1752 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1752) = g32p_row13_cosetRepresentatives 1752 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1752 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1752) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1752))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1752)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1752 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1752) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1752))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1752)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1753 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1753) = g32p_row13_cosetRepresentatives 1753 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1753 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1753) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1753))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1753)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1753 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1753) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1753))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1753)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1754 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1754) = g32p_row13_cosetRepresentatives 1754 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1754 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1754) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1754))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1754)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1754 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1754) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1754))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1754)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1755 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1755) = g32p_row13_cosetRepresentatives 1755 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1755 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1755) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1755))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1755)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1755 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1755) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1755))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1755)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1756 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1756) = g32p_row13_cosetRepresentatives 1756 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1756 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1756) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1756))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1756)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1756 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1756) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1756))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1756)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1757 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1757) = g32p_row13_cosetRepresentatives 1757 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1757 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1757) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1757))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1757)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1757 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1757) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1757))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1757)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1758 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1758) = g32p_row13_cosetRepresentatives 1758 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1758 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1758) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1758))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1758)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1758 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1758) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1758))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1758)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1759 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1759) = g32p_row13_cosetRepresentatives 1759 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1759 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1759) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1759))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1759)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1759 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1759) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1759))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1759)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0109 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 109 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 109 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1744
  · exact g32p_row13_cosetWord_1745
  · exact g32p_row13_cosetWord_1746
  · exact g32p_row13_cosetWord_1747
  · exact g32p_row13_cosetWord_1748
  · exact g32p_row13_cosetWord_1749
  · exact g32p_row13_cosetWord_1750
  · exact g32p_row13_cosetWord_1751
  · exact g32p_row13_cosetWord_1752
  · exact g32p_row13_cosetWord_1753
  · exact g32p_row13_cosetWord_1754
  · exact g32p_row13_cosetWord_1755
  · exact g32p_row13_cosetWord_1756
  · exact g32p_row13_cosetWord_1757
  · exact g32p_row13_cosetWord_1758
  · exact g32p_row13_cosetWord_1759

theorem g32p_row13_cosetGeneratorBlock_0109 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 109 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 109 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 109 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1744 s
  · exact g32p_row13_cosetGeneratorStep_1745 s
  · exact g32p_row13_cosetGeneratorStep_1746 s
  · exact g32p_row13_cosetGeneratorStep_1747 s
  · exact g32p_row13_cosetGeneratorStep_1748 s
  · exact g32p_row13_cosetGeneratorStep_1749 s
  · exact g32p_row13_cosetGeneratorStep_1750 s
  · exact g32p_row13_cosetGeneratorStep_1751 s
  · exact g32p_row13_cosetGeneratorStep_1752 s
  · exact g32p_row13_cosetGeneratorStep_1753 s
  · exact g32p_row13_cosetGeneratorStep_1754 s
  · exact g32p_row13_cosetGeneratorStep_1755 s
  · exact g32p_row13_cosetGeneratorStep_1756 s
  · exact g32p_row13_cosetGeneratorStep_1757 s
  · exact g32p_row13_cosetGeneratorStep_1758 s
  · exact g32p_row13_cosetGeneratorStep_1759 s

theorem g32p_row13_cosetBranchBlock_0109 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 109 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 109 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 109 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1744 s
  · exact g32p_row13_cosetBranchStep_1745 s
  · exact g32p_row13_cosetBranchStep_1746 s
  · exact g32p_row13_cosetBranchStep_1747 s
  · exact g32p_row13_cosetBranchStep_1748 s
  · exact g32p_row13_cosetBranchStep_1749 s
  · exact g32p_row13_cosetBranchStep_1750 s
  · exact g32p_row13_cosetBranchStep_1751 s
  · exact g32p_row13_cosetBranchStep_1752 s
  · exact g32p_row13_cosetBranchStep_1753 s
  · exact g32p_row13_cosetBranchStep_1754 s
  · exact g32p_row13_cosetBranchStep_1755 s
  · exact g32p_row13_cosetBranchStep_1756 s
  · exact g32p_row13_cosetBranchStep_1757 s
  · exact g32p_row13_cosetBranchStep_1758 s
  · exact g32p_row13_cosetBranchStep_1759 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1760 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1760) = g32p_row13_cosetRepresentatives 1760 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1760 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1760) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1760))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1760)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1760 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1760) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1760))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1760)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1761 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1761) = g32p_row13_cosetRepresentatives 1761 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1761 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1761) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1761))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1761)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1761 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1761) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1761))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1761)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1762 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1762) = g32p_row13_cosetRepresentatives 1762 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1762 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1762) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1762))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1762)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1762 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1762) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1762))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1762)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1763 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1763) = g32p_row13_cosetRepresentatives 1763 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1763 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1763) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1763))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1763)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1763 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1763) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1763))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1763)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1764 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1764) = g32p_row13_cosetRepresentatives 1764 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1764 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1764) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1764))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1764)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1764 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1764) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1764))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1764)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1765 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1765) = g32p_row13_cosetRepresentatives 1765 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1765 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1765) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1765))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1765)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1765 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1765) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1765))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1765)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1766 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1766) = g32p_row13_cosetRepresentatives 1766 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1766 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1766) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1766))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1766)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1766 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1766) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1766))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1766)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1767 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1767) = g32p_row13_cosetRepresentatives 1767 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1767 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1767) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1767))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1767)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1767 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1767) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1767))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1767)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1768 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1768) = g32p_row13_cosetRepresentatives 1768 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1768 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1768) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1768))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1768)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1768 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1768) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1768))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1768)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1769 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1769) = g32p_row13_cosetRepresentatives 1769 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1769 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1769) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1769))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1769)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1769 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1769) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1769))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1769)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1770 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1770) = g32p_row13_cosetRepresentatives 1770 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1770 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1770) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1770))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1770)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1770 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1770) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1770))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1770)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1771 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1771) = g32p_row13_cosetRepresentatives 1771 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1771 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1771) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1771))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1771)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1771 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1771) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1771))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1771)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1772 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1772) = g32p_row13_cosetRepresentatives 1772 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1772 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1772) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1772))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1772)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1772 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1772) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1772))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1772)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1773 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1773) = g32p_row13_cosetRepresentatives 1773 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1773 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1773) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1773))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1773)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1773 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1773) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1773))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1773)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1774 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1774) = g32p_row13_cosetRepresentatives 1774 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1774 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1774) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1774))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1774)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1774 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1774) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1774))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1774)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1775 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1775) = g32p_row13_cosetRepresentatives 1775 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1775 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1775) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1775))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1775)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1775 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1775) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1775))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1775)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0110 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 110 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 110 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1760
  · exact g32p_row13_cosetWord_1761
  · exact g32p_row13_cosetWord_1762
  · exact g32p_row13_cosetWord_1763
  · exact g32p_row13_cosetWord_1764
  · exact g32p_row13_cosetWord_1765
  · exact g32p_row13_cosetWord_1766
  · exact g32p_row13_cosetWord_1767
  · exact g32p_row13_cosetWord_1768
  · exact g32p_row13_cosetWord_1769
  · exact g32p_row13_cosetWord_1770
  · exact g32p_row13_cosetWord_1771
  · exact g32p_row13_cosetWord_1772
  · exact g32p_row13_cosetWord_1773
  · exact g32p_row13_cosetWord_1774
  · exact g32p_row13_cosetWord_1775

theorem g32p_row13_cosetGeneratorBlock_0110 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 110 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 110 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 110 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1760 s
  · exact g32p_row13_cosetGeneratorStep_1761 s
  · exact g32p_row13_cosetGeneratorStep_1762 s
  · exact g32p_row13_cosetGeneratorStep_1763 s
  · exact g32p_row13_cosetGeneratorStep_1764 s
  · exact g32p_row13_cosetGeneratorStep_1765 s
  · exact g32p_row13_cosetGeneratorStep_1766 s
  · exact g32p_row13_cosetGeneratorStep_1767 s
  · exact g32p_row13_cosetGeneratorStep_1768 s
  · exact g32p_row13_cosetGeneratorStep_1769 s
  · exact g32p_row13_cosetGeneratorStep_1770 s
  · exact g32p_row13_cosetGeneratorStep_1771 s
  · exact g32p_row13_cosetGeneratorStep_1772 s
  · exact g32p_row13_cosetGeneratorStep_1773 s
  · exact g32p_row13_cosetGeneratorStep_1774 s
  · exact g32p_row13_cosetGeneratorStep_1775 s

theorem g32p_row13_cosetBranchBlock_0110 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 110 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 110 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 110 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1760 s
  · exact g32p_row13_cosetBranchStep_1761 s
  · exact g32p_row13_cosetBranchStep_1762 s
  · exact g32p_row13_cosetBranchStep_1763 s
  · exact g32p_row13_cosetBranchStep_1764 s
  · exact g32p_row13_cosetBranchStep_1765 s
  · exact g32p_row13_cosetBranchStep_1766 s
  · exact g32p_row13_cosetBranchStep_1767 s
  · exact g32p_row13_cosetBranchStep_1768 s
  · exact g32p_row13_cosetBranchStep_1769 s
  · exact g32p_row13_cosetBranchStep_1770 s
  · exact g32p_row13_cosetBranchStep_1771 s
  · exact g32p_row13_cosetBranchStep_1772 s
  · exact g32p_row13_cosetBranchStep_1773 s
  · exact g32p_row13_cosetBranchStep_1774 s
  · exact g32p_row13_cosetBranchStep_1775 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_1776 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1776) = g32p_row13_cosetRepresentatives 1776 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1776 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1776) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1776))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1776)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1776 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1776) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1776))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1776)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1777 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1777) = g32p_row13_cosetRepresentatives 1777 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1777 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1777) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1777))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1777)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1777 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1777) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1777))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1777)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1778 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1778) = g32p_row13_cosetRepresentatives 1778 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1778 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1778) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1778))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1778)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1778 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1778) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1778))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1778)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1779 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1779) = g32p_row13_cosetRepresentatives 1779 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1779 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1779) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1779))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1779)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1779 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1779) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1779))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1779)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1780 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1780) = g32p_row13_cosetRepresentatives 1780 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1780 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1780) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1780))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1780)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1780 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1780) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1780))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1780)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1781 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1781) = g32p_row13_cosetRepresentatives 1781 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1781 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1781) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1781))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1781)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1781 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1781) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1781))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1781)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1782 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1782) = g32p_row13_cosetRepresentatives 1782 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1782 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1782) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1782))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1782)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1782 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1782) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1782))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1782)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1783 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1783) = g32p_row13_cosetRepresentatives 1783 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1783 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1783) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1783))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1783)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1783 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1783) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1783))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1783)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1784 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1784) = g32p_row13_cosetRepresentatives 1784 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1784 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1784) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1784))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1784)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1784 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1784) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1784))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1784)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1785 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1785) = g32p_row13_cosetRepresentatives 1785 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1785 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1785) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1785))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1785)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1785 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1785) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1785))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1785)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1786 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1786) = g32p_row13_cosetRepresentatives 1786 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1786 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1786) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1786))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1786)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1786 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1786) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1786))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1786)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1787 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1787) = g32p_row13_cosetRepresentatives 1787 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1787 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1787) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1787))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1787)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1787 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1787) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1787))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1787)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1788 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1788) = g32p_row13_cosetRepresentatives 1788 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1788 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1788) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1788))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1788)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1788 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1788) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1788))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1788)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1789 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1789) = g32p_row13_cosetRepresentatives 1789 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1789 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1789) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1789))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1789)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1789 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1789) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1789))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1789)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1790 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1790) = g32p_row13_cosetRepresentatives 1790 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1790 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1790) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1790))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1790)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1790 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1790) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1790))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1790)) := by
  decide +kernel

theorem g32p_row13_cosetWord_1791 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 1791) = g32p_row13_cosetRepresentatives 1791 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_1791 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 1791) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 1791))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 1791)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_1791 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 1791) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 1791))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 1791)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0111 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 111 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 111 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_1776
  · exact g32p_row13_cosetWord_1777
  · exact g32p_row13_cosetWord_1778
  · exact g32p_row13_cosetWord_1779
  · exact g32p_row13_cosetWord_1780
  · exact g32p_row13_cosetWord_1781
  · exact g32p_row13_cosetWord_1782
  · exact g32p_row13_cosetWord_1783
  · exact g32p_row13_cosetWord_1784
  · exact g32p_row13_cosetWord_1785
  · exact g32p_row13_cosetWord_1786
  · exact g32p_row13_cosetWord_1787
  · exact g32p_row13_cosetWord_1788
  · exact g32p_row13_cosetWord_1789
  · exact g32p_row13_cosetWord_1790
  · exact g32p_row13_cosetWord_1791

theorem g32p_row13_cosetGeneratorBlock_0111 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 111 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 111 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 111 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_1776 s
  · exact g32p_row13_cosetGeneratorStep_1777 s
  · exact g32p_row13_cosetGeneratorStep_1778 s
  · exact g32p_row13_cosetGeneratorStep_1779 s
  · exact g32p_row13_cosetGeneratorStep_1780 s
  · exact g32p_row13_cosetGeneratorStep_1781 s
  · exact g32p_row13_cosetGeneratorStep_1782 s
  · exact g32p_row13_cosetGeneratorStep_1783 s
  · exact g32p_row13_cosetGeneratorStep_1784 s
  · exact g32p_row13_cosetGeneratorStep_1785 s
  · exact g32p_row13_cosetGeneratorStep_1786 s
  · exact g32p_row13_cosetGeneratorStep_1787 s
  · exact g32p_row13_cosetGeneratorStep_1788 s
  · exact g32p_row13_cosetGeneratorStep_1789 s
  · exact g32p_row13_cosetGeneratorStep_1790 s
  · exact g32p_row13_cosetGeneratorStep_1791 s

theorem g32p_row13_cosetBranchBlock_0111 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 111 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 111 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 111 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_1776 s
  · exact g32p_row13_cosetBranchStep_1777 s
  · exact g32p_row13_cosetBranchStep_1778 s
  · exact g32p_row13_cosetBranchStep_1779 s
  · exact g32p_row13_cosetBranchStep_1780 s
  · exact g32p_row13_cosetBranchStep_1781 s
  · exact g32p_row13_cosetBranchStep_1782 s
  · exact g32p_row13_cosetBranchStep_1783 s
  · exact g32p_row13_cosetBranchStep_1784 s
  · exact g32p_row13_cosetBranchStep_1785 s
  · exact g32p_row13_cosetBranchStep_1786 s
  · exact g32p_row13_cosetBranchStep_1787 s
  · exact g32p_row13_cosetBranchStep_1788 s
  · exact g32p_row13_cosetBranchStep_1789 s
  · exact g32p_row13_cosetBranchStep_1790 s
  · exact g32p_row13_cosetBranchStep_1791 s


end HodgeLean.Foundations.Program

end
