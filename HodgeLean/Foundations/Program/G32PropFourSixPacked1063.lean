import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked1044

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4608 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4608) = g32p_row13_cosetRepresentatives 4608 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4608 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4608) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4608))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4608)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4608 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4608) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4608))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4608)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4609 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4609) = g32p_row13_cosetRepresentatives 4609 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4609 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4609) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4609))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4609)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4609 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4609) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4609))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4609)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4610 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4610) = g32p_row13_cosetRepresentatives 4610 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4610 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4610) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4610))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4610)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4610 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4610) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4610))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4610)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4611 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4611) = g32p_row13_cosetRepresentatives 4611 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4611 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4611) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4611))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4611)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4611 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4611) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4611))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4611)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4612 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4612) = g32p_row13_cosetRepresentatives 4612 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4612 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4612) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4612))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4612)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4612 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4612) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4612))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4612)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4613 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4613) = g32p_row13_cosetRepresentatives 4613 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4613 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4613) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4613))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4613)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4613 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4613) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4613))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4613)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4614 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4614) = g32p_row13_cosetRepresentatives 4614 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4614 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4614) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4614))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4614)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4614 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4614) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4614))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4614)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4615 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4615) = g32p_row13_cosetRepresentatives 4615 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4615 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4615) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4615))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4615)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4615 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4615) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4615))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4615)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4616 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4616) = g32p_row13_cosetRepresentatives 4616 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4616 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4616) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4616))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4616)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4616 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4616) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4616))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4616)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4617 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4617) = g32p_row13_cosetRepresentatives 4617 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4617 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4617) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4617))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4617)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4617 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4617) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4617))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4617)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4618 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4618) = g32p_row13_cosetRepresentatives 4618 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4618 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4618) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4618))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4618)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4618 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4618) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4618))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4618)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4619 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4619) = g32p_row13_cosetRepresentatives 4619 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4619 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4619) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4619))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4619)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4619 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4619) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4619))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4619)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4620 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4620) = g32p_row13_cosetRepresentatives 4620 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4620 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4620) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4620))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4620)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4620 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4620) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4620))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4620)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4621 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4621) = g32p_row13_cosetRepresentatives 4621 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4621 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4621) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4621))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4621)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4621 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4621) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4621))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4621)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4622 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4622) = g32p_row13_cosetRepresentatives 4622 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4622 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4622) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4622))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4622)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4622 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4622) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4622))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4622)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4623 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4623) = g32p_row13_cosetRepresentatives 4623 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4623 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4623) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4623))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4623)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4623 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4623) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4623))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4623)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0288 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 288 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 288 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4608
  · exact g32p_row13_cosetWord_4609
  · exact g32p_row13_cosetWord_4610
  · exact g32p_row13_cosetWord_4611
  · exact g32p_row13_cosetWord_4612
  · exact g32p_row13_cosetWord_4613
  · exact g32p_row13_cosetWord_4614
  · exact g32p_row13_cosetWord_4615
  · exact g32p_row13_cosetWord_4616
  · exact g32p_row13_cosetWord_4617
  · exact g32p_row13_cosetWord_4618
  · exact g32p_row13_cosetWord_4619
  · exact g32p_row13_cosetWord_4620
  · exact g32p_row13_cosetWord_4621
  · exact g32p_row13_cosetWord_4622
  · exact g32p_row13_cosetWord_4623

theorem g32p_row13_cosetGeneratorBlock_0288 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 288 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 288 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 288 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4608 s
  · exact g32p_row13_cosetGeneratorStep_4609 s
  · exact g32p_row13_cosetGeneratorStep_4610 s
  · exact g32p_row13_cosetGeneratorStep_4611 s
  · exact g32p_row13_cosetGeneratorStep_4612 s
  · exact g32p_row13_cosetGeneratorStep_4613 s
  · exact g32p_row13_cosetGeneratorStep_4614 s
  · exact g32p_row13_cosetGeneratorStep_4615 s
  · exact g32p_row13_cosetGeneratorStep_4616 s
  · exact g32p_row13_cosetGeneratorStep_4617 s
  · exact g32p_row13_cosetGeneratorStep_4618 s
  · exact g32p_row13_cosetGeneratorStep_4619 s
  · exact g32p_row13_cosetGeneratorStep_4620 s
  · exact g32p_row13_cosetGeneratorStep_4621 s
  · exact g32p_row13_cosetGeneratorStep_4622 s
  · exact g32p_row13_cosetGeneratorStep_4623 s

theorem g32p_row13_cosetBranchBlock_0288 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 288 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 288 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 288 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4608 s
  · exact g32p_row13_cosetBranchStep_4609 s
  · exact g32p_row13_cosetBranchStep_4610 s
  · exact g32p_row13_cosetBranchStep_4611 s
  · exact g32p_row13_cosetBranchStep_4612 s
  · exact g32p_row13_cosetBranchStep_4613 s
  · exact g32p_row13_cosetBranchStep_4614 s
  · exact g32p_row13_cosetBranchStep_4615 s
  · exact g32p_row13_cosetBranchStep_4616 s
  · exact g32p_row13_cosetBranchStep_4617 s
  · exact g32p_row13_cosetBranchStep_4618 s
  · exact g32p_row13_cosetBranchStep_4619 s
  · exact g32p_row13_cosetBranchStep_4620 s
  · exact g32p_row13_cosetBranchStep_4621 s
  · exact g32p_row13_cosetBranchStep_4622 s
  · exact g32p_row13_cosetBranchStep_4623 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4624 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4624) = g32p_row13_cosetRepresentatives 4624 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4624 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4624) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4624))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4624)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4624 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4624) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4624))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4624)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4625 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4625) = g32p_row13_cosetRepresentatives 4625 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4625 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4625) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4625))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4625)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4625 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4625) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4625))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4625)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4626 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4626) = g32p_row13_cosetRepresentatives 4626 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4626 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4626) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4626))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4626)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4626 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4626) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4626))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4626)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4627 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4627) = g32p_row13_cosetRepresentatives 4627 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4627 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4627) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4627))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4627)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4627 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4627) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4627))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4627)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4628 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4628) = g32p_row13_cosetRepresentatives 4628 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4628 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4628) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4628))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4628)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4628 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4628) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4628))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4628)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4629 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4629) = g32p_row13_cosetRepresentatives 4629 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4629 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4629) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4629))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4629)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4629 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4629) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4629))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4629)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4630 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4630) = g32p_row13_cosetRepresentatives 4630 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4630 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4630) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4630))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4630)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4630 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4630) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4630))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4630)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4631 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4631) = g32p_row13_cosetRepresentatives 4631 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4631 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4631) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4631))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4631)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4631 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4631) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4631))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4631)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4632 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4632) = g32p_row13_cosetRepresentatives 4632 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4632 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4632) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4632))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4632)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4632 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4632) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4632))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4632)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4633 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4633) = g32p_row13_cosetRepresentatives 4633 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4633 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4633) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4633))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4633)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4633 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4633) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4633))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4633)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4634 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4634) = g32p_row13_cosetRepresentatives 4634 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4634 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4634) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4634))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4634)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4634 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4634) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4634))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4634)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4635 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4635) = g32p_row13_cosetRepresentatives 4635 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4635 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4635) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4635))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4635)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4635 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4635) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4635))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4635)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4636 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4636) = g32p_row13_cosetRepresentatives 4636 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4636 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4636) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4636))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4636)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4636 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4636) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4636))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4636)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4637 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4637) = g32p_row13_cosetRepresentatives 4637 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4637 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4637) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4637))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4637)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4637 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4637) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4637))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4637)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4638 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4638) = g32p_row13_cosetRepresentatives 4638 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4638 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4638) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4638))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4638)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4638 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4638) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4638))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4638)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4639 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4639) = g32p_row13_cosetRepresentatives 4639 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4639 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4639) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4639))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4639)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4639 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4639) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4639))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4639)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0289 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 289 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 289 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4624
  · exact g32p_row13_cosetWord_4625
  · exact g32p_row13_cosetWord_4626
  · exact g32p_row13_cosetWord_4627
  · exact g32p_row13_cosetWord_4628
  · exact g32p_row13_cosetWord_4629
  · exact g32p_row13_cosetWord_4630
  · exact g32p_row13_cosetWord_4631
  · exact g32p_row13_cosetWord_4632
  · exact g32p_row13_cosetWord_4633
  · exact g32p_row13_cosetWord_4634
  · exact g32p_row13_cosetWord_4635
  · exact g32p_row13_cosetWord_4636
  · exact g32p_row13_cosetWord_4637
  · exact g32p_row13_cosetWord_4638
  · exact g32p_row13_cosetWord_4639

theorem g32p_row13_cosetGeneratorBlock_0289 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 289 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 289 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 289 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4624 s
  · exact g32p_row13_cosetGeneratorStep_4625 s
  · exact g32p_row13_cosetGeneratorStep_4626 s
  · exact g32p_row13_cosetGeneratorStep_4627 s
  · exact g32p_row13_cosetGeneratorStep_4628 s
  · exact g32p_row13_cosetGeneratorStep_4629 s
  · exact g32p_row13_cosetGeneratorStep_4630 s
  · exact g32p_row13_cosetGeneratorStep_4631 s
  · exact g32p_row13_cosetGeneratorStep_4632 s
  · exact g32p_row13_cosetGeneratorStep_4633 s
  · exact g32p_row13_cosetGeneratorStep_4634 s
  · exact g32p_row13_cosetGeneratorStep_4635 s
  · exact g32p_row13_cosetGeneratorStep_4636 s
  · exact g32p_row13_cosetGeneratorStep_4637 s
  · exact g32p_row13_cosetGeneratorStep_4638 s
  · exact g32p_row13_cosetGeneratorStep_4639 s

theorem g32p_row13_cosetBranchBlock_0289 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 289 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 289 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 289 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4624 s
  · exact g32p_row13_cosetBranchStep_4625 s
  · exact g32p_row13_cosetBranchStep_4626 s
  · exact g32p_row13_cosetBranchStep_4627 s
  · exact g32p_row13_cosetBranchStep_4628 s
  · exact g32p_row13_cosetBranchStep_4629 s
  · exact g32p_row13_cosetBranchStep_4630 s
  · exact g32p_row13_cosetBranchStep_4631 s
  · exact g32p_row13_cosetBranchStep_4632 s
  · exact g32p_row13_cosetBranchStep_4633 s
  · exact g32p_row13_cosetBranchStep_4634 s
  · exact g32p_row13_cosetBranchStep_4635 s
  · exact g32p_row13_cosetBranchStep_4636 s
  · exact g32p_row13_cosetBranchStep_4637 s
  · exact g32p_row13_cosetBranchStep_4638 s
  · exact g32p_row13_cosetBranchStep_4639 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4640 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4640) = g32p_row13_cosetRepresentatives 4640 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4640 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4640) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4640))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4640)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4640 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4640) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4640))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4640)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4641 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4641) = g32p_row13_cosetRepresentatives 4641 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4641 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4641) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4641))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4641)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4641 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4641) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4641))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4641)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4642 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4642) = g32p_row13_cosetRepresentatives 4642 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4642 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4642) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4642))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4642)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4642 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4642) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4642))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4642)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4643 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4643) = g32p_row13_cosetRepresentatives 4643 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4643 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4643) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4643))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4643)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4643 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4643) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4643))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4643)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4644 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4644) = g32p_row13_cosetRepresentatives 4644 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4644 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4644) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4644))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4644)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4644 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4644) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4644))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4644)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4645 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4645) = g32p_row13_cosetRepresentatives 4645 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4645 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4645) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4645))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4645)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4645 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4645) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4645))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4645)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4646 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4646) = g32p_row13_cosetRepresentatives 4646 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4646 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4646) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4646))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4646)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4646 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4646) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4646))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4646)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4647 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4647) = g32p_row13_cosetRepresentatives 4647 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4647 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4647) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4647))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4647)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4647 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4647) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4647))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4647)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4648 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4648) = g32p_row13_cosetRepresentatives 4648 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4648 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4648) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4648))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4648)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4648 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4648) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4648))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4648)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4649 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4649) = g32p_row13_cosetRepresentatives 4649 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4649 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4649) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4649))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4649)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4649 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4649) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4649))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4649)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4650 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4650) = g32p_row13_cosetRepresentatives 4650 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4650 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4650) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4650))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4650)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4650 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4650) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4650))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4650)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4651 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4651) = g32p_row13_cosetRepresentatives 4651 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4651 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4651) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4651))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4651)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4651 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4651) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4651))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4651)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4652 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4652) = g32p_row13_cosetRepresentatives 4652 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4652 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4652) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4652))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4652)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4652 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4652) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4652))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4652)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4653 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4653) = g32p_row13_cosetRepresentatives 4653 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4653 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4653) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4653))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4653)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4653 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4653) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4653))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4653)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4654 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4654) = g32p_row13_cosetRepresentatives 4654 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4654 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4654) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4654))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4654)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4654 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4654) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4654))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4654)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4655 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4655) = g32p_row13_cosetRepresentatives 4655 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4655 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4655) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4655))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4655)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4655 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4655) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4655))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4655)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0290 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 290 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 290 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4640
  · exact g32p_row13_cosetWord_4641
  · exact g32p_row13_cosetWord_4642
  · exact g32p_row13_cosetWord_4643
  · exact g32p_row13_cosetWord_4644
  · exact g32p_row13_cosetWord_4645
  · exact g32p_row13_cosetWord_4646
  · exact g32p_row13_cosetWord_4647
  · exact g32p_row13_cosetWord_4648
  · exact g32p_row13_cosetWord_4649
  · exact g32p_row13_cosetWord_4650
  · exact g32p_row13_cosetWord_4651
  · exact g32p_row13_cosetWord_4652
  · exact g32p_row13_cosetWord_4653
  · exact g32p_row13_cosetWord_4654
  · exact g32p_row13_cosetWord_4655

theorem g32p_row13_cosetGeneratorBlock_0290 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 290 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 290 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 290 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4640 s
  · exact g32p_row13_cosetGeneratorStep_4641 s
  · exact g32p_row13_cosetGeneratorStep_4642 s
  · exact g32p_row13_cosetGeneratorStep_4643 s
  · exact g32p_row13_cosetGeneratorStep_4644 s
  · exact g32p_row13_cosetGeneratorStep_4645 s
  · exact g32p_row13_cosetGeneratorStep_4646 s
  · exact g32p_row13_cosetGeneratorStep_4647 s
  · exact g32p_row13_cosetGeneratorStep_4648 s
  · exact g32p_row13_cosetGeneratorStep_4649 s
  · exact g32p_row13_cosetGeneratorStep_4650 s
  · exact g32p_row13_cosetGeneratorStep_4651 s
  · exact g32p_row13_cosetGeneratorStep_4652 s
  · exact g32p_row13_cosetGeneratorStep_4653 s
  · exact g32p_row13_cosetGeneratorStep_4654 s
  · exact g32p_row13_cosetGeneratorStep_4655 s

theorem g32p_row13_cosetBranchBlock_0290 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 290 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 290 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 290 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4640 s
  · exact g32p_row13_cosetBranchStep_4641 s
  · exact g32p_row13_cosetBranchStep_4642 s
  · exact g32p_row13_cosetBranchStep_4643 s
  · exact g32p_row13_cosetBranchStep_4644 s
  · exact g32p_row13_cosetBranchStep_4645 s
  · exact g32p_row13_cosetBranchStep_4646 s
  · exact g32p_row13_cosetBranchStep_4647 s
  · exact g32p_row13_cosetBranchStep_4648 s
  · exact g32p_row13_cosetBranchStep_4649 s
  · exact g32p_row13_cosetBranchStep_4650 s
  · exact g32p_row13_cosetBranchStep_4651 s
  · exact g32p_row13_cosetBranchStep_4652 s
  · exact g32p_row13_cosetBranchStep_4653 s
  · exact g32p_row13_cosetBranchStep_4654 s
  · exact g32p_row13_cosetBranchStep_4655 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4656 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4656) = g32p_row13_cosetRepresentatives 4656 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4656 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4656) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4656))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4656)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4656 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4656) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4656))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4656)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4657 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4657) = g32p_row13_cosetRepresentatives 4657 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4657 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4657) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4657))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4657)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4657 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4657) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4657))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4657)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4658 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4658) = g32p_row13_cosetRepresentatives 4658 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4658 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4658) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4658))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4658)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4658 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4658) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4658))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4658)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4659 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4659) = g32p_row13_cosetRepresentatives 4659 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4659 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4659) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4659))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4659)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4659 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4659) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4659))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4659)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4660 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4660) = g32p_row13_cosetRepresentatives 4660 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4660 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4660) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4660))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4660)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4660 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4660) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4660))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4660)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4661 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4661) = g32p_row13_cosetRepresentatives 4661 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4661 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4661) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4661))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4661)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4661 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4661) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4661))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4661)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4662 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4662) = g32p_row13_cosetRepresentatives 4662 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4662 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4662) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4662))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4662)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4662 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4662) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4662))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4662)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4663 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4663) = g32p_row13_cosetRepresentatives 4663 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4663 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4663) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4663))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4663)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4663 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4663) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4663))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4663)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4664 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4664) = g32p_row13_cosetRepresentatives 4664 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4664 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4664) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4664))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4664)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4664 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4664) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4664))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4664)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4665 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4665) = g32p_row13_cosetRepresentatives 4665 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4665 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4665) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4665))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4665)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4665 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4665) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4665))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4665)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4666 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4666) = g32p_row13_cosetRepresentatives 4666 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4666 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4666) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4666))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4666)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4666 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4666) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4666))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4666)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4667 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4667) = g32p_row13_cosetRepresentatives 4667 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4667 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4667) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4667))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4667)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4667 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4667) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4667))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4667)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4668 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4668) = g32p_row13_cosetRepresentatives 4668 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4668 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4668) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4668))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4668)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4668 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4668) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4668))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4668)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4669 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4669) = g32p_row13_cosetRepresentatives 4669 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4669 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4669) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4669))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4669)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4669 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4669) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4669))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4669)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4670 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4670) = g32p_row13_cosetRepresentatives 4670 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4670 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4670) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4670))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4670)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4670 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4670) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4670))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4670)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4671 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4671) = g32p_row13_cosetRepresentatives 4671 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4671 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4671) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4671))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4671)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4671 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4671) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4671))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4671)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0291 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 291 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 291 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4656
  · exact g32p_row13_cosetWord_4657
  · exact g32p_row13_cosetWord_4658
  · exact g32p_row13_cosetWord_4659
  · exact g32p_row13_cosetWord_4660
  · exact g32p_row13_cosetWord_4661
  · exact g32p_row13_cosetWord_4662
  · exact g32p_row13_cosetWord_4663
  · exact g32p_row13_cosetWord_4664
  · exact g32p_row13_cosetWord_4665
  · exact g32p_row13_cosetWord_4666
  · exact g32p_row13_cosetWord_4667
  · exact g32p_row13_cosetWord_4668
  · exact g32p_row13_cosetWord_4669
  · exact g32p_row13_cosetWord_4670
  · exact g32p_row13_cosetWord_4671

theorem g32p_row13_cosetGeneratorBlock_0291 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 291 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 291 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 291 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4656 s
  · exact g32p_row13_cosetGeneratorStep_4657 s
  · exact g32p_row13_cosetGeneratorStep_4658 s
  · exact g32p_row13_cosetGeneratorStep_4659 s
  · exact g32p_row13_cosetGeneratorStep_4660 s
  · exact g32p_row13_cosetGeneratorStep_4661 s
  · exact g32p_row13_cosetGeneratorStep_4662 s
  · exact g32p_row13_cosetGeneratorStep_4663 s
  · exact g32p_row13_cosetGeneratorStep_4664 s
  · exact g32p_row13_cosetGeneratorStep_4665 s
  · exact g32p_row13_cosetGeneratorStep_4666 s
  · exact g32p_row13_cosetGeneratorStep_4667 s
  · exact g32p_row13_cosetGeneratorStep_4668 s
  · exact g32p_row13_cosetGeneratorStep_4669 s
  · exact g32p_row13_cosetGeneratorStep_4670 s
  · exact g32p_row13_cosetGeneratorStep_4671 s

theorem g32p_row13_cosetBranchBlock_0291 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 291 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 291 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 291 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4656 s
  · exact g32p_row13_cosetBranchStep_4657 s
  · exact g32p_row13_cosetBranchStep_4658 s
  · exact g32p_row13_cosetBranchStep_4659 s
  · exact g32p_row13_cosetBranchStep_4660 s
  · exact g32p_row13_cosetBranchStep_4661 s
  · exact g32p_row13_cosetBranchStep_4662 s
  · exact g32p_row13_cosetBranchStep_4663 s
  · exact g32p_row13_cosetBranchStep_4664 s
  · exact g32p_row13_cosetBranchStep_4665 s
  · exact g32p_row13_cosetBranchStep_4666 s
  · exact g32p_row13_cosetBranchStep_4667 s
  · exact g32p_row13_cosetBranchStep_4668 s
  · exact g32p_row13_cosetBranchStep_4669 s
  · exact g32p_row13_cosetBranchStep_4670 s
  · exact g32p_row13_cosetBranchStep_4671 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4672 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4672) = g32p_row13_cosetRepresentatives 4672 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4672 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4672) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4672))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4672)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4672 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4672) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4672))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4672)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4673 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4673) = g32p_row13_cosetRepresentatives 4673 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4673 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4673) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4673))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4673)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4673 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4673) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4673))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4673)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4674 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4674) = g32p_row13_cosetRepresentatives 4674 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4674 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4674) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4674))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4674)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4674 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4674) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4674))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4674)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4675 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4675) = g32p_row13_cosetRepresentatives 4675 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4675 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4675) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4675))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4675)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4675 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4675) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4675))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4675)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4676 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4676) = g32p_row13_cosetRepresentatives 4676 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4676 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4676) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4676))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4676)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4676 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4676) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4676))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4676)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4677 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4677) = g32p_row13_cosetRepresentatives 4677 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4677 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4677) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4677))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4677)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4677 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4677) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4677))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4677)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4678 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4678) = g32p_row13_cosetRepresentatives 4678 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4678 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4678) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4678))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4678)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4678 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4678) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4678))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4678)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4679 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4679) = g32p_row13_cosetRepresentatives 4679 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4679 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4679) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4679))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4679)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4679 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4679) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4679))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4679)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4680 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4680) = g32p_row13_cosetRepresentatives 4680 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4680 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4680) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4680))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4680)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4680 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4680) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4680))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4680)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4681 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4681) = g32p_row13_cosetRepresentatives 4681 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4681 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4681) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4681))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4681)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4681 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4681) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4681))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4681)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4682 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4682) = g32p_row13_cosetRepresentatives 4682 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4682 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4682) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4682))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4682)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4682 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4682) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4682))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4682)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4683 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4683) = g32p_row13_cosetRepresentatives 4683 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4683 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4683) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4683))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4683)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4683 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4683) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4683))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4683)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4684 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4684) = g32p_row13_cosetRepresentatives 4684 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4684 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4684) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4684))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4684)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4684 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4684) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4684))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4684)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4685 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4685) = g32p_row13_cosetRepresentatives 4685 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4685 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4685) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4685))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4685)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4685 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4685) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4685))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4685)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4686 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4686) = g32p_row13_cosetRepresentatives 4686 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4686 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4686) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4686))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4686)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4686 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4686) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4686))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4686)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4687 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4687) = g32p_row13_cosetRepresentatives 4687 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4687 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4687) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4687))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4687)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4687 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4687) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4687))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4687)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0292 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 292 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 292 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4672
  · exact g32p_row13_cosetWord_4673
  · exact g32p_row13_cosetWord_4674
  · exact g32p_row13_cosetWord_4675
  · exact g32p_row13_cosetWord_4676
  · exact g32p_row13_cosetWord_4677
  · exact g32p_row13_cosetWord_4678
  · exact g32p_row13_cosetWord_4679
  · exact g32p_row13_cosetWord_4680
  · exact g32p_row13_cosetWord_4681
  · exact g32p_row13_cosetWord_4682
  · exact g32p_row13_cosetWord_4683
  · exact g32p_row13_cosetWord_4684
  · exact g32p_row13_cosetWord_4685
  · exact g32p_row13_cosetWord_4686
  · exact g32p_row13_cosetWord_4687

theorem g32p_row13_cosetGeneratorBlock_0292 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 292 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 292 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 292 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4672 s
  · exact g32p_row13_cosetGeneratorStep_4673 s
  · exact g32p_row13_cosetGeneratorStep_4674 s
  · exact g32p_row13_cosetGeneratorStep_4675 s
  · exact g32p_row13_cosetGeneratorStep_4676 s
  · exact g32p_row13_cosetGeneratorStep_4677 s
  · exact g32p_row13_cosetGeneratorStep_4678 s
  · exact g32p_row13_cosetGeneratorStep_4679 s
  · exact g32p_row13_cosetGeneratorStep_4680 s
  · exact g32p_row13_cosetGeneratorStep_4681 s
  · exact g32p_row13_cosetGeneratorStep_4682 s
  · exact g32p_row13_cosetGeneratorStep_4683 s
  · exact g32p_row13_cosetGeneratorStep_4684 s
  · exact g32p_row13_cosetGeneratorStep_4685 s
  · exact g32p_row13_cosetGeneratorStep_4686 s
  · exact g32p_row13_cosetGeneratorStep_4687 s

theorem g32p_row13_cosetBranchBlock_0292 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 292 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 292 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 292 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4672 s
  · exact g32p_row13_cosetBranchStep_4673 s
  · exact g32p_row13_cosetBranchStep_4674 s
  · exact g32p_row13_cosetBranchStep_4675 s
  · exact g32p_row13_cosetBranchStep_4676 s
  · exact g32p_row13_cosetBranchStep_4677 s
  · exact g32p_row13_cosetBranchStep_4678 s
  · exact g32p_row13_cosetBranchStep_4679 s
  · exact g32p_row13_cosetBranchStep_4680 s
  · exact g32p_row13_cosetBranchStep_4681 s
  · exact g32p_row13_cosetBranchStep_4682 s
  · exact g32p_row13_cosetBranchStep_4683 s
  · exact g32p_row13_cosetBranchStep_4684 s
  · exact g32p_row13_cosetBranchStep_4685 s
  · exact g32p_row13_cosetBranchStep_4686 s
  · exact g32p_row13_cosetBranchStep_4687 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4688 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4688) = g32p_row13_cosetRepresentatives 4688 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4688 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4688) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4688))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4688)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4688 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4688) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4688))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4688)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4689 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4689) = g32p_row13_cosetRepresentatives 4689 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4689 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4689) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4689))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4689)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4689 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4689) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4689))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4689)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4690 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4690) = g32p_row13_cosetRepresentatives 4690 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4690 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4690) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4690))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4690)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4690 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4690) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4690))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4690)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4691 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4691) = g32p_row13_cosetRepresentatives 4691 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4691 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4691) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4691))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4691)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4691 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4691) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4691))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4691)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4692 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4692) = g32p_row13_cosetRepresentatives 4692 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4692 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4692) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4692))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4692)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4692 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4692) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4692))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4692)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4693 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4693) = g32p_row13_cosetRepresentatives 4693 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4693 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4693) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4693))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4693)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4693 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4693) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4693))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4693)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4694 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4694) = g32p_row13_cosetRepresentatives 4694 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4694 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4694) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4694))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4694)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4694 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4694) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4694))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4694)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4695 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4695) = g32p_row13_cosetRepresentatives 4695 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4695 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4695) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4695))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4695)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4695 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4695) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4695))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4695)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4696 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4696) = g32p_row13_cosetRepresentatives 4696 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4696 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4696) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4696))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4696)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4696 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4696) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4696))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4696)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4697 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4697) = g32p_row13_cosetRepresentatives 4697 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4697 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4697) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4697))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4697)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4697 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4697) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4697))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4697)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4698 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4698) = g32p_row13_cosetRepresentatives 4698 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4698 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4698) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4698))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4698)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4698 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4698) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4698))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4698)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4699 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4699) = g32p_row13_cosetRepresentatives 4699 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4699 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4699) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4699))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4699)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4699 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4699) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4699))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4699)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4700 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4700) = g32p_row13_cosetRepresentatives 4700 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4700 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4700) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4700))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4700)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4700 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4700) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4700))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4700)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4701 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4701) = g32p_row13_cosetRepresentatives 4701 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4701 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4701) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4701))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4701)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4701 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4701) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4701))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4701)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4702 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4702) = g32p_row13_cosetRepresentatives 4702 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4702 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4702) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4702))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4702)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4702 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4702) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4702))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4702)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4703 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4703) = g32p_row13_cosetRepresentatives 4703 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4703 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4703) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4703))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4703)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4703 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4703) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4703))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4703)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0293 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 293 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 293 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4688
  · exact g32p_row13_cosetWord_4689
  · exact g32p_row13_cosetWord_4690
  · exact g32p_row13_cosetWord_4691
  · exact g32p_row13_cosetWord_4692
  · exact g32p_row13_cosetWord_4693
  · exact g32p_row13_cosetWord_4694
  · exact g32p_row13_cosetWord_4695
  · exact g32p_row13_cosetWord_4696
  · exact g32p_row13_cosetWord_4697
  · exact g32p_row13_cosetWord_4698
  · exact g32p_row13_cosetWord_4699
  · exact g32p_row13_cosetWord_4700
  · exact g32p_row13_cosetWord_4701
  · exact g32p_row13_cosetWord_4702
  · exact g32p_row13_cosetWord_4703

theorem g32p_row13_cosetGeneratorBlock_0293 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 293 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 293 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 293 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4688 s
  · exact g32p_row13_cosetGeneratorStep_4689 s
  · exact g32p_row13_cosetGeneratorStep_4690 s
  · exact g32p_row13_cosetGeneratorStep_4691 s
  · exact g32p_row13_cosetGeneratorStep_4692 s
  · exact g32p_row13_cosetGeneratorStep_4693 s
  · exact g32p_row13_cosetGeneratorStep_4694 s
  · exact g32p_row13_cosetGeneratorStep_4695 s
  · exact g32p_row13_cosetGeneratorStep_4696 s
  · exact g32p_row13_cosetGeneratorStep_4697 s
  · exact g32p_row13_cosetGeneratorStep_4698 s
  · exact g32p_row13_cosetGeneratorStep_4699 s
  · exact g32p_row13_cosetGeneratorStep_4700 s
  · exact g32p_row13_cosetGeneratorStep_4701 s
  · exact g32p_row13_cosetGeneratorStep_4702 s
  · exact g32p_row13_cosetGeneratorStep_4703 s

theorem g32p_row13_cosetBranchBlock_0293 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 293 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 293 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 293 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4688 s
  · exact g32p_row13_cosetBranchStep_4689 s
  · exact g32p_row13_cosetBranchStep_4690 s
  · exact g32p_row13_cosetBranchStep_4691 s
  · exact g32p_row13_cosetBranchStep_4692 s
  · exact g32p_row13_cosetBranchStep_4693 s
  · exact g32p_row13_cosetBranchStep_4694 s
  · exact g32p_row13_cosetBranchStep_4695 s
  · exact g32p_row13_cosetBranchStep_4696 s
  · exact g32p_row13_cosetBranchStep_4697 s
  · exact g32p_row13_cosetBranchStep_4698 s
  · exact g32p_row13_cosetBranchStep_4699 s
  · exact g32p_row13_cosetBranchStep_4700 s
  · exact g32p_row13_cosetBranchStep_4701 s
  · exact g32p_row13_cosetBranchStep_4702 s
  · exact g32p_row13_cosetBranchStep_4703 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4704 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4704) = g32p_row13_cosetRepresentatives 4704 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4704 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4704) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4704))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4704)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4704 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4704) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4704))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4704)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4705 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4705) = g32p_row13_cosetRepresentatives 4705 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4705 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4705) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4705))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4705)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4705 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4705) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4705))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4705)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4706 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4706) = g32p_row13_cosetRepresentatives 4706 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4706 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4706) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4706))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4706)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4706 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4706) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4706))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4706)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4707 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4707) = g32p_row13_cosetRepresentatives 4707 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4707 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4707) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4707))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4707)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4707 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4707) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4707))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4707)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4708 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4708) = g32p_row13_cosetRepresentatives 4708 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4708 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4708) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4708))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4708)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4708 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4708) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4708))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4708)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4709 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4709) = g32p_row13_cosetRepresentatives 4709 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4709 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4709) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4709))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4709)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4709 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4709) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4709))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4709)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4710 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4710) = g32p_row13_cosetRepresentatives 4710 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4710 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4710) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4710))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4710)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4710 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4710) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4710))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4710)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4711 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4711) = g32p_row13_cosetRepresentatives 4711 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4711 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4711) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4711))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4711)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4711 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4711) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4711))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4711)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4712 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4712) = g32p_row13_cosetRepresentatives 4712 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4712 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4712) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4712))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4712)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4712 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4712) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4712))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4712)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4713 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4713) = g32p_row13_cosetRepresentatives 4713 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4713 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4713) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4713))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4713)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4713 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4713) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4713))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4713)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4714 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4714) = g32p_row13_cosetRepresentatives 4714 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4714 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4714) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4714))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4714)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4714 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4714) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4714))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4714)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4715 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4715) = g32p_row13_cosetRepresentatives 4715 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4715 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4715) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4715))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4715)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4715 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4715) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4715))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4715)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4716 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4716) = g32p_row13_cosetRepresentatives 4716 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4716 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4716) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4716))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4716)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4716 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4716) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4716))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4716)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4717 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4717) = g32p_row13_cosetRepresentatives 4717 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4717 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4717) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4717))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4717)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4717 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4717) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4717))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4717)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4718 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4718) = g32p_row13_cosetRepresentatives 4718 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4718 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4718) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4718))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4718)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4718 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4718) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4718))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4718)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4719 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4719) = g32p_row13_cosetRepresentatives 4719 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4719 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4719) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4719))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4719)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4719 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4719) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4719))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4719)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0294 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 294 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 294 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4704
  · exact g32p_row13_cosetWord_4705
  · exact g32p_row13_cosetWord_4706
  · exact g32p_row13_cosetWord_4707
  · exact g32p_row13_cosetWord_4708
  · exact g32p_row13_cosetWord_4709
  · exact g32p_row13_cosetWord_4710
  · exact g32p_row13_cosetWord_4711
  · exact g32p_row13_cosetWord_4712
  · exact g32p_row13_cosetWord_4713
  · exact g32p_row13_cosetWord_4714
  · exact g32p_row13_cosetWord_4715
  · exact g32p_row13_cosetWord_4716
  · exact g32p_row13_cosetWord_4717
  · exact g32p_row13_cosetWord_4718
  · exact g32p_row13_cosetWord_4719

theorem g32p_row13_cosetGeneratorBlock_0294 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 294 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 294 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 294 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4704 s
  · exact g32p_row13_cosetGeneratorStep_4705 s
  · exact g32p_row13_cosetGeneratorStep_4706 s
  · exact g32p_row13_cosetGeneratorStep_4707 s
  · exact g32p_row13_cosetGeneratorStep_4708 s
  · exact g32p_row13_cosetGeneratorStep_4709 s
  · exact g32p_row13_cosetGeneratorStep_4710 s
  · exact g32p_row13_cosetGeneratorStep_4711 s
  · exact g32p_row13_cosetGeneratorStep_4712 s
  · exact g32p_row13_cosetGeneratorStep_4713 s
  · exact g32p_row13_cosetGeneratorStep_4714 s
  · exact g32p_row13_cosetGeneratorStep_4715 s
  · exact g32p_row13_cosetGeneratorStep_4716 s
  · exact g32p_row13_cosetGeneratorStep_4717 s
  · exact g32p_row13_cosetGeneratorStep_4718 s
  · exact g32p_row13_cosetGeneratorStep_4719 s

theorem g32p_row13_cosetBranchBlock_0294 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 294 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 294 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 294 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4704 s
  · exact g32p_row13_cosetBranchStep_4705 s
  · exact g32p_row13_cosetBranchStep_4706 s
  · exact g32p_row13_cosetBranchStep_4707 s
  · exact g32p_row13_cosetBranchStep_4708 s
  · exact g32p_row13_cosetBranchStep_4709 s
  · exact g32p_row13_cosetBranchStep_4710 s
  · exact g32p_row13_cosetBranchStep_4711 s
  · exact g32p_row13_cosetBranchStep_4712 s
  · exact g32p_row13_cosetBranchStep_4713 s
  · exact g32p_row13_cosetBranchStep_4714 s
  · exact g32p_row13_cosetBranchStep_4715 s
  · exact g32p_row13_cosetBranchStep_4716 s
  · exact g32p_row13_cosetBranchStep_4717 s
  · exact g32p_row13_cosetBranchStep_4718 s
  · exact g32p_row13_cosetBranchStep_4719 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4720 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4720) = g32p_row13_cosetRepresentatives 4720 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4720 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4720) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4720))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4720)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4720 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4720) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4720))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4720)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4721 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4721) = g32p_row13_cosetRepresentatives 4721 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4721 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4721) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4721))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4721)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4721 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4721) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4721))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4721)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4722 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4722) = g32p_row13_cosetRepresentatives 4722 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4722 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4722) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4722))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4722)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4722 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4722) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4722))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4722)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4723 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4723) = g32p_row13_cosetRepresentatives 4723 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4723 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4723) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4723))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4723)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4723 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4723) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4723))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4723)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4724 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4724) = g32p_row13_cosetRepresentatives 4724 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4724 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4724) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4724))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4724)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4724 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4724) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4724))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4724)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4725 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4725) = g32p_row13_cosetRepresentatives 4725 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4725 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4725) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4725))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4725)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4725 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4725) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4725))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4725)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4726 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4726) = g32p_row13_cosetRepresentatives 4726 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4726 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4726) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4726))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4726)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4726 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4726) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4726))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4726)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4727 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4727) = g32p_row13_cosetRepresentatives 4727 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4727 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4727) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4727))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4727)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4727 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4727) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4727))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4727)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4728 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4728) = g32p_row13_cosetRepresentatives 4728 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4728 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4728) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4728))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4728)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4728 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4728) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4728))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4728)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4729 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4729) = g32p_row13_cosetRepresentatives 4729 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4729 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4729) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4729))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4729)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4729 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4729) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4729))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4729)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4730 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4730) = g32p_row13_cosetRepresentatives 4730 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4730 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4730) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4730))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4730)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4730 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4730) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4730))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4730)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4731 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4731) = g32p_row13_cosetRepresentatives 4731 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4731 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4731) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4731))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4731)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4731 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4731) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4731))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4731)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4732 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4732) = g32p_row13_cosetRepresentatives 4732 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4732 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4732) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4732))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4732)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4732 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4732) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4732))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4732)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4733 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4733) = g32p_row13_cosetRepresentatives 4733 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4733 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4733) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4733))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4733)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4733 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4733) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4733))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4733)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4734 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4734) = g32p_row13_cosetRepresentatives 4734 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4734 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4734) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4734))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4734)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4734 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4734) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4734))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4734)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4735 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4735) = g32p_row13_cosetRepresentatives 4735 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4735 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4735) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4735))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4735)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4735 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4735) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4735))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4735)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0295 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 295 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 295 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4720
  · exact g32p_row13_cosetWord_4721
  · exact g32p_row13_cosetWord_4722
  · exact g32p_row13_cosetWord_4723
  · exact g32p_row13_cosetWord_4724
  · exact g32p_row13_cosetWord_4725
  · exact g32p_row13_cosetWord_4726
  · exact g32p_row13_cosetWord_4727
  · exact g32p_row13_cosetWord_4728
  · exact g32p_row13_cosetWord_4729
  · exact g32p_row13_cosetWord_4730
  · exact g32p_row13_cosetWord_4731
  · exact g32p_row13_cosetWord_4732
  · exact g32p_row13_cosetWord_4733
  · exact g32p_row13_cosetWord_4734
  · exact g32p_row13_cosetWord_4735

theorem g32p_row13_cosetGeneratorBlock_0295 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 295 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 295 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 295 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4720 s
  · exact g32p_row13_cosetGeneratorStep_4721 s
  · exact g32p_row13_cosetGeneratorStep_4722 s
  · exact g32p_row13_cosetGeneratorStep_4723 s
  · exact g32p_row13_cosetGeneratorStep_4724 s
  · exact g32p_row13_cosetGeneratorStep_4725 s
  · exact g32p_row13_cosetGeneratorStep_4726 s
  · exact g32p_row13_cosetGeneratorStep_4727 s
  · exact g32p_row13_cosetGeneratorStep_4728 s
  · exact g32p_row13_cosetGeneratorStep_4729 s
  · exact g32p_row13_cosetGeneratorStep_4730 s
  · exact g32p_row13_cosetGeneratorStep_4731 s
  · exact g32p_row13_cosetGeneratorStep_4732 s
  · exact g32p_row13_cosetGeneratorStep_4733 s
  · exact g32p_row13_cosetGeneratorStep_4734 s
  · exact g32p_row13_cosetGeneratorStep_4735 s

theorem g32p_row13_cosetBranchBlock_0295 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 295 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 295 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 295 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4720 s
  · exact g32p_row13_cosetBranchStep_4721 s
  · exact g32p_row13_cosetBranchStep_4722 s
  · exact g32p_row13_cosetBranchStep_4723 s
  · exact g32p_row13_cosetBranchStep_4724 s
  · exact g32p_row13_cosetBranchStep_4725 s
  · exact g32p_row13_cosetBranchStep_4726 s
  · exact g32p_row13_cosetBranchStep_4727 s
  · exact g32p_row13_cosetBranchStep_4728 s
  · exact g32p_row13_cosetBranchStep_4729 s
  · exact g32p_row13_cosetBranchStep_4730 s
  · exact g32p_row13_cosetBranchStep_4731 s
  · exact g32p_row13_cosetBranchStep_4732 s
  · exact g32p_row13_cosetBranchStep_4733 s
  · exact g32p_row13_cosetBranchStep_4734 s
  · exact g32p_row13_cosetBranchStep_4735 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4736 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4736) = g32p_row13_cosetRepresentatives 4736 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4736 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4736) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4736))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4736)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4736 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4736) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4736))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4736)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4737 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4737) = g32p_row13_cosetRepresentatives 4737 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4737 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4737) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4737))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4737)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4737 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4737) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4737))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4737)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4738 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4738) = g32p_row13_cosetRepresentatives 4738 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4738 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4738) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4738))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4738)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4738 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4738) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4738))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4738)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4739 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4739) = g32p_row13_cosetRepresentatives 4739 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4739 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4739) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4739))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4739)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4739 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4739) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4739))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4739)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4740 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4740) = g32p_row13_cosetRepresentatives 4740 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4740 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4740) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4740))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4740)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4740 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4740) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4740))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4740)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4741 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4741) = g32p_row13_cosetRepresentatives 4741 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4741 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4741) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4741))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4741)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4741 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4741) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4741))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4741)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4742 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4742) = g32p_row13_cosetRepresentatives 4742 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4742 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4742) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4742))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4742)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4742 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4742) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4742))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4742)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4743 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4743) = g32p_row13_cosetRepresentatives 4743 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4743 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4743) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4743))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4743)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4743 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4743) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4743))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4743)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4744 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4744) = g32p_row13_cosetRepresentatives 4744 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4744 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4744) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4744))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4744)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4744 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4744) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4744))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4744)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4745 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4745) = g32p_row13_cosetRepresentatives 4745 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4745 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4745) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4745))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4745)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4745 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4745) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4745))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4745)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4746 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4746) = g32p_row13_cosetRepresentatives 4746 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4746 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4746) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4746))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4746)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4746 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4746) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4746))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4746)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4747 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4747) = g32p_row13_cosetRepresentatives 4747 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4747 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4747) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4747))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4747)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4747 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4747) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4747))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4747)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4748 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4748) = g32p_row13_cosetRepresentatives 4748 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4748 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4748) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4748))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4748)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4748 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4748) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4748))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4748)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4749 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4749) = g32p_row13_cosetRepresentatives 4749 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4749 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4749) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4749))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4749)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4749 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4749) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4749))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4749)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4750 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4750) = g32p_row13_cosetRepresentatives 4750 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4750 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4750) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4750))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4750)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4750 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4750) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4750))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4750)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4751 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4751) = g32p_row13_cosetRepresentatives 4751 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4751 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4751) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4751))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4751)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4751 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4751) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4751))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4751)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0296 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 296 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 296 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4736
  · exact g32p_row13_cosetWord_4737
  · exact g32p_row13_cosetWord_4738
  · exact g32p_row13_cosetWord_4739
  · exact g32p_row13_cosetWord_4740
  · exact g32p_row13_cosetWord_4741
  · exact g32p_row13_cosetWord_4742
  · exact g32p_row13_cosetWord_4743
  · exact g32p_row13_cosetWord_4744
  · exact g32p_row13_cosetWord_4745
  · exact g32p_row13_cosetWord_4746
  · exact g32p_row13_cosetWord_4747
  · exact g32p_row13_cosetWord_4748
  · exact g32p_row13_cosetWord_4749
  · exact g32p_row13_cosetWord_4750
  · exact g32p_row13_cosetWord_4751

theorem g32p_row13_cosetGeneratorBlock_0296 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 296 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 296 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 296 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4736 s
  · exact g32p_row13_cosetGeneratorStep_4737 s
  · exact g32p_row13_cosetGeneratorStep_4738 s
  · exact g32p_row13_cosetGeneratorStep_4739 s
  · exact g32p_row13_cosetGeneratorStep_4740 s
  · exact g32p_row13_cosetGeneratorStep_4741 s
  · exact g32p_row13_cosetGeneratorStep_4742 s
  · exact g32p_row13_cosetGeneratorStep_4743 s
  · exact g32p_row13_cosetGeneratorStep_4744 s
  · exact g32p_row13_cosetGeneratorStep_4745 s
  · exact g32p_row13_cosetGeneratorStep_4746 s
  · exact g32p_row13_cosetGeneratorStep_4747 s
  · exact g32p_row13_cosetGeneratorStep_4748 s
  · exact g32p_row13_cosetGeneratorStep_4749 s
  · exact g32p_row13_cosetGeneratorStep_4750 s
  · exact g32p_row13_cosetGeneratorStep_4751 s

theorem g32p_row13_cosetBranchBlock_0296 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 296 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 296 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 296 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4736 s
  · exact g32p_row13_cosetBranchStep_4737 s
  · exact g32p_row13_cosetBranchStep_4738 s
  · exact g32p_row13_cosetBranchStep_4739 s
  · exact g32p_row13_cosetBranchStep_4740 s
  · exact g32p_row13_cosetBranchStep_4741 s
  · exact g32p_row13_cosetBranchStep_4742 s
  · exact g32p_row13_cosetBranchStep_4743 s
  · exact g32p_row13_cosetBranchStep_4744 s
  · exact g32p_row13_cosetBranchStep_4745 s
  · exact g32p_row13_cosetBranchStep_4746 s
  · exact g32p_row13_cosetBranchStep_4747 s
  · exact g32p_row13_cosetBranchStep_4748 s
  · exact g32p_row13_cosetBranchStep_4749 s
  · exact g32p_row13_cosetBranchStep_4750 s
  · exact g32p_row13_cosetBranchStep_4751 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4752 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4752) = g32p_row13_cosetRepresentatives 4752 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4752 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4752) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4752))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4752)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4752 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4752) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4752))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4752)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4753 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4753) = g32p_row13_cosetRepresentatives 4753 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4753 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4753) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4753))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4753)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4753 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4753) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4753))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4753)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4754 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4754) = g32p_row13_cosetRepresentatives 4754 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4754 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4754) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4754))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4754)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4754 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4754) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4754))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4754)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4755 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4755) = g32p_row13_cosetRepresentatives 4755 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4755 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4755) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4755))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4755)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4755 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4755) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4755))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4755)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4756 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4756) = g32p_row13_cosetRepresentatives 4756 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4756 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4756) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4756))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4756)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4756 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4756) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4756))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4756)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4757 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4757) = g32p_row13_cosetRepresentatives 4757 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4757 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4757) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4757))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4757)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4757 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4757) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4757))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4757)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4758 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4758) = g32p_row13_cosetRepresentatives 4758 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4758 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4758) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4758))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4758)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4758 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4758) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4758))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4758)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4759 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4759) = g32p_row13_cosetRepresentatives 4759 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4759 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4759) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4759))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4759)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4759 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4759) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4759))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4759)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4760 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4760) = g32p_row13_cosetRepresentatives 4760 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4760 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4760) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4760))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4760)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4760 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4760) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4760))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4760)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4761 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4761) = g32p_row13_cosetRepresentatives 4761 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4761 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4761) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4761))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4761)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4761 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4761) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4761))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4761)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4762 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4762) = g32p_row13_cosetRepresentatives 4762 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4762 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4762) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4762))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4762)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4762 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4762) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4762))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4762)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4763 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4763) = g32p_row13_cosetRepresentatives 4763 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4763 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4763) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4763))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4763)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4763 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4763) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4763))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4763)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4764 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4764) = g32p_row13_cosetRepresentatives 4764 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4764 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4764) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4764))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4764)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4764 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4764) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4764))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4764)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4765 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4765) = g32p_row13_cosetRepresentatives 4765 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4765 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4765) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4765))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4765)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4765 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4765) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4765))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4765)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4766 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4766) = g32p_row13_cosetRepresentatives 4766 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4766 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4766) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4766))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4766)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4766 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4766) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4766))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4766)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4767 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4767) = g32p_row13_cosetRepresentatives 4767 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4767 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4767) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4767))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4767)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4767 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4767) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4767))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4767)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0297 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 297 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 297 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4752
  · exact g32p_row13_cosetWord_4753
  · exact g32p_row13_cosetWord_4754
  · exact g32p_row13_cosetWord_4755
  · exact g32p_row13_cosetWord_4756
  · exact g32p_row13_cosetWord_4757
  · exact g32p_row13_cosetWord_4758
  · exact g32p_row13_cosetWord_4759
  · exact g32p_row13_cosetWord_4760
  · exact g32p_row13_cosetWord_4761
  · exact g32p_row13_cosetWord_4762
  · exact g32p_row13_cosetWord_4763
  · exact g32p_row13_cosetWord_4764
  · exact g32p_row13_cosetWord_4765
  · exact g32p_row13_cosetWord_4766
  · exact g32p_row13_cosetWord_4767

theorem g32p_row13_cosetGeneratorBlock_0297 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 297 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 297 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 297 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4752 s
  · exact g32p_row13_cosetGeneratorStep_4753 s
  · exact g32p_row13_cosetGeneratorStep_4754 s
  · exact g32p_row13_cosetGeneratorStep_4755 s
  · exact g32p_row13_cosetGeneratorStep_4756 s
  · exact g32p_row13_cosetGeneratorStep_4757 s
  · exact g32p_row13_cosetGeneratorStep_4758 s
  · exact g32p_row13_cosetGeneratorStep_4759 s
  · exact g32p_row13_cosetGeneratorStep_4760 s
  · exact g32p_row13_cosetGeneratorStep_4761 s
  · exact g32p_row13_cosetGeneratorStep_4762 s
  · exact g32p_row13_cosetGeneratorStep_4763 s
  · exact g32p_row13_cosetGeneratorStep_4764 s
  · exact g32p_row13_cosetGeneratorStep_4765 s
  · exact g32p_row13_cosetGeneratorStep_4766 s
  · exact g32p_row13_cosetGeneratorStep_4767 s

theorem g32p_row13_cosetBranchBlock_0297 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 297 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 297 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 297 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4752 s
  · exact g32p_row13_cosetBranchStep_4753 s
  · exact g32p_row13_cosetBranchStep_4754 s
  · exact g32p_row13_cosetBranchStep_4755 s
  · exact g32p_row13_cosetBranchStep_4756 s
  · exact g32p_row13_cosetBranchStep_4757 s
  · exact g32p_row13_cosetBranchStep_4758 s
  · exact g32p_row13_cosetBranchStep_4759 s
  · exact g32p_row13_cosetBranchStep_4760 s
  · exact g32p_row13_cosetBranchStep_4761 s
  · exact g32p_row13_cosetBranchStep_4762 s
  · exact g32p_row13_cosetBranchStep_4763 s
  · exact g32p_row13_cosetBranchStep_4764 s
  · exact g32p_row13_cosetBranchStep_4765 s
  · exact g32p_row13_cosetBranchStep_4766 s
  · exact g32p_row13_cosetBranchStep_4767 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4768 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4768) = g32p_row13_cosetRepresentatives 4768 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4768 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4768) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4768))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4768)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4768 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4768) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4768))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4768)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4769 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4769) = g32p_row13_cosetRepresentatives 4769 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4769 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4769) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4769))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4769)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4769 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4769) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4769))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4769)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4770 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4770) = g32p_row13_cosetRepresentatives 4770 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4770 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4770) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4770))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4770)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4770 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4770) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4770))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4770)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4771 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4771) = g32p_row13_cosetRepresentatives 4771 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4771 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4771) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4771))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4771)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4771 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4771) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4771))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4771)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4772 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4772) = g32p_row13_cosetRepresentatives 4772 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4772 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4772) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4772))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4772)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4772 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4772) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4772))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4772)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4773 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4773) = g32p_row13_cosetRepresentatives 4773 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4773 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4773) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4773))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4773)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4773 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4773) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4773))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4773)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4774 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4774) = g32p_row13_cosetRepresentatives 4774 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4774 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4774) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4774))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4774)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4774 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4774) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4774))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4774)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4775 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4775) = g32p_row13_cosetRepresentatives 4775 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4775 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4775) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4775))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4775)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4775 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4775) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4775))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4775)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4776 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4776) = g32p_row13_cosetRepresentatives 4776 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4776 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4776) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4776))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4776)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4776 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4776) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4776))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4776)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4777 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4777) = g32p_row13_cosetRepresentatives 4777 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4777 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4777) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4777))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4777)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4777 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4777) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4777))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4777)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4778 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4778) = g32p_row13_cosetRepresentatives 4778 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4778 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4778) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4778))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4778)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4778 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4778) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4778))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4778)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4779 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4779) = g32p_row13_cosetRepresentatives 4779 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4779 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4779) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4779))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4779)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4779 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4779) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4779))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4779)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4780 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4780) = g32p_row13_cosetRepresentatives 4780 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4780 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4780) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4780))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4780)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4780 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4780) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4780))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4780)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4781 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4781) = g32p_row13_cosetRepresentatives 4781 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4781 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4781) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4781))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4781)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4781 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4781) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4781))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4781)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4782 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4782) = g32p_row13_cosetRepresentatives 4782 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4782 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4782) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4782))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4782)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4782 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4782) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4782))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4782)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4783 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4783) = g32p_row13_cosetRepresentatives 4783 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4783 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4783) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4783))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4783)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4783 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4783) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4783))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4783)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0298 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 298 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 298 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4768
  · exact g32p_row13_cosetWord_4769
  · exact g32p_row13_cosetWord_4770
  · exact g32p_row13_cosetWord_4771
  · exact g32p_row13_cosetWord_4772
  · exact g32p_row13_cosetWord_4773
  · exact g32p_row13_cosetWord_4774
  · exact g32p_row13_cosetWord_4775
  · exact g32p_row13_cosetWord_4776
  · exact g32p_row13_cosetWord_4777
  · exact g32p_row13_cosetWord_4778
  · exact g32p_row13_cosetWord_4779
  · exact g32p_row13_cosetWord_4780
  · exact g32p_row13_cosetWord_4781
  · exact g32p_row13_cosetWord_4782
  · exact g32p_row13_cosetWord_4783

theorem g32p_row13_cosetGeneratorBlock_0298 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 298 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 298 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 298 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4768 s
  · exact g32p_row13_cosetGeneratorStep_4769 s
  · exact g32p_row13_cosetGeneratorStep_4770 s
  · exact g32p_row13_cosetGeneratorStep_4771 s
  · exact g32p_row13_cosetGeneratorStep_4772 s
  · exact g32p_row13_cosetGeneratorStep_4773 s
  · exact g32p_row13_cosetGeneratorStep_4774 s
  · exact g32p_row13_cosetGeneratorStep_4775 s
  · exact g32p_row13_cosetGeneratorStep_4776 s
  · exact g32p_row13_cosetGeneratorStep_4777 s
  · exact g32p_row13_cosetGeneratorStep_4778 s
  · exact g32p_row13_cosetGeneratorStep_4779 s
  · exact g32p_row13_cosetGeneratorStep_4780 s
  · exact g32p_row13_cosetGeneratorStep_4781 s
  · exact g32p_row13_cosetGeneratorStep_4782 s
  · exact g32p_row13_cosetGeneratorStep_4783 s

theorem g32p_row13_cosetBranchBlock_0298 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 298 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 298 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 298 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4768 s
  · exact g32p_row13_cosetBranchStep_4769 s
  · exact g32p_row13_cosetBranchStep_4770 s
  · exact g32p_row13_cosetBranchStep_4771 s
  · exact g32p_row13_cosetBranchStep_4772 s
  · exact g32p_row13_cosetBranchStep_4773 s
  · exact g32p_row13_cosetBranchStep_4774 s
  · exact g32p_row13_cosetBranchStep_4775 s
  · exact g32p_row13_cosetBranchStep_4776 s
  · exact g32p_row13_cosetBranchStep_4777 s
  · exact g32p_row13_cosetBranchStep_4778 s
  · exact g32p_row13_cosetBranchStep_4779 s
  · exact g32p_row13_cosetBranchStep_4780 s
  · exact g32p_row13_cosetBranchStep_4781 s
  · exact g32p_row13_cosetBranchStep_4782 s
  · exact g32p_row13_cosetBranchStep_4783 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4784 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4784) = g32p_row13_cosetRepresentatives 4784 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4784 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4784) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4784))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4784)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4784 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4784) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4784))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4784)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4785 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4785) = g32p_row13_cosetRepresentatives 4785 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4785 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4785) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4785))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4785)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4785 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4785) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4785))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4785)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4786 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4786) = g32p_row13_cosetRepresentatives 4786 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4786 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4786) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4786))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4786)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4786 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4786) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4786))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4786)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4787 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4787) = g32p_row13_cosetRepresentatives 4787 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4787 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4787) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4787))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4787)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4787 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4787) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4787))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4787)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4788 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4788) = g32p_row13_cosetRepresentatives 4788 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4788 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4788) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4788))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4788)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4788 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4788) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4788))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4788)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4789 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4789) = g32p_row13_cosetRepresentatives 4789 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4789 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4789) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4789))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4789)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4789 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4789) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4789))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4789)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4790 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4790) = g32p_row13_cosetRepresentatives 4790 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4790 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4790) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4790))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4790)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4790 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4790) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4790))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4790)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4791 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4791) = g32p_row13_cosetRepresentatives 4791 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4791 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4791) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4791))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4791)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4791 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4791) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4791))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4791)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4792 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4792) = g32p_row13_cosetRepresentatives 4792 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4792 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4792) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4792))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4792)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4792 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4792) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4792))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4792)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4793 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4793) = g32p_row13_cosetRepresentatives 4793 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4793 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4793) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4793))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4793)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4793 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4793) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4793))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4793)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4794 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4794) = g32p_row13_cosetRepresentatives 4794 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4794 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4794) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4794))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4794)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4794 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4794) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4794))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4794)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4795 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4795) = g32p_row13_cosetRepresentatives 4795 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4795 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4795) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4795))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4795)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4795 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4795) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4795))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4795)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4796 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4796) = g32p_row13_cosetRepresentatives 4796 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4796 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4796) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4796))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4796)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4796 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4796) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4796))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4796)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4797 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4797) = g32p_row13_cosetRepresentatives 4797 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4797 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4797) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4797))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4797)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4797 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4797) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4797))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4797)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4798 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4798) = g32p_row13_cosetRepresentatives 4798 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4798 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4798) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4798))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4798)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4798 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4798) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4798))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4798)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4799 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4799) = g32p_row13_cosetRepresentatives 4799 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4799 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4799) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4799))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4799)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4799 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4799) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4799))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4799)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0299 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 299 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 299 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4784
  · exact g32p_row13_cosetWord_4785
  · exact g32p_row13_cosetWord_4786
  · exact g32p_row13_cosetWord_4787
  · exact g32p_row13_cosetWord_4788
  · exact g32p_row13_cosetWord_4789
  · exact g32p_row13_cosetWord_4790
  · exact g32p_row13_cosetWord_4791
  · exact g32p_row13_cosetWord_4792
  · exact g32p_row13_cosetWord_4793
  · exact g32p_row13_cosetWord_4794
  · exact g32p_row13_cosetWord_4795
  · exact g32p_row13_cosetWord_4796
  · exact g32p_row13_cosetWord_4797
  · exact g32p_row13_cosetWord_4798
  · exact g32p_row13_cosetWord_4799

theorem g32p_row13_cosetGeneratorBlock_0299 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 299 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 299 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 299 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4784 s
  · exact g32p_row13_cosetGeneratorStep_4785 s
  · exact g32p_row13_cosetGeneratorStep_4786 s
  · exact g32p_row13_cosetGeneratorStep_4787 s
  · exact g32p_row13_cosetGeneratorStep_4788 s
  · exact g32p_row13_cosetGeneratorStep_4789 s
  · exact g32p_row13_cosetGeneratorStep_4790 s
  · exact g32p_row13_cosetGeneratorStep_4791 s
  · exact g32p_row13_cosetGeneratorStep_4792 s
  · exact g32p_row13_cosetGeneratorStep_4793 s
  · exact g32p_row13_cosetGeneratorStep_4794 s
  · exact g32p_row13_cosetGeneratorStep_4795 s
  · exact g32p_row13_cosetGeneratorStep_4796 s
  · exact g32p_row13_cosetGeneratorStep_4797 s
  · exact g32p_row13_cosetGeneratorStep_4798 s
  · exact g32p_row13_cosetGeneratorStep_4799 s

theorem g32p_row13_cosetBranchBlock_0299 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 299 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 299 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 299 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4784 s
  · exact g32p_row13_cosetBranchStep_4785 s
  · exact g32p_row13_cosetBranchStep_4786 s
  · exact g32p_row13_cosetBranchStep_4787 s
  · exact g32p_row13_cosetBranchStep_4788 s
  · exact g32p_row13_cosetBranchStep_4789 s
  · exact g32p_row13_cosetBranchStep_4790 s
  · exact g32p_row13_cosetBranchStep_4791 s
  · exact g32p_row13_cosetBranchStep_4792 s
  · exact g32p_row13_cosetBranchStep_4793 s
  · exact g32p_row13_cosetBranchStep_4794 s
  · exact g32p_row13_cosetBranchStep_4795 s
  · exact g32p_row13_cosetBranchStep_4796 s
  · exact g32p_row13_cosetBranchStep_4797 s
  · exact g32p_row13_cosetBranchStep_4798 s
  · exact g32p_row13_cosetBranchStep_4799 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4800 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4800) = g32p_row13_cosetRepresentatives 4800 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4800 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4800) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4800))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4800)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4800 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4800) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4800))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4800)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4801 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4801) = g32p_row13_cosetRepresentatives 4801 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4801 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4801) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4801))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4801)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4801 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4801) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4801))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4801)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4802 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4802) = g32p_row13_cosetRepresentatives 4802 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4802 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4802) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4802))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4802)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4802 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4802) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4802))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4802)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4803 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4803) = g32p_row13_cosetRepresentatives 4803 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4803 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4803) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4803))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4803)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4803 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4803) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4803))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4803)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4804 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4804) = g32p_row13_cosetRepresentatives 4804 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4804 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4804) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4804))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4804)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4804 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4804) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4804))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4804)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4805 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4805) = g32p_row13_cosetRepresentatives 4805 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4805 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4805) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4805))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4805)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4805 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4805) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4805))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4805)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4806 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4806) = g32p_row13_cosetRepresentatives 4806 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4806 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4806) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4806))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4806)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4806 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4806) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4806))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4806)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4807 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4807) = g32p_row13_cosetRepresentatives 4807 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4807 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4807) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4807))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4807)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4807 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4807) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4807))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4807)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4808 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4808) = g32p_row13_cosetRepresentatives 4808 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4808 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4808) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4808))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4808)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4808 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4808) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4808))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4808)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4809 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4809) = g32p_row13_cosetRepresentatives 4809 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4809 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4809) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4809))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4809)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4809 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4809) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4809))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4809)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4810 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4810) = g32p_row13_cosetRepresentatives 4810 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4810 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4810) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4810))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4810)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4810 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4810) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4810))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4810)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4811 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4811) = g32p_row13_cosetRepresentatives 4811 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4811 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4811) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4811))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4811)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4811 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4811) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4811))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4811)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4812 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4812) = g32p_row13_cosetRepresentatives 4812 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4812 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4812) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4812))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4812)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4812 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4812) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4812))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4812)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4813 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4813) = g32p_row13_cosetRepresentatives 4813 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4813 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4813) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4813))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4813)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4813 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4813) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4813))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4813)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4814 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4814) = g32p_row13_cosetRepresentatives 4814 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4814 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4814) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4814))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4814)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4814 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4814) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4814))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4814)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4815 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4815) = g32p_row13_cosetRepresentatives 4815 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4815 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4815) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4815))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4815)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4815 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4815) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4815))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4815)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0300 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 300 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 300 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4800
  · exact g32p_row13_cosetWord_4801
  · exact g32p_row13_cosetWord_4802
  · exact g32p_row13_cosetWord_4803
  · exact g32p_row13_cosetWord_4804
  · exact g32p_row13_cosetWord_4805
  · exact g32p_row13_cosetWord_4806
  · exact g32p_row13_cosetWord_4807
  · exact g32p_row13_cosetWord_4808
  · exact g32p_row13_cosetWord_4809
  · exact g32p_row13_cosetWord_4810
  · exact g32p_row13_cosetWord_4811
  · exact g32p_row13_cosetWord_4812
  · exact g32p_row13_cosetWord_4813
  · exact g32p_row13_cosetWord_4814
  · exact g32p_row13_cosetWord_4815

theorem g32p_row13_cosetGeneratorBlock_0300 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 300 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 300 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 300 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4800 s
  · exact g32p_row13_cosetGeneratorStep_4801 s
  · exact g32p_row13_cosetGeneratorStep_4802 s
  · exact g32p_row13_cosetGeneratorStep_4803 s
  · exact g32p_row13_cosetGeneratorStep_4804 s
  · exact g32p_row13_cosetGeneratorStep_4805 s
  · exact g32p_row13_cosetGeneratorStep_4806 s
  · exact g32p_row13_cosetGeneratorStep_4807 s
  · exact g32p_row13_cosetGeneratorStep_4808 s
  · exact g32p_row13_cosetGeneratorStep_4809 s
  · exact g32p_row13_cosetGeneratorStep_4810 s
  · exact g32p_row13_cosetGeneratorStep_4811 s
  · exact g32p_row13_cosetGeneratorStep_4812 s
  · exact g32p_row13_cosetGeneratorStep_4813 s
  · exact g32p_row13_cosetGeneratorStep_4814 s
  · exact g32p_row13_cosetGeneratorStep_4815 s

theorem g32p_row13_cosetBranchBlock_0300 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 300 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 300 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 300 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4800 s
  · exact g32p_row13_cosetBranchStep_4801 s
  · exact g32p_row13_cosetBranchStep_4802 s
  · exact g32p_row13_cosetBranchStep_4803 s
  · exact g32p_row13_cosetBranchStep_4804 s
  · exact g32p_row13_cosetBranchStep_4805 s
  · exact g32p_row13_cosetBranchStep_4806 s
  · exact g32p_row13_cosetBranchStep_4807 s
  · exact g32p_row13_cosetBranchStep_4808 s
  · exact g32p_row13_cosetBranchStep_4809 s
  · exact g32p_row13_cosetBranchStep_4810 s
  · exact g32p_row13_cosetBranchStep_4811 s
  · exact g32p_row13_cosetBranchStep_4812 s
  · exact g32p_row13_cosetBranchStep_4813 s
  · exact g32p_row13_cosetBranchStep_4814 s
  · exact g32p_row13_cosetBranchStep_4815 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4816 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4816) = g32p_row13_cosetRepresentatives 4816 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4816 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4816) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4816))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4816)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4816 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4816) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4816))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4816)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4817 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4817) = g32p_row13_cosetRepresentatives 4817 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4817 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4817) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4817))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4817)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4817 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4817) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4817))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4817)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4818 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4818) = g32p_row13_cosetRepresentatives 4818 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4818 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4818) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4818))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4818)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4818 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4818) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4818))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4818)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4819 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4819) = g32p_row13_cosetRepresentatives 4819 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4819 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4819) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4819))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4819)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4819 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4819) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4819))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4819)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4820 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4820) = g32p_row13_cosetRepresentatives 4820 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4820 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4820) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4820))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4820)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4820 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4820) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4820))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4820)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4821 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4821) = g32p_row13_cosetRepresentatives 4821 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4821 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4821) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4821))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4821)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4821 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4821) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4821))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4821)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4822 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4822) = g32p_row13_cosetRepresentatives 4822 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4822 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4822) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4822))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4822)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4822 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4822) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4822))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4822)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4823 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4823) = g32p_row13_cosetRepresentatives 4823 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4823 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4823) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4823))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4823)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4823 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4823) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4823))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4823)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4824 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4824) = g32p_row13_cosetRepresentatives 4824 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4824 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4824) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4824))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4824)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4824 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4824) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4824))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4824)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4825 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4825) = g32p_row13_cosetRepresentatives 4825 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4825 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4825) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4825))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4825)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4825 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4825) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4825))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4825)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4826 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4826) = g32p_row13_cosetRepresentatives 4826 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4826 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4826) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4826))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4826)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4826 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4826) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4826))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4826)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4827 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4827) = g32p_row13_cosetRepresentatives 4827 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4827 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4827) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4827))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4827)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4827 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4827) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4827))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4827)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4828 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4828) = g32p_row13_cosetRepresentatives 4828 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4828 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4828) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4828))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4828)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4828 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4828) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4828))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4828)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4829 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4829) = g32p_row13_cosetRepresentatives 4829 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4829 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4829) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4829))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4829)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4829 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4829) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4829))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4829)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4830 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4830) = g32p_row13_cosetRepresentatives 4830 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4830 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4830) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4830))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4830)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4830 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4830) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4830))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4830)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4831 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4831) = g32p_row13_cosetRepresentatives 4831 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4831 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4831) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4831))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4831)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4831 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4831) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4831))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4831)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0301 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 301 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 301 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4816
  · exact g32p_row13_cosetWord_4817
  · exact g32p_row13_cosetWord_4818
  · exact g32p_row13_cosetWord_4819
  · exact g32p_row13_cosetWord_4820
  · exact g32p_row13_cosetWord_4821
  · exact g32p_row13_cosetWord_4822
  · exact g32p_row13_cosetWord_4823
  · exact g32p_row13_cosetWord_4824
  · exact g32p_row13_cosetWord_4825
  · exact g32p_row13_cosetWord_4826
  · exact g32p_row13_cosetWord_4827
  · exact g32p_row13_cosetWord_4828
  · exact g32p_row13_cosetWord_4829
  · exact g32p_row13_cosetWord_4830
  · exact g32p_row13_cosetWord_4831

theorem g32p_row13_cosetGeneratorBlock_0301 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 301 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 301 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 301 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4816 s
  · exact g32p_row13_cosetGeneratorStep_4817 s
  · exact g32p_row13_cosetGeneratorStep_4818 s
  · exact g32p_row13_cosetGeneratorStep_4819 s
  · exact g32p_row13_cosetGeneratorStep_4820 s
  · exact g32p_row13_cosetGeneratorStep_4821 s
  · exact g32p_row13_cosetGeneratorStep_4822 s
  · exact g32p_row13_cosetGeneratorStep_4823 s
  · exact g32p_row13_cosetGeneratorStep_4824 s
  · exact g32p_row13_cosetGeneratorStep_4825 s
  · exact g32p_row13_cosetGeneratorStep_4826 s
  · exact g32p_row13_cosetGeneratorStep_4827 s
  · exact g32p_row13_cosetGeneratorStep_4828 s
  · exact g32p_row13_cosetGeneratorStep_4829 s
  · exact g32p_row13_cosetGeneratorStep_4830 s
  · exact g32p_row13_cosetGeneratorStep_4831 s

theorem g32p_row13_cosetBranchBlock_0301 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 301 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 301 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 301 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4816 s
  · exact g32p_row13_cosetBranchStep_4817 s
  · exact g32p_row13_cosetBranchStep_4818 s
  · exact g32p_row13_cosetBranchStep_4819 s
  · exact g32p_row13_cosetBranchStep_4820 s
  · exact g32p_row13_cosetBranchStep_4821 s
  · exact g32p_row13_cosetBranchStep_4822 s
  · exact g32p_row13_cosetBranchStep_4823 s
  · exact g32p_row13_cosetBranchStep_4824 s
  · exact g32p_row13_cosetBranchStep_4825 s
  · exact g32p_row13_cosetBranchStep_4826 s
  · exact g32p_row13_cosetBranchStep_4827 s
  · exact g32p_row13_cosetBranchStep_4828 s
  · exact g32p_row13_cosetBranchStep_4829 s
  · exact g32p_row13_cosetBranchStep_4830 s
  · exact g32p_row13_cosetBranchStep_4831 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4832 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4832) = g32p_row13_cosetRepresentatives 4832 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4832 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4832) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4832))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4832)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4832 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4832) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4832))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4832)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4833 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4833) = g32p_row13_cosetRepresentatives 4833 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4833 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4833) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4833))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4833)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4833 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4833) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4833))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4833)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4834 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4834) = g32p_row13_cosetRepresentatives 4834 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4834 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4834) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4834))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4834)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4834 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4834) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4834))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4834)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4835 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4835) = g32p_row13_cosetRepresentatives 4835 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4835 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4835) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4835))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4835)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4835 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4835) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4835))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4835)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4836 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4836) = g32p_row13_cosetRepresentatives 4836 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4836 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4836) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4836))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4836)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4836 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4836) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4836))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4836)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4837 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4837) = g32p_row13_cosetRepresentatives 4837 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4837 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4837) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4837))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4837)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4837 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4837) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4837))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4837)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4838 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4838) = g32p_row13_cosetRepresentatives 4838 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4838 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4838) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4838))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4838)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4838 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4838) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4838))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4838)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4839 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4839) = g32p_row13_cosetRepresentatives 4839 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4839 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4839) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4839))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4839)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4839 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4839) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4839))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4839)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4840 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4840) = g32p_row13_cosetRepresentatives 4840 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4840 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4840) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4840))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4840)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4840 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4840) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4840))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4840)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4841 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4841) = g32p_row13_cosetRepresentatives 4841 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4841 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4841) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4841))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4841)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4841 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4841) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4841))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4841)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4842 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4842) = g32p_row13_cosetRepresentatives 4842 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4842 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4842) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4842))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4842)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4842 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4842) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4842))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4842)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4843 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4843) = g32p_row13_cosetRepresentatives 4843 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4843 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4843) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4843))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4843)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4843 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4843) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4843))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4843)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4844 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4844) = g32p_row13_cosetRepresentatives 4844 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4844 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4844) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4844))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4844)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4844 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4844) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4844))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4844)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4845 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4845) = g32p_row13_cosetRepresentatives 4845 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4845 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4845) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4845))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4845)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4845 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4845) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4845))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4845)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4846 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4846) = g32p_row13_cosetRepresentatives 4846 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4846 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4846) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4846))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4846)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4846 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4846) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4846))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4846)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4847 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4847) = g32p_row13_cosetRepresentatives 4847 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4847 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4847) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4847))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4847)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4847 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4847) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4847))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4847)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0302 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 302 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 302 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4832
  · exact g32p_row13_cosetWord_4833
  · exact g32p_row13_cosetWord_4834
  · exact g32p_row13_cosetWord_4835
  · exact g32p_row13_cosetWord_4836
  · exact g32p_row13_cosetWord_4837
  · exact g32p_row13_cosetWord_4838
  · exact g32p_row13_cosetWord_4839
  · exact g32p_row13_cosetWord_4840
  · exact g32p_row13_cosetWord_4841
  · exact g32p_row13_cosetWord_4842
  · exact g32p_row13_cosetWord_4843
  · exact g32p_row13_cosetWord_4844
  · exact g32p_row13_cosetWord_4845
  · exact g32p_row13_cosetWord_4846
  · exact g32p_row13_cosetWord_4847

theorem g32p_row13_cosetGeneratorBlock_0302 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 302 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 302 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 302 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4832 s
  · exact g32p_row13_cosetGeneratorStep_4833 s
  · exact g32p_row13_cosetGeneratorStep_4834 s
  · exact g32p_row13_cosetGeneratorStep_4835 s
  · exact g32p_row13_cosetGeneratorStep_4836 s
  · exact g32p_row13_cosetGeneratorStep_4837 s
  · exact g32p_row13_cosetGeneratorStep_4838 s
  · exact g32p_row13_cosetGeneratorStep_4839 s
  · exact g32p_row13_cosetGeneratorStep_4840 s
  · exact g32p_row13_cosetGeneratorStep_4841 s
  · exact g32p_row13_cosetGeneratorStep_4842 s
  · exact g32p_row13_cosetGeneratorStep_4843 s
  · exact g32p_row13_cosetGeneratorStep_4844 s
  · exact g32p_row13_cosetGeneratorStep_4845 s
  · exact g32p_row13_cosetGeneratorStep_4846 s
  · exact g32p_row13_cosetGeneratorStep_4847 s

theorem g32p_row13_cosetBranchBlock_0302 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 302 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 302 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 302 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4832 s
  · exact g32p_row13_cosetBranchStep_4833 s
  · exact g32p_row13_cosetBranchStep_4834 s
  · exact g32p_row13_cosetBranchStep_4835 s
  · exact g32p_row13_cosetBranchStep_4836 s
  · exact g32p_row13_cosetBranchStep_4837 s
  · exact g32p_row13_cosetBranchStep_4838 s
  · exact g32p_row13_cosetBranchStep_4839 s
  · exact g32p_row13_cosetBranchStep_4840 s
  · exact g32p_row13_cosetBranchStep_4841 s
  · exact g32p_row13_cosetBranchStep_4842 s
  · exact g32p_row13_cosetBranchStep_4843 s
  · exact g32p_row13_cosetBranchStep_4844 s
  · exact g32p_row13_cosetBranchStep_4845 s
  · exact g32p_row13_cosetBranchStep_4846 s
  · exact g32p_row13_cosetBranchStep_4847 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4848 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4848) = g32p_row13_cosetRepresentatives 4848 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4848 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4848) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4848))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4848)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4848 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4848) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4848))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4848)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4849 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4849) = g32p_row13_cosetRepresentatives 4849 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4849 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4849) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4849))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4849)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4849 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4849) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4849))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4849)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4850 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4850) = g32p_row13_cosetRepresentatives 4850 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4850 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4850) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4850))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4850)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4850 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4850) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4850))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4850)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4851 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4851) = g32p_row13_cosetRepresentatives 4851 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4851 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4851) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4851))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4851)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4851 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4851) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4851))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4851)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4852 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4852) = g32p_row13_cosetRepresentatives 4852 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4852 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4852) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4852))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4852)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4852 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4852) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4852))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4852)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4853 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4853) = g32p_row13_cosetRepresentatives 4853 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4853 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4853) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4853))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4853)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4853 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4853) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4853))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4853)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4854 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4854) = g32p_row13_cosetRepresentatives 4854 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4854 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4854) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4854))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4854)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4854 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4854) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4854))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4854)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4855 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4855) = g32p_row13_cosetRepresentatives 4855 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4855 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4855) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4855))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4855)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4855 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4855) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4855))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4855)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4856 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4856) = g32p_row13_cosetRepresentatives 4856 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4856 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4856) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4856))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4856)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4856 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4856) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4856))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4856)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4857 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4857) = g32p_row13_cosetRepresentatives 4857 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4857 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4857) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4857))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4857)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4857 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4857) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4857))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4857)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4858 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4858) = g32p_row13_cosetRepresentatives 4858 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4858 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4858) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4858))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4858)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4858 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4858) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4858))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4858)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4859 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4859) = g32p_row13_cosetRepresentatives 4859 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4859 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4859) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4859))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4859)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4859 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4859) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4859))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4859)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4860 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4860) = g32p_row13_cosetRepresentatives 4860 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4860 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4860) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4860))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4860)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4860 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4860) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4860))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4860)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4861 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4861) = g32p_row13_cosetRepresentatives 4861 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4861 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4861) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4861))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4861)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4861 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4861) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4861))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4861)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4862 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4862) = g32p_row13_cosetRepresentatives 4862 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4862 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4862) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4862))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4862)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4862 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4862) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4862))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4862)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4863 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4863) = g32p_row13_cosetRepresentatives 4863 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4863 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4863) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4863))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4863)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4863 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4863) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4863))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4863)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0303 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 303 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 303 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4848
  · exact g32p_row13_cosetWord_4849
  · exact g32p_row13_cosetWord_4850
  · exact g32p_row13_cosetWord_4851
  · exact g32p_row13_cosetWord_4852
  · exact g32p_row13_cosetWord_4853
  · exact g32p_row13_cosetWord_4854
  · exact g32p_row13_cosetWord_4855
  · exact g32p_row13_cosetWord_4856
  · exact g32p_row13_cosetWord_4857
  · exact g32p_row13_cosetWord_4858
  · exact g32p_row13_cosetWord_4859
  · exact g32p_row13_cosetWord_4860
  · exact g32p_row13_cosetWord_4861
  · exact g32p_row13_cosetWord_4862
  · exact g32p_row13_cosetWord_4863

theorem g32p_row13_cosetGeneratorBlock_0303 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 303 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 303 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 303 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4848 s
  · exact g32p_row13_cosetGeneratorStep_4849 s
  · exact g32p_row13_cosetGeneratorStep_4850 s
  · exact g32p_row13_cosetGeneratorStep_4851 s
  · exact g32p_row13_cosetGeneratorStep_4852 s
  · exact g32p_row13_cosetGeneratorStep_4853 s
  · exact g32p_row13_cosetGeneratorStep_4854 s
  · exact g32p_row13_cosetGeneratorStep_4855 s
  · exact g32p_row13_cosetGeneratorStep_4856 s
  · exact g32p_row13_cosetGeneratorStep_4857 s
  · exact g32p_row13_cosetGeneratorStep_4858 s
  · exact g32p_row13_cosetGeneratorStep_4859 s
  · exact g32p_row13_cosetGeneratorStep_4860 s
  · exact g32p_row13_cosetGeneratorStep_4861 s
  · exact g32p_row13_cosetGeneratorStep_4862 s
  · exact g32p_row13_cosetGeneratorStep_4863 s

theorem g32p_row13_cosetBranchBlock_0303 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 303 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 303 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 303 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4848 s
  · exact g32p_row13_cosetBranchStep_4849 s
  · exact g32p_row13_cosetBranchStep_4850 s
  · exact g32p_row13_cosetBranchStep_4851 s
  · exact g32p_row13_cosetBranchStep_4852 s
  · exact g32p_row13_cosetBranchStep_4853 s
  · exact g32p_row13_cosetBranchStep_4854 s
  · exact g32p_row13_cosetBranchStep_4855 s
  · exact g32p_row13_cosetBranchStep_4856 s
  · exact g32p_row13_cosetBranchStep_4857 s
  · exact g32p_row13_cosetBranchStep_4858 s
  · exact g32p_row13_cosetBranchStep_4859 s
  · exact g32p_row13_cosetBranchStep_4860 s
  · exact g32p_row13_cosetBranchStep_4861 s
  · exact g32p_row13_cosetBranchStep_4862 s
  · exact g32p_row13_cosetBranchStep_4863 s


end HodgeLean.Foundations.Program

end
