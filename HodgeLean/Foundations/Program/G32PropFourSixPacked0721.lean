import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0704
import HodgeLean.Foundations.Program.G32PropFourSixPacked0705
import HodgeLean.Foundations.Program.G32PropFourSixPacked0706
import HodgeLean.Foundations.Program.G32PropFourSixPacked0707
import HodgeLean.Foundations.Program.G32PropFourSixPacked0708
import HodgeLean.Foundations.Program.G32PropFourSixPacked0709
import HodgeLean.Foundations.Program.G32PropFourSixPacked0710
import HodgeLean.Foundations.Program.G32PropFourSixPacked0711
import HodgeLean.Foundations.Program.G32PropFourSixPacked0712
import HodgeLean.Foundations.Program.G32PropFourSixPacked0713
import HodgeLean.Foundations.Program.G32PropFourSixPacked0714
import HodgeLean.Foundations.Program.G32PropFourSixPacked0715
import HodgeLean.Foundations.Program.G32PropFourSixPacked0716
import HodgeLean.Foundations.Program.G32PropFourSixPacked0717
import HodgeLean.Foundations.Program.G32PropFourSixPacked0718
import HodgeLean.Foundations.Program.G32PropFourSixPacked0719
import HodgeLean.Foundations.Program.G32PropFourSixPacked0720
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow18
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4096 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4096) = g32p_row18_cosetRepresentatives 4096 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4096 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4096) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4096))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4096)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4096 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4096) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4096))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4096)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4097 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4097) = g32p_row18_cosetRepresentatives 4097 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4097 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4097) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4097))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4097)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4097 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4097) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4097))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4097)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4098 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4098) = g32p_row18_cosetRepresentatives 4098 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4098 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4098) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4098))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4098)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4098 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4098) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4098))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4098)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4099 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4099) = g32p_row18_cosetRepresentatives 4099 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4099 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4099) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4099))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4099)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4099 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4099) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4099))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4099)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4100 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4100) = g32p_row18_cosetRepresentatives 4100 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4100 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4100) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4100))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4100)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4100 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4100) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4100))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4100)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4101 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4101) = g32p_row18_cosetRepresentatives 4101 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4101 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4101) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4101))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4101)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4101 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4101) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4101))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4101)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4102 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4102) = g32p_row18_cosetRepresentatives 4102 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4102 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4102) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4102))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4102)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4102 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4102) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4102))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4102)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4103 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4103) = g32p_row18_cosetRepresentatives 4103 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4103 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4103) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4103))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4103)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4103 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4103) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4103))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4103)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4104 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4104) = g32p_row18_cosetRepresentatives 4104 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4104 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4104) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4104))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4104)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4104 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4104) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4104))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4104)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4105 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4105) = g32p_row18_cosetRepresentatives 4105 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4105 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4105) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4105))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4105)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4105 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4105) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4105))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4105)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4106 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4106) = g32p_row18_cosetRepresentatives 4106 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4106 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4106) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4106))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4106)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4106 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4106) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4106))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4106)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4107 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4107) = g32p_row18_cosetRepresentatives 4107 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4107 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4107) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4107))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4107)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4107 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4107) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4107))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4107)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4108 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4108) = g32p_row18_cosetRepresentatives 4108 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4108 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4108) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4108))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4108)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4108 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4108) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4108))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4108)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4109 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4109) = g32p_row18_cosetRepresentatives 4109 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4109 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4109) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4109))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4109)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4109 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4109) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4109))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4109)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4110 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4110) = g32p_row18_cosetRepresentatives 4110 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4110 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4110) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4110))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4110)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4110 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4110) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4110))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4110)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4111 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4111) = g32p_row18_cosetRepresentatives 4111 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4111 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4111) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4111))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4111)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4111 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4111) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4111))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4111)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0256 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 256 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 256 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4096
  · exact g32p_row18_cosetWord_4097
  · exact g32p_row18_cosetWord_4098
  · exact g32p_row18_cosetWord_4099
  · exact g32p_row18_cosetWord_4100
  · exact g32p_row18_cosetWord_4101
  · exact g32p_row18_cosetWord_4102
  · exact g32p_row18_cosetWord_4103
  · exact g32p_row18_cosetWord_4104
  · exact g32p_row18_cosetWord_4105
  · exact g32p_row18_cosetWord_4106
  · exact g32p_row18_cosetWord_4107
  · exact g32p_row18_cosetWord_4108
  · exact g32p_row18_cosetWord_4109
  · exact g32p_row18_cosetWord_4110
  · exact g32p_row18_cosetWord_4111

theorem g32p_row18_cosetGeneratorBlock_0256 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 256 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 256 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 256 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4096 s
  · exact g32p_row18_cosetGeneratorStep_4097 s
  · exact g32p_row18_cosetGeneratorStep_4098 s
  · exact g32p_row18_cosetGeneratorStep_4099 s
  · exact g32p_row18_cosetGeneratorStep_4100 s
  · exact g32p_row18_cosetGeneratorStep_4101 s
  · exact g32p_row18_cosetGeneratorStep_4102 s
  · exact g32p_row18_cosetGeneratorStep_4103 s
  · exact g32p_row18_cosetGeneratorStep_4104 s
  · exact g32p_row18_cosetGeneratorStep_4105 s
  · exact g32p_row18_cosetGeneratorStep_4106 s
  · exact g32p_row18_cosetGeneratorStep_4107 s
  · exact g32p_row18_cosetGeneratorStep_4108 s
  · exact g32p_row18_cosetGeneratorStep_4109 s
  · exact g32p_row18_cosetGeneratorStep_4110 s
  · exact g32p_row18_cosetGeneratorStep_4111 s

theorem g32p_row18_cosetBranchBlock_0256 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 256 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 256 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 256 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4096 s
  · exact g32p_row18_cosetBranchStep_4097 s
  · exact g32p_row18_cosetBranchStep_4098 s
  · exact g32p_row18_cosetBranchStep_4099 s
  · exact g32p_row18_cosetBranchStep_4100 s
  · exact g32p_row18_cosetBranchStep_4101 s
  · exact g32p_row18_cosetBranchStep_4102 s
  · exact g32p_row18_cosetBranchStep_4103 s
  · exact g32p_row18_cosetBranchStep_4104 s
  · exact g32p_row18_cosetBranchStep_4105 s
  · exact g32p_row18_cosetBranchStep_4106 s
  · exact g32p_row18_cosetBranchStep_4107 s
  · exact g32p_row18_cosetBranchStep_4108 s
  · exact g32p_row18_cosetBranchStep_4109 s
  · exact g32p_row18_cosetBranchStep_4110 s
  · exact g32p_row18_cosetBranchStep_4111 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4112 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4112) = g32p_row18_cosetRepresentatives 4112 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4112 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4112) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4112))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4112)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4112 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4112) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4112))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4112)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4113 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4113) = g32p_row18_cosetRepresentatives 4113 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4113 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4113) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4113))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4113)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4113 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4113) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4113))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4113)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4114 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4114) = g32p_row18_cosetRepresentatives 4114 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4114 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4114) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4114))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4114)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4114 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4114) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4114))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4114)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4115 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4115) = g32p_row18_cosetRepresentatives 4115 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4115 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4115) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4115))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4115)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4115 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4115) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4115))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4115)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4116 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4116) = g32p_row18_cosetRepresentatives 4116 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4116 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4116) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4116))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4116)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4116 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4116) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4116))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4116)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4117 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4117) = g32p_row18_cosetRepresentatives 4117 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4117 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4117) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4117))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4117)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4117 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4117) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4117))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4117)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4118 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4118) = g32p_row18_cosetRepresentatives 4118 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4118 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4118) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4118))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4118)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4118 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4118) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4118))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4118)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4119 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4119) = g32p_row18_cosetRepresentatives 4119 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4119 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4119) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4119))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4119)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4119 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4119) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4119))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4119)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4120 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4120) = g32p_row18_cosetRepresentatives 4120 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4120 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4120) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4120))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4120)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4120 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4120) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4120))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4120)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4121 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4121) = g32p_row18_cosetRepresentatives 4121 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4121 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4121) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4121))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4121)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4121 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4121) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4121))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4121)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4122 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4122) = g32p_row18_cosetRepresentatives 4122 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4122 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4122) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4122))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4122)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4122 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4122) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4122))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4122)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4123 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4123) = g32p_row18_cosetRepresentatives 4123 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4123 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4123) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4123))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4123)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4123 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4123) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4123))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4123)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4124 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4124) = g32p_row18_cosetRepresentatives 4124 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4124 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4124) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4124))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4124)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4124 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4124) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4124))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4124)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4125 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4125) = g32p_row18_cosetRepresentatives 4125 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4125 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4125) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4125))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4125)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4125 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4125) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4125))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4125)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4126 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4126) = g32p_row18_cosetRepresentatives 4126 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4126 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4126) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4126))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4126)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4126 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4126) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4126))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4126)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4127 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4127) = g32p_row18_cosetRepresentatives 4127 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4127 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4127) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4127))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4127)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4127 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4127) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4127))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4127)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0257 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 257 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 257 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4112
  · exact g32p_row18_cosetWord_4113
  · exact g32p_row18_cosetWord_4114
  · exact g32p_row18_cosetWord_4115
  · exact g32p_row18_cosetWord_4116
  · exact g32p_row18_cosetWord_4117
  · exact g32p_row18_cosetWord_4118
  · exact g32p_row18_cosetWord_4119
  · exact g32p_row18_cosetWord_4120
  · exact g32p_row18_cosetWord_4121
  · exact g32p_row18_cosetWord_4122
  · exact g32p_row18_cosetWord_4123
  · exact g32p_row18_cosetWord_4124
  · exact g32p_row18_cosetWord_4125
  · exact g32p_row18_cosetWord_4126
  · exact g32p_row18_cosetWord_4127

theorem g32p_row18_cosetGeneratorBlock_0257 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 257 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 257 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 257 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4112 s
  · exact g32p_row18_cosetGeneratorStep_4113 s
  · exact g32p_row18_cosetGeneratorStep_4114 s
  · exact g32p_row18_cosetGeneratorStep_4115 s
  · exact g32p_row18_cosetGeneratorStep_4116 s
  · exact g32p_row18_cosetGeneratorStep_4117 s
  · exact g32p_row18_cosetGeneratorStep_4118 s
  · exact g32p_row18_cosetGeneratorStep_4119 s
  · exact g32p_row18_cosetGeneratorStep_4120 s
  · exact g32p_row18_cosetGeneratorStep_4121 s
  · exact g32p_row18_cosetGeneratorStep_4122 s
  · exact g32p_row18_cosetGeneratorStep_4123 s
  · exact g32p_row18_cosetGeneratorStep_4124 s
  · exact g32p_row18_cosetGeneratorStep_4125 s
  · exact g32p_row18_cosetGeneratorStep_4126 s
  · exact g32p_row18_cosetGeneratorStep_4127 s

theorem g32p_row18_cosetBranchBlock_0257 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 257 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 257 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 257 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4112 s
  · exact g32p_row18_cosetBranchStep_4113 s
  · exact g32p_row18_cosetBranchStep_4114 s
  · exact g32p_row18_cosetBranchStep_4115 s
  · exact g32p_row18_cosetBranchStep_4116 s
  · exact g32p_row18_cosetBranchStep_4117 s
  · exact g32p_row18_cosetBranchStep_4118 s
  · exact g32p_row18_cosetBranchStep_4119 s
  · exact g32p_row18_cosetBranchStep_4120 s
  · exact g32p_row18_cosetBranchStep_4121 s
  · exact g32p_row18_cosetBranchStep_4122 s
  · exact g32p_row18_cosetBranchStep_4123 s
  · exact g32p_row18_cosetBranchStep_4124 s
  · exact g32p_row18_cosetBranchStep_4125 s
  · exact g32p_row18_cosetBranchStep_4126 s
  · exact g32p_row18_cosetBranchStep_4127 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4128 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4128) = g32p_row18_cosetRepresentatives 4128 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4128 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4128) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4128))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4128)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4128 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4128) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4128))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4128)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4129 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4129) = g32p_row18_cosetRepresentatives 4129 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4129 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4129) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4129))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4129)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4129 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4129) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4129))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4129)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4130 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4130) = g32p_row18_cosetRepresentatives 4130 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4130 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4130) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4130))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4130)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4130 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4130) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4130))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4130)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4131 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4131) = g32p_row18_cosetRepresentatives 4131 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4131 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4131) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4131))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4131)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4131 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4131) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4131))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4131)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4132 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4132) = g32p_row18_cosetRepresentatives 4132 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4132 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4132) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4132))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4132)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4132 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4132) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4132))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4132)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4133 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4133) = g32p_row18_cosetRepresentatives 4133 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4133 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4133) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4133))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4133)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4133 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4133) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4133))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4133)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4134 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4134) = g32p_row18_cosetRepresentatives 4134 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4134 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4134) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4134))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4134)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4134 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4134) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4134))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4134)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4135 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4135) = g32p_row18_cosetRepresentatives 4135 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4135 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4135) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4135))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4135)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4135 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4135) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4135))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4135)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4136 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4136) = g32p_row18_cosetRepresentatives 4136 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4136 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4136) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4136))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4136)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4136 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4136) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4136))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4136)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4137 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4137) = g32p_row18_cosetRepresentatives 4137 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4137 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4137) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4137))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4137)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4137 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4137) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4137))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4137)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4138 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4138) = g32p_row18_cosetRepresentatives 4138 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4138 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4138) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4138))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4138)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4138 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4138) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4138))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4138)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4139 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4139) = g32p_row18_cosetRepresentatives 4139 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4139 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4139) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4139))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4139)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4139 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4139) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4139))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4139)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4140 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4140) = g32p_row18_cosetRepresentatives 4140 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4140 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4140) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4140))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4140)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4140 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4140) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4140))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4140)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4141 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4141) = g32p_row18_cosetRepresentatives 4141 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4141 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4141) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4141))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4141)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4141 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4141) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4141))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4141)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4142 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4142) = g32p_row18_cosetRepresentatives 4142 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4142 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4142) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4142))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4142)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4142 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4142) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4142))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4142)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4143 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4143) = g32p_row18_cosetRepresentatives 4143 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4143 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4143) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4143))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4143)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4143 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4143) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4143))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4143)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0258 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 258 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 258 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4128
  · exact g32p_row18_cosetWord_4129
  · exact g32p_row18_cosetWord_4130
  · exact g32p_row18_cosetWord_4131
  · exact g32p_row18_cosetWord_4132
  · exact g32p_row18_cosetWord_4133
  · exact g32p_row18_cosetWord_4134
  · exact g32p_row18_cosetWord_4135
  · exact g32p_row18_cosetWord_4136
  · exact g32p_row18_cosetWord_4137
  · exact g32p_row18_cosetWord_4138
  · exact g32p_row18_cosetWord_4139
  · exact g32p_row18_cosetWord_4140
  · exact g32p_row18_cosetWord_4141
  · exact g32p_row18_cosetWord_4142
  · exact g32p_row18_cosetWord_4143

theorem g32p_row18_cosetGeneratorBlock_0258 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 258 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 258 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 258 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4128 s
  · exact g32p_row18_cosetGeneratorStep_4129 s
  · exact g32p_row18_cosetGeneratorStep_4130 s
  · exact g32p_row18_cosetGeneratorStep_4131 s
  · exact g32p_row18_cosetGeneratorStep_4132 s
  · exact g32p_row18_cosetGeneratorStep_4133 s
  · exact g32p_row18_cosetGeneratorStep_4134 s
  · exact g32p_row18_cosetGeneratorStep_4135 s
  · exact g32p_row18_cosetGeneratorStep_4136 s
  · exact g32p_row18_cosetGeneratorStep_4137 s
  · exact g32p_row18_cosetGeneratorStep_4138 s
  · exact g32p_row18_cosetGeneratorStep_4139 s
  · exact g32p_row18_cosetGeneratorStep_4140 s
  · exact g32p_row18_cosetGeneratorStep_4141 s
  · exact g32p_row18_cosetGeneratorStep_4142 s
  · exact g32p_row18_cosetGeneratorStep_4143 s

theorem g32p_row18_cosetBranchBlock_0258 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 258 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 258 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 258 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4128 s
  · exact g32p_row18_cosetBranchStep_4129 s
  · exact g32p_row18_cosetBranchStep_4130 s
  · exact g32p_row18_cosetBranchStep_4131 s
  · exact g32p_row18_cosetBranchStep_4132 s
  · exact g32p_row18_cosetBranchStep_4133 s
  · exact g32p_row18_cosetBranchStep_4134 s
  · exact g32p_row18_cosetBranchStep_4135 s
  · exact g32p_row18_cosetBranchStep_4136 s
  · exact g32p_row18_cosetBranchStep_4137 s
  · exact g32p_row18_cosetBranchStep_4138 s
  · exact g32p_row18_cosetBranchStep_4139 s
  · exact g32p_row18_cosetBranchStep_4140 s
  · exact g32p_row18_cosetBranchStep_4141 s
  · exact g32p_row18_cosetBranchStep_4142 s
  · exact g32p_row18_cosetBranchStep_4143 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4144 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4144) = g32p_row18_cosetRepresentatives 4144 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4144 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4144) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4144))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4144)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4144 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4144) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4144))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4144)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4145 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4145) = g32p_row18_cosetRepresentatives 4145 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4145 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4145) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4145))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4145)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4145 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4145) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4145))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4145)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4146 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4146) = g32p_row18_cosetRepresentatives 4146 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4146 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4146) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4146))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4146)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4146 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4146) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4146))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4146)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4147 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4147) = g32p_row18_cosetRepresentatives 4147 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4147 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4147) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4147))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4147)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4147 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4147) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4147))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4147)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4148 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4148) = g32p_row18_cosetRepresentatives 4148 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4148 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4148) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4148))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4148)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4148 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4148) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4148))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4148)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4149 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4149) = g32p_row18_cosetRepresentatives 4149 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4149 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4149) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4149))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4149)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4149 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4149) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4149))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4149)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4150 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4150) = g32p_row18_cosetRepresentatives 4150 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4150 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4150) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4150))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4150)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4150 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4150) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4150))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4150)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4151 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4151) = g32p_row18_cosetRepresentatives 4151 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4151 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4151) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4151))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4151)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4151 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4151) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4151))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4151)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4152 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4152) = g32p_row18_cosetRepresentatives 4152 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4152 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4152) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4152))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4152)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4152 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4152) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4152))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4152)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4153 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4153) = g32p_row18_cosetRepresentatives 4153 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4153 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4153) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4153))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4153)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4153 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4153) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4153))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4153)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4154 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4154) = g32p_row18_cosetRepresentatives 4154 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4154 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4154) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4154))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4154)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4154 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4154) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4154))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4154)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4155 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4155) = g32p_row18_cosetRepresentatives 4155 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4155 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4155) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4155))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4155)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4155 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4155) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4155))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4155)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4156 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4156) = g32p_row18_cosetRepresentatives 4156 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4156 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4156) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4156))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4156)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4156 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4156) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4156))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4156)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4157 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4157) = g32p_row18_cosetRepresentatives 4157 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4157 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4157) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4157))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4157)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4157 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4157) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4157))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4157)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4158 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4158) = g32p_row18_cosetRepresentatives 4158 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4158 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4158) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4158))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4158)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4158 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4158) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4158))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4158)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4159 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4159) = g32p_row18_cosetRepresentatives 4159 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4159 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4159) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4159))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4159)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4159 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4159) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4159))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4159)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0259 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 259 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 259 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4144
  · exact g32p_row18_cosetWord_4145
  · exact g32p_row18_cosetWord_4146
  · exact g32p_row18_cosetWord_4147
  · exact g32p_row18_cosetWord_4148
  · exact g32p_row18_cosetWord_4149
  · exact g32p_row18_cosetWord_4150
  · exact g32p_row18_cosetWord_4151
  · exact g32p_row18_cosetWord_4152
  · exact g32p_row18_cosetWord_4153
  · exact g32p_row18_cosetWord_4154
  · exact g32p_row18_cosetWord_4155
  · exact g32p_row18_cosetWord_4156
  · exact g32p_row18_cosetWord_4157
  · exact g32p_row18_cosetWord_4158
  · exact g32p_row18_cosetWord_4159

theorem g32p_row18_cosetGeneratorBlock_0259 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 259 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 259 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 259 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4144 s
  · exact g32p_row18_cosetGeneratorStep_4145 s
  · exact g32p_row18_cosetGeneratorStep_4146 s
  · exact g32p_row18_cosetGeneratorStep_4147 s
  · exact g32p_row18_cosetGeneratorStep_4148 s
  · exact g32p_row18_cosetGeneratorStep_4149 s
  · exact g32p_row18_cosetGeneratorStep_4150 s
  · exact g32p_row18_cosetGeneratorStep_4151 s
  · exact g32p_row18_cosetGeneratorStep_4152 s
  · exact g32p_row18_cosetGeneratorStep_4153 s
  · exact g32p_row18_cosetGeneratorStep_4154 s
  · exact g32p_row18_cosetGeneratorStep_4155 s
  · exact g32p_row18_cosetGeneratorStep_4156 s
  · exact g32p_row18_cosetGeneratorStep_4157 s
  · exact g32p_row18_cosetGeneratorStep_4158 s
  · exact g32p_row18_cosetGeneratorStep_4159 s

theorem g32p_row18_cosetBranchBlock_0259 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 259 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 259 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 259 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4144 s
  · exact g32p_row18_cosetBranchStep_4145 s
  · exact g32p_row18_cosetBranchStep_4146 s
  · exact g32p_row18_cosetBranchStep_4147 s
  · exact g32p_row18_cosetBranchStep_4148 s
  · exact g32p_row18_cosetBranchStep_4149 s
  · exact g32p_row18_cosetBranchStep_4150 s
  · exact g32p_row18_cosetBranchStep_4151 s
  · exact g32p_row18_cosetBranchStep_4152 s
  · exact g32p_row18_cosetBranchStep_4153 s
  · exact g32p_row18_cosetBranchStep_4154 s
  · exact g32p_row18_cosetBranchStep_4155 s
  · exact g32p_row18_cosetBranchStep_4156 s
  · exact g32p_row18_cosetBranchStep_4157 s
  · exact g32p_row18_cosetBranchStep_4158 s
  · exact g32p_row18_cosetBranchStep_4159 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4160 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4160) = g32p_row18_cosetRepresentatives 4160 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4160 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4160) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4160))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4160)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4160 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4160) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4160))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4160)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4161 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4161) = g32p_row18_cosetRepresentatives 4161 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4161 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4161) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4161))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4161)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4161 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4161) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4161))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4161)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4162 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4162) = g32p_row18_cosetRepresentatives 4162 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4162 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4162) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4162))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4162)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4162 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4162) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4162))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4162)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4163 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4163) = g32p_row18_cosetRepresentatives 4163 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4163 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4163) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4163))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4163)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4163 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4163) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4163))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4163)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4164 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4164) = g32p_row18_cosetRepresentatives 4164 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4164 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4164) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4164))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4164)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4164 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4164) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4164))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4164)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4165 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4165) = g32p_row18_cosetRepresentatives 4165 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4165 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4165) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4165))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4165)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4165 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4165) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4165))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4165)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4166 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4166) = g32p_row18_cosetRepresentatives 4166 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4166 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4166) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4166))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4166)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4166 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4166) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4166))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4166)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4167 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4167) = g32p_row18_cosetRepresentatives 4167 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4167 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4167) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4167))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4167)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4167 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4167) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4167))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4167)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4168 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4168) = g32p_row18_cosetRepresentatives 4168 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4168 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4168) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4168))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4168)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4168 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4168) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4168))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4168)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4169 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4169) = g32p_row18_cosetRepresentatives 4169 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4169 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4169) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4169))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4169)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4169 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4169) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4169))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4169)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4170 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4170) = g32p_row18_cosetRepresentatives 4170 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4170 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4170) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4170))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4170)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4170 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4170) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4170))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4170)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4171 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4171) = g32p_row18_cosetRepresentatives 4171 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4171 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4171) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4171))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4171)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4171 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4171) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4171))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4171)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4172 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4172) = g32p_row18_cosetRepresentatives 4172 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4172 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4172) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4172))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4172)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4172 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4172) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4172))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4172)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4173 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4173) = g32p_row18_cosetRepresentatives 4173 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4173 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4173) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4173))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4173)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4173 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4173) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4173))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4173)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4174 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4174) = g32p_row18_cosetRepresentatives 4174 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4174 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4174) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4174))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4174)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4174 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4174) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4174))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4174)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4175 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4175) = g32p_row18_cosetRepresentatives 4175 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4175 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4175) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4175))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4175)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4175 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4175) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4175))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4175)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0260 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 260 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 260 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4160
  · exact g32p_row18_cosetWord_4161
  · exact g32p_row18_cosetWord_4162
  · exact g32p_row18_cosetWord_4163
  · exact g32p_row18_cosetWord_4164
  · exact g32p_row18_cosetWord_4165
  · exact g32p_row18_cosetWord_4166
  · exact g32p_row18_cosetWord_4167
  · exact g32p_row18_cosetWord_4168
  · exact g32p_row18_cosetWord_4169
  · exact g32p_row18_cosetWord_4170
  · exact g32p_row18_cosetWord_4171
  · exact g32p_row18_cosetWord_4172
  · exact g32p_row18_cosetWord_4173
  · exact g32p_row18_cosetWord_4174
  · exact g32p_row18_cosetWord_4175

theorem g32p_row18_cosetGeneratorBlock_0260 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 260 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 260 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 260 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4160 s
  · exact g32p_row18_cosetGeneratorStep_4161 s
  · exact g32p_row18_cosetGeneratorStep_4162 s
  · exact g32p_row18_cosetGeneratorStep_4163 s
  · exact g32p_row18_cosetGeneratorStep_4164 s
  · exact g32p_row18_cosetGeneratorStep_4165 s
  · exact g32p_row18_cosetGeneratorStep_4166 s
  · exact g32p_row18_cosetGeneratorStep_4167 s
  · exact g32p_row18_cosetGeneratorStep_4168 s
  · exact g32p_row18_cosetGeneratorStep_4169 s
  · exact g32p_row18_cosetGeneratorStep_4170 s
  · exact g32p_row18_cosetGeneratorStep_4171 s
  · exact g32p_row18_cosetGeneratorStep_4172 s
  · exact g32p_row18_cosetGeneratorStep_4173 s
  · exact g32p_row18_cosetGeneratorStep_4174 s
  · exact g32p_row18_cosetGeneratorStep_4175 s

theorem g32p_row18_cosetBranchBlock_0260 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 260 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 260 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 260 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4160 s
  · exact g32p_row18_cosetBranchStep_4161 s
  · exact g32p_row18_cosetBranchStep_4162 s
  · exact g32p_row18_cosetBranchStep_4163 s
  · exact g32p_row18_cosetBranchStep_4164 s
  · exact g32p_row18_cosetBranchStep_4165 s
  · exact g32p_row18_cosetBranchStep_4166 s
  · exact g32p_row18_cosetBranchStep_4167 s
  · exact g32p_row18_cosetBranchStep_4168 s
  · exact g32p_row18_cosetBranchStep_4169 s
  · exact g32p_row18_cosetBranchStep_4170 s
  · exact g32p_row18_cosetBranchStep_4171 s
  · exact g32p_row18_cosetBranchStep_4172 s
  · exact g32p_row18_cosetBranchStep_4173 s
  · exact g32p_row18_cosetBranchStep_4174 s
  · exact g32p_row18_cosetBranchStep_4175 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4176 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4176) = g32p_row18_cosetRepresentatives 4176 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4176 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4176) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4176))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4176)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4176 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4176) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4176))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4176)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4177 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4177) = g32p_row18_cosetRepresentatives 4177 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4177 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4177) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4177))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4177)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4177 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4177) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4177))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4177)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4178 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4178) = g32p_row18_cosetRepresentatives 4178 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4178 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4178) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4178))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4178)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4178 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4178) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4178))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4178)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4179 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4179) = g32p_row18_cosetRepresentatives 4179 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4179 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4179) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4179))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4179)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4179 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4179) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4179))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4179)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4180 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4180) = g32p_row18_cosetRepresentatives 4180 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4180 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4180) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4180))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4180)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4180 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4180) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4180))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4180)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4181 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4181) = g32p_row18_cosetRepresentatives 4181 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4181 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4181) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4181))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4181)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4181 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4181) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4181))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4181)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4182 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4182) = g32p_row18_cosetRepresentatives 4182 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4182 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4182) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4182))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4182)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4182 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4182) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4182))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4182)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4183 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4183) = g32p_row18_cosetRepresentatives 4183 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4183 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4183) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4183))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4183)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4183 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4183) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4183))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4183)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4184 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4184) = g32p_row18_cosetRepresentatives 4184 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4184 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4184) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4184))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4184)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4184 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4184) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4184))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4184)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4185 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4185) = g32p_row18_cosetRepresentatives 4185 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4185 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4185) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4185))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4185)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4185 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4185) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4185))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4185)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4186 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4186) = g32p_row18_cosetRepresentatives 4186 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4186 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4186) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4186))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4186)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4186 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4186) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4186))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4186)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4187 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4187) = g32p_row18_cosetRepresentatives 4187 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4187 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4187) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4187))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4187)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4187 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4187) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4187))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4187)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4188 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4188) = g32p_row18_cosetRepresentatives 4188 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4188 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4188) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4188))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4188)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4188 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4188) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4188))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4188)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4189 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4189) = g32p_row18_cosetRepresentatives 4189 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4189 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4189) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4189))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4189)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4189 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4189) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4189))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4189)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4190 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4190) = g32p_row18_cosetRepresentatives 4190 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4190 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4190) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4190))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4190)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4190 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4190) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4190))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4190)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4191 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4191) = g32p_row18_cosetRepresentatives 4191 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4191 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4191) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4191))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4191)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4191 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4191) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4191))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4191)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0261 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 261 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 261 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4176
  · exact g32p_row18_cosetWord_4177
  · exact g32p_row18_cosetWord_4178
  · exact g32p_row18_cosetWord_4179
  · exact g32p_row18_cosetWord_4180
  · exact g32p_row18_cosetWord_4181
  · exact g32p_row18_cosetWord_4182
  · exact g32p_row18_cosetWord_4183
  · exact g32p_row18_cosetWord_4184
  · exact g32p_row18_cosetWord_4185
  · exact g32p_row18_cosetWord_4186
  · exact g32p_row18_cosetWord_4187
  · exact g32p_row18_cosetWord_4188
  · exact g32p_row18_cosetWord_4189
  · exact g32p_row18_cosetWord_4190
  · exact g32p_row18_cosetWord_4191

theorem g32p_row18_cosetGeneratorBlock_0261 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 261 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 261 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 261 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4176 s
  · exact g32p_row18_cosetGeneratorStep_4177 s
  · exact g32p_row18_cosetGeneratorStep_4178 s
  · exact g32p_row18_cosetGeneratorStep_4179 s
  · exact g32p_row18_cosetGeneratorStep_4180 s
  · exact g32p_row18_cosetGeneratorStep_4181 s
  · exact g32p_row18_cosetGeneratorStep_4182 s
  · exact g32p_row18_cosetGeneratorStep_4183 s
  · exact g32p_row18_cosetGeneratorStep_4184 s
  · exact g32p_row18_cosetGeneratorStep_4185 s
  · exact g32p_row18_cosetGeneratorStep_4186 s
  · exact g32p_row18_cosetGeneratorStep_4187 s
  · exact g32p_row18_cosetGeneratorStep_4188 s
  · exact g32p_row18_cosetGeneratorStep_4189 s
  · exact g32p_row18_cosetGeneratorStep_4190 s
  · exact g32p_row18_cosetGeneratorStep_4191 s

theorem g32p_row18_cosetBranchBlock_0261 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 261 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 261 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 261 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4176 s
  · exact g32p_row18_cosetBranchStep_4177 s
  · exact g32p_row18_cosetBranchStep_4178 s
  · exact g32p_row18_cosetBranchStep_4179 s
  · exact g32p_row18_cosetBranchStep_4180 s
  · exact g32p_row18_cosetBranchStep_4181 s
  · exact g32p_row18_cosetBranchStep_4182 s
  · exact g32p_row18_cosetBranchStep_4183 s
  · exact g32p_row18_cosetBranchStep_4184 s
  · exact g32p_row18_cosetBranchStep_4185 s
  · exact g32p_row18_cosetBranchStep_4186 s
  · exact g32p_row18_cosetBranchStep_4187 s
  · exact g32p_row18_cosetBranchStep_4188 s
  · exact g32p_row18_cosetBranchStep_4189 s
  · exact g32p_row18_cosetBranchStep_4190 s
  · exact g32p_row18_cosetBranchStep_4191 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4192 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4192) = g32p_row18_cosetRepresentatives 4192 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4192 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4192) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4192))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4192)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4192 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4192) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4192))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4192)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4193 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4193) = g32p_row18_cosetRepresentatives 4193 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4193 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4193) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4193))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4193)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4193 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4193) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4193))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4193)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4194 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4194) = g32p_row18_cosetRepresentatives 4194 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4194 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4194) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4194))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4194)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4194 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4194) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4194))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4194)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4195 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4195) = g32p_row18_cosetRepresentatives 4195 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4195 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4195) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4195))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4195)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4195 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4195) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4195))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4195)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4196 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4196) = g32p_row18_cosetRepresentatives 4196 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4196 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4196) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4196))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4196)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4196 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4196) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4196))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4196)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4197 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4197) = g32p_row18_cosetRepresentatives 4197 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4197 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4197) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4197))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4197)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4197 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4197) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4197))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4197)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4198 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4198) = g32p_row18_cosetRepresentatives 4198 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4198 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4198) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4198))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4198)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4198 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4198) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4198))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4198)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4199 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4199) = g32p_row18_cosetRepresentatives 4199 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4199 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4199) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4199))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4199)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4199 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4199) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4199))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4199)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4200 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4200) = g32p_row18_cosetRepresentatives 4200 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4200 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4200) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4200))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4200)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4200 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4200) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4200))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4200)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4201 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4201) = g32p_row18_cosetRepresentatives 4201 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4201 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4201) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4201))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4201)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4201 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4201) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4201))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4201)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4202 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4202) = g32p_row18_cosetRepresentatives 4202 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4202 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4202) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4202))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4202)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4202 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4202) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4202))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4202)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4203 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4203) = g32p_row18_cosetRepresentatives 4203 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4203 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4203) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4203))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4203)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4203 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4203) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4203))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4203)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4204 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4204) = g32p_row18_cosetRepresentatives 4204 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4204 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4204) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4204))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4204)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4204 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4204) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4204))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4204)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4205 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4205) = g32p_row18_cosetRepresentatives 4205 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4205 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4205) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4205))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4205)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4205 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4205) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4205))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4205)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4206 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4206) = g32p_row18_cosetRepresentatives 4206 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4206 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4206) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4206))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4206)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4206 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4206) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4206))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4206)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4207 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4207) = g32p_row18_cosetRepresentatives 4207 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4207 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4207) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4207))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4207)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4207 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4207) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4207))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4207)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0262 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 262 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 262 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4192
  · exact g32p_row18_cosetWord_4193
  · exact g32p_row18_cosetWord_4194
  · exact g32p_row18_cosetWord_4195
  · exact g32p_row18_cosetWord_4196
  · exact g32p_row18_cosetWord_4197
  · exact g32p_row18_cosetWord_4198
  · exact g32p_row18_cosetWord_4199
  · exact g32p_row18_cosetWord_4200
  · exact g32p_row18_cosetWord_4201
  · exact g32p_row18_cosetWord_4202
  · exact g32p_row18_cosetWord_4203
  · exact g32p_row18_cosetWord_4204
  · exact g32p_row18_cosetWord_4205
  · exact g32p_row18_cosetWord_4206
  · exact g32p_row18_cosetWord_4207

theorem g32p_row18_cosetGeneratorBlock_0262 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 262 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 262 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 262 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4192 s
  · exact g32p_row18_cosetGeneratorStep_4193 s
  · exact g32p_row18_cosetGeneratorStep_4194 s
  · exact g32p_row18_cosetGeneratorStep_4195 s
  · exact g32p_row18_cosetGeneratorStep_4196 s
  · exact g32p_row18_cosetGeneratorStep_4197 s
  · exact g32p_row18_cosetGeneratorStep_4198 s
  · exact g32p_row18_cosetGeneratorStep_4199 s
  · exact g32p_row18_cosetGeneratorStep_4200 s
  · exact g32p_row18_cosetGeneratorStep_4201 s
  · exact g32p_row18_cosetGeneratorStep_4202 s
  · exact g32p_row18_cosetGeneratorStep_4203 s
  · exact g32p_row18_cosetGeneratorStep_4204 s
  · exact g32p_row18_cosetGeneratorStep_4205 s
  · exact g32p_row18_cosetGeneratorStep_4206 s
  · exact g32p_row18_cosetGeneratorStep_4207 s

theorem g32p_row18_cosetBranchBlock_0262 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 262 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 262 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 262 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4192 s
  · exact g32p_row18_cosetBranchStep_4193 s
  · exact g32p_row18_cosetBranchStep_4194 s
  · exact g32p_row18_cosetBranchStep_4195 s
  · exact g32p_row18_cosetBranchStep_4196 s
  · exact g32p_row18_cosetBranchStep_4197 s
  · exact g32p_row18_cosetBranchStep_4198 s
  · exact g32p_row18_cosetBranchStep_4199 s
  · exact g32p_row18_cosetBranchStep_4200 s
  · exact g32p_row18_cosetBranchStep_4201 s
  · exact g32p_row18_cosetBranchStep_4202 s
  · exact g32p_row18_cosetBranchStep_4203 s
  · exact g32p_row18_cosetBranchStep_4204 s
  · exact g32p_row18_cosetBranchStep_4205 s
  · exact g32p_row18_cosetBranchStep_4206 s
  · exact g32p_row18_cosetBranchStep_4207 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4208 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4208) = g32p_row18_cosetRepresentatives 4208 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4208 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4208) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4208))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4208)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4208 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4208) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4208))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4208)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4209 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4209) = g32p_row18_cosetRepresentatives 4209 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4209 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4209) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4209))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4209)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4209 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4209) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4209))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4209)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4210 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4210) = g32p_row18_cosetRepresentatives 4210 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4210 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4210) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4210))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4210)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4210 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4210) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4210))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4210)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4211 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4211) = g32p_row18_cosetRepresentatives 4211 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4211 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4211) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4211))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4211)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4211 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4211) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4211))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4211)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4212 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4212) = g32p_row18_cosetRepresentatives 4212 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4212 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4212) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4212))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4212)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4212 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4212) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4212))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4212)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4213 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4213) = g32p_row18_cosetRepresentatives 4213 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4213 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4213) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4213))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4213)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4213 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4213) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4213))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4213)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4214 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4214) = g32p_row18_cosetRepresentatives 4214 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4214 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4214) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4214))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4214)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4214 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4214) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4214))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4214)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4215 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4215) = g32p_row18_cosetRepresentatives 4215 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4215 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4215) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4215))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4215)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4215 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4215) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4215))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4215)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4216 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4216) = g32p_row18_cosetRepresentatives 4216 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4216 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4216) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4216))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4216)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4216 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4216) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4216))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4216)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4217 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4217) = g32p_row18_cosetRepresentatives 4217 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4217 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4217) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4217))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4217)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4217 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4217) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4217))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4217)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4218 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4218) = g32p_row18_cosetRepresentatives 4218 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4218 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4218) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4218))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4218)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4218 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4218) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4218))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4218)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4219 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4219) = g32p_row18_cosetRepresentatives 4219 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4219 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4219) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4219))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4219)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4219 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4219) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4219))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4219)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4220 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4220) = g32p_row18_cosetRepresentatives 4220 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4220 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4220) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4220))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4220)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4220 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4220) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4220))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4220)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4221 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4221) = g32p_row18_cosetRepresentatives 4221 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4221 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4221) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4221))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4221)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4221 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4221) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4221))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4221)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4222 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4222) = g32p_row18_cosetRepresentatives 4222 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4222 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4222) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4222))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4222)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4222 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4222) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4222))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4222)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4223 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4223) = g32p_row18_cosetRepresentatives 4223 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4223 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4223) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4223))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4223)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4223 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4223) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4223))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4223)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0263 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 263 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 263 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4208
  · exact g32p_row18_cosetWord_4209
  · exact g32p_row18_cosetWord_4210
  · exact g32p_row18_cosetWord_4211
  · exact g32p_row18_cosetWord_4212
  · exact g32p_row18_cosetWord_4213
  · exact g32p_row18_cosetWord_4214
  · exact g32p_row18_cosetWord_4215
  · exact g32p_row18_cosetWord_4216
  · exact g32p_row18_cosetWord_4217
  · exact g32p_row18_cosetWord_4218
  · exact g32p_row18_cosetWord_4219
  · exact g32p_row18_cosetWord_4220
  · exact g32p_row18_cosetWord_4221
  · exact g32p_row18_cosetWord_4222
  · exact g32p_row18_cosetWord_4223

theorem g32p_row18_cosetGeneratorBlock_0263 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 263 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 263 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 263 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4208 s
  · exact g32p_row18_cosetGeneratorStep_4209 s
  · exact g32p_row18_cosetGeneratorStep_4210 s
  · exact g32p_row18_cosetGeneratorStep_4211 s
  · exact g32p_row18_cosetGeneratorStep_4212 s
  · exact g32p_row18_cosetGeneratorStep_4213 s
  · exact g32p_row18_cosetGeneratorStep_4214 s
  · exact g32p_row18_cosetGeneratorStep_4215 s
  · exact g32p_row18_cosetGeneratorStep_4216 s
  · exact g32p_row18_cosetGeneratorStep_4217 s
  · exact g32p_row18_cosetGeneratorStep_4218 s
  · exact g32p_row18_cosetGeneratorStep_4219 s
  · exact g32p_row18_cosetGeneratorStep_4220 s
  · exact g32p_row18_cosetGeneratorStep_4221 s
  · exact g32p_row18_cosetGeneratorStep_4222 s
  · exact g32p_row18_cosetGeneratorStep_4223 s

theorem g32p_row18_cosetBranchBlock_0263 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 263 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 263 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 263 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4208 s
  · exact g32p_row18_cosetBranchStep_4209 s
  · exact g32p_row18_cosetBranchStep_4210 s
  · exact g32p_row18_cosetBranchStep_4211 s
  · exact g32p_row18_cosetBranchStep_4212 s
  · exact g32p_row18_cosetBranchStep_4213 s
  · exact g32p_row18_cosetBranchStep_4214 s
  · exact g32p_row18_cosetBranchStep_4215 s
  · exact g32p_row18_cosetBranchStep_4216 s
  · exact g32p_row18_cosetBranchStep_4217 s
  · exact g32p_row18_cosetBranchStep_4218 s
  · exact g32p_row18_cosetBranchStep_4219 s
  · exact g32p_row18_cosetBranchStep_4220 s
  · exact g32p_row18_cosetBranchStep_4221 s
  · exact g32p_row18_cosetBranchStep_4222 s
  · exact g32p_row18_cosetBranchStep_4223 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4224 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4224) = g32p_row18_cosetRepresentatives 4224 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4224 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4224) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4224))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4224)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4224 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4224) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4224))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4224)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4225 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4225) = g32p_row18_cosetRepresentatives 4225 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4225 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4225) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4225))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4225)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4225 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4225) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4225))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4225)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4226 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4226) = g32p_row18_cosetRepresentatives 4226 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4226 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4226) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4226))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4226)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4226 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4226) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4226))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4226)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4227 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4227) = g32p_row18_cosetRepresentatives 4227 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4227 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4227) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4227))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4227)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4227 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4227) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4227))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4227)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4228 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4228) = g32p_row18_cosetRepresentatives 4228 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4228 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4228) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4228))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4228)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4228 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4228) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4228))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4228)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4229 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4229) = g32p_row18_cosetRepresentatives 4229 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4229 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4229) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4229))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4229)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4229 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4229) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4229))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4229)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4230 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4230) = g32p_row18_cosetRepresentatives 4230 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4230 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4230) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4230))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4230)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4230 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4230) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4230))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4230)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4231 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4231) = g32p_row18_cosetRepresentatives 4231 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4231 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4231) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4231))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4231)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4231 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4231) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4231))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4231)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4232 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4232) = g32p_row18_cosetRepresentatives 4232 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4232 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4232) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4232))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4232)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4232 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4232) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4232))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4232)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4233 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4233) = g32p_row18_cosetRepresentatives 4233 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4233 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4233) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4233))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4233)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4233 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4233) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4233))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4233)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4234 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4234) = g32p_row18_cosetRepresentatives 4234 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4234 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4234) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4234))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4234)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4234 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4234) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4234))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4234)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4235 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4235) = g32p_row18_cosetRepresentatives 4235 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4235 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4235) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4235))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4235)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4235 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4235) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4235))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4235)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4236 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4236) = g32p_row18_cosetRepresentatives 4236 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4236 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4236) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4236))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4236)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4236 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4236) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4236))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4236)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4237 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4237) = g32p_row18_cosetRepresentatives 4237 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4237 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4237) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4237))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4237)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4237 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4237) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4237))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4237)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4238 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4238) = g32p_row18_cosetRepresentatives 4238 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4238 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4238) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4238))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4238)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4238 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4238) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4238))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4238)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4239 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4239) = g32p_row18_cosetRepresentatives 4239 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4239 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4239) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4239))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4239)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4239 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4239) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4239))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4239)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0264 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 264 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 264 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4224
  · exact g32p_row18_cosetWord_4225
  · exact g32p_row18_cosetWord_4226
  · exact g32p_row18_cosetWord_4227
  · exact g32p_row18_cosetWord_4228
  · exact g32p_row18_cosetWord_4229
  · exact g32p_row18_cosetWord_4230
  · exact g32p_row18_cosetWord_4231
  · exact g32p_row18_cosetWord_4232
  · exact g32p_row18_cosetWord_4233
  · exact g32p_row18_cosetWord_4234
  · exact g32p_row18_cosetWord_4235
  · exact g32p_row18_cosetWord_4236
  · exact g32p_row18_cosetWord_4237
  · exact g32p_row18_cosetWord_4238
  · exact g32p_row18_cosetWord_4239

theorem g32p_row18_cosetGeneratorBlock_0264 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 264 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 264 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 264 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4224 s
  · exact g32p_row18_cosetGeneratorStep_4225 s
  · exact g32p_row18_cosetGeneratorStep_4226 s
  · exact g32p_row18_cosetGeneratorStep_4227 s
  · exact g32p_row18_cosetGeneratorStep_4228 s
  · exact g32p_row18_cosetGeneratorStep_4229 s
  · exact g32p_row18_cosetGeneratorStep_4230 s
  · exact g32p_row18_cosetGeneratorStep_4231 s
  · exact g32p_row18_cosetGeneratorStep_4232 s
  · exact g32p_row18_cosetGeneratorStep_4233 s
  · exact g32p_row18_cosetGeneratorStep_4234 s
  · exact g32p_row18_cosetGeneratorStep_4235 s
  · exact g32p_row18_cosetGeneratorStep_4236 s
  · exact g32p_row18_cosetGeneratorStep_4237 s
  · exact g32p_row18_cosetGeneratorStep_4238 s
  · exact g32p_row18_cosetGeneratorStep_4239 s

theorem g32p_row18_cosetBranchBlock_0264 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 264 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 264 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 264 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4224 s
  · exact g32p_row18_cosetBranchStep_4225 s
  · exact g32p_row18_cosetBranchStep_4226 s
  · exact g32p_row18_cosetBranchStep_4227 s
  · exact g32p_row18_cosetBranchStep_4228 s
  · exact g32p_row18_cosetBranchStep_4229 s
  · exact g32p_row18_cosetBranchStep_4230 s
  · exact g32p_row18_cosetBranchStep_4231 s
  · exact g32p_row18_cosetBranchStep_4232 s
  · exact g32p_row18_cosetBranchStep_4233 s
  · exact g32p_row18_cosetBranchStep_4234 s
  · exact g32p_row18_cosetBranchStep_4235 s
  · exact g32p_row18_cosetBranchStep_4236 s
  · exact g32p_row18_cosetBranchStep_4237 s
  · exact g32p_row18_cosetBranchStep_4238 s
  · exact g32p_row18_cosetBranchStep_4239 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4240 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4240) = g32p_row18_cosetRepresentatives 4240 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4240 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4240) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4240))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4240)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4240 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4240) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4240))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4240)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4241 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4241) = g32p_row18_cosetRepresentatives 4241 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4241 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4241) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4241))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4241)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4241 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4241) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4241))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4241)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4242 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4242) = g32p_row18_cosetRepresentatives 4242 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4242 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4242) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4242))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4242)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4242 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4242) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4242))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4242)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4243 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4243) = g32p_row18_cosetRepresentatives 4243 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4243 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4243) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4243))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4243)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4243 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4243) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4243))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4243)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4244 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4244) = g32p_row18_cosetRepresentatives 4244 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4244 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4244) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4244))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4244)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4244 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4244) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4244))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4244)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4245 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4245) = g32p_row18_cosetRepresentatives 4245 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4245 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4245) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4245))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4245)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4245 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4245) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4245))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4245)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4246 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4246) = g32p_row18_cosetRepresentatives 4246 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4246 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4246) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4246))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4246)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4246 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4246) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4246))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4246)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4247 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4247) = g32p_row18_cosetRepresentatives 4247 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4247 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4247) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4247))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4247)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4247 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4247) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4247))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4247)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4248 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4248) = g32p_row18_cosetRepresentatives 4248 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4248 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4248) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4248))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4248)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4248 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4248) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4248))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4248)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4249 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4249) = g32p_row18_cosetRepresentatives 4249 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4249 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4249) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4249))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4249)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4249 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4249) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4249))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4249)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4250 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4250) = g32p_row18_cosetRepresentatives 4250 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4250 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4250) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4250))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4250)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4250 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4250) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4250))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4250)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4251 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4251) = g32p_row18_cosetRepresentatives 4251 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4251 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4251) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4251))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4251)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4251 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4251) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4251))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4251)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4252 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4252) = g32p_row18_cosetRepresentatives 4252 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4252 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4252) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4252))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4252)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4252 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4252) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4252))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4252)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4253 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4253) = g32p_row18_cosetRepresentatives 4253 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4253 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4253) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4253))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4253)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4253 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4253) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4253))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4253)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4254 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4254) = g32p_row18_cosetRepresentatives 4254 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4254 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4254) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4254))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4254)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4254 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4254) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4254))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4254)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4255 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4255) = g32p_row18_cosetRepresentatives 4255 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4255 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4255) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4255))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4255)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4255 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4255) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4255))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4255)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0265 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 265 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 265 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4240
  · exact g32p_row18_cosetWord_4241
  · exact g32p_row18_cosetWord_4242
  · exact g32p_row18_cosetWord_4243
  · exact g32p_row18_cosetWord_4244
  · exact g32p_row18_cosetWord_4245
  · exact g32p_row18_cosetWord_4246
  · exact g32p_row18_cosetWord_4247
  · exact g32p_row18_cosetWord_4248
  · exact g32p_row18_cosetWord_4249
  · exact g32p_row18_cosetWord_4250
  · exact g32p_row18_cosetWord_4251
  · exact g32p_row18_cosetWord_4252
  · exact g32p_row18_cosetWord_4253
  · exact g32p_row18_cosetWord_4254
  · exact g32p_row18_cosetWord_4255

theorem g32p_row18_cosetGeneratorBlock_0265 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 265 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 265 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 265 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4240 s
  · exact g32p_row18_cosetGeneratorStep_4241 s
  · exact g32p_row18_cosetGeneratorStep_4242 s
  · exact g32p_row18_cosetGeneratorStep_4243 s
  · exact g32p_row18_cosetGeneratorStep_4244 s
  · exact g32p_row18_cosetGeneratorStep_4245 s
  · exact g32p_row18_cosetGeneratorStep_4246 s
  · exact g32p_row18_cosetGeneratorStep_4247 s
  · exact g32p_row18_cosetGeneratorStep_4248 s
  · exact g32p_row18_cosetGeneratorStep_4249 s
  · exact g32p_row18_cosetGeneratorStep_4250 s
  · exact g32p_row18_cosetGeneratorStep_4251 s
  · exact g32p_row18_cosetGeneratorStep_4252 s
  · exact g32p_row18_cosetGeneratorStep_4253 s
  · exact g32p_row18_cosetGeneratorStep_4254 s
  · exact g32p_row18_cosetGeneratorStep_4255 s

theorem g32p_row18_cosetBranchBlock_0265 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 265 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 265 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 265 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4240 s
  · exact g32p_row18_cosetBranchStep_4241 s
  · exact g32p_row18_cosetBranchStep_4242 s
  · exact g32p_row18_cosetBranchStep_4243 s
  · exact g32p_row18_cosetBranchStep_4244 s
  · exact g32p_row18_cosetBranchStep_4245 s
  · exact g32p_row18_cosetBranchStep_4246 s
  · exact g32p_row18_cosetBranchStep_4247 s
  · exact g32p_row18_cosetBranchStep_4248 s
  · exact g32p_row18_cosetBranchStep_4249 s
  · exact g32p_row18_cosetBranchStep_4250 s
  · exact g32p_row18_cosetBranchStep_4251 s
  · exact g32p_row18_cosetBranchStep_4252 s
  · exact g32p_row18_cosetBranchStep_4253 s
  · exact g32p_row18_cosetBranchStep_4254 s
  · exact g32p_row18_cosetBranchStep_4255 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4256 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4256) = g32p_row18_cosetRepresentatives 4256 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4256) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4256))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4256)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4256) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4256))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4256)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4257 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4257) = g32p_row18_cosetRepresentatives 4257 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4257) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4257))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4257)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4257) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4257))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4257)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4258 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4258) = g32p_row18_cosetRepresentatives 4258 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4258) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4258))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4258)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4258) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4258))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4258)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4259 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4259) = g32p_row18_cosetRepresentatives 4259 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4259) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4259))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4259)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4259) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4259))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4259)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4260 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4260) = g32p_row18_cosetRepresentatives 4260 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4260) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4260))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4260)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4260) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4260))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4260)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4261 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4261) = g32p_row18_cosetRepresentatives 4261 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4261) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4261))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4261)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4261) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4261))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4261)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4262 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4262) = g32p_row18_cosetRepresentatives 4262 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4262) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4262))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4262)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4262) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4262))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4262)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4263 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4263) = g32p_row18_cosetRepresentatives 4263 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4263) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4263))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4263)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4263) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4263))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4263)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4264 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4264) = g32p_row18_cosetRepresentatives 4264 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4264) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4264))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4264)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4264) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4264))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4264)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4265 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4265) = g32p_row18_cosetRepresentatives 4265 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4265) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4265))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4265)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4265) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4265))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4265)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4266 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4266) = g32p_row18_cosetRepresentatives 4266 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4266) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4266))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4266)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4266) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4266))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4266)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4267 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4267) = g32p_row18_cosetRepresentatives 4267 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4267) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4267))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4267)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4267) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4267))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4267)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4268 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4268) = g32p_row18_cosetRepresentatives 4268 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4268) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4268))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4268)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4268) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4268))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4268)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4269 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4269) = g32p_row18_cosetRepresentatives 4269 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4269) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4269))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4269)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4269) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4269))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4269)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4270 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4270) = g32p_row18_cosetRepresentatives 4270 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4270) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4270))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4270)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4270) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4270))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4270)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4271 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4271) = g32p_row18_cosetRepresentatives 4271 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4271) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4271))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4271)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4271) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4271))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4271)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0266 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 266 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 266 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4256
  · exact g32p_row18_cosetWord_4257
  · exact g32p_row18_cosetWord_4258
  · exact g32p_row18_cosetWord_4259
  · exact g32p_row18_cosetWord_4260
  · exact g32p_row18_cosetWord_4261
  · exact g32p_row18_cosetWord_4262
  · exact g32p_row18_cosetWord_4263
  · exact g32p_row18_cosetWord_4264
  · exact g32p_row18_cosetWord_4265
  · exact g32p_row18_cosetWord_4266
  · exact g32p_row18_cosetWord_4267
  · exact g32p_row18_cosetWord_4268
  · exact g32p_row18_cosetWord_4269
  · exact g32p_row18_cosetWord_4270
  · exact g32p_row18_cosetWord_4271

theorem g32p_row18_cosetGeneratorBlock_0266 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 266 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 266 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 266 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4256 s
  · exact g32p_row18_cosetGeneratorStep_4257 s
  · exact g32p_row18_cosetGeneratorStep_4258 s
  · exact g32p_row18_cosetGeneratorStep_4259 s
  · exact g32p_row18_cosetGeneratorStep_4260 s
  · exact g32p_row18_cosetGeneratorStep_4261 s
  · exact g32p_row18_cosetGeneratorStep_4262 s
  · exact g32p_row18_cosetGeneratorStep_4263 s
  · exact g32p_row18_cosetGeneratorStep_4264 s
  · exact g32p_row18_cosetGeneratorStep_4265 s
  · exact g32p_row18_cosetGeneratorStep_4266 s
  · exact g32p_row18_cosetGeneratorStep_4267 s
  · exact g32p_row18_cosetGeneratorStep_4268 s
  · exact g32p_row18_cosetGeneratorStep_4269 s
  · exact g32p_row18_cosetGeneratorStep_4270 s
  · exact g32p_row18_cosetGeneratorStep_4271 s

theorem g32p_row18_cosetBranchBlock_0266 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 266 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 266 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 266 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4256 s
  · exact g32p_row18_cosetBranchStep_4257 s
  · exact g32p_row18_cosetBranchStep_4258 s
  · exact g32p_row18_cosetBranchStep_4259 s
  · exact g32p_row18_cosetBranchStep_4260 s
  · exact g32p_row18_cosetBranchStep_4261 s
  · exact g32p_row18_cosetBranchStep_4262 s
  · exact g32p_row18_cosetBranchStep_4263 s
  · exact g32p_row18_cosetBranchStep_4264 s
  · exact g32p_row18_cosetBranchStep_4265 s
  · exact g32p_row18_cosetBranchStep_4266 s
  · exact g32p_row18_cosetBranchStep_4267 s
  · exact g32p_row18_cosetBranchStep_4268 s
  · exact g32p_row18_cosetBranchStep_4269 s
  · exact g32p_row18_cosetBranchStep_4270 s
  · exact g32p_row18_cosetBranchStep_4271 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4272 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4272) = g32p_row18_cosetRepresentatives 4272 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4272) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4272))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4272)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4272) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4272))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4272)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4273 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4273) = g32p_row18_cosetRepresentatives 4273 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4273) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4273))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4273)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4273) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4273))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4273)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4274 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4274) = g32p_row18_cosetRepresentatives 4274 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4274) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4274))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4274)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4274) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4274))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4274)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4275 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4275) = g32p_row18_cosetRepresentatives 4275 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4275) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4275))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4275)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4275) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4275))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4275)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4276 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4276) = g32p_row18_cosetRepresentatives 4276 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4276) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4276))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4276)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4276) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4276))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4276)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4277 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4277) = g32p_row18_cosetRepresentatives 4277 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4277) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4277))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4277)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4277) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4277))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4277)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4278 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4278) = g32p_row18_cosetRepresentatives 4278 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4278) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4278))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4278)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4278) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4278))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4278)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4279 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4279) = g32p_row18_cosetRepresentatives 4279 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4279) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4279))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4279)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4279) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4279))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4279)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4280 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4280) = g32p_row18_cosetRepresentatives 4280 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4280) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4280))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4280)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4280) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4280))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4280)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4281 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4281) = g32p_row18_cosetRepresentatives 4281 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4281) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4281))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4281)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4281) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4281))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4281)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4282 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4282) = g32p_row18_cosetRepresentatives 4282 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4282) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4282))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4282)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4282) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4282))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4282)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4283 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4283) = g32p_row18_cosetRepresentatives 4283 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4283) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4283))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4283)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4283) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4283))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4283)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4284 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4284) = g32p_row18_cosetRepresentatives 4284 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4284) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4284))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4284)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4284) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4284))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4284)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4285 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4285) = g32p_row18_cosetRepresentatives 4285 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4285) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4285))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4285)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4285) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4285))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4285)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4286 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4286) = g32p_row18_cosetRepresentatives 4286 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4286) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4286))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4286)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4286) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4286))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4286)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4287 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4287) = g32p_row18_cosetRepresentatives 4287 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4287) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4287))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4287)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4287) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4287))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4287)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0267 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 267 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 267 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4272
  · exact g32p_row18_cosetWord_4273
  · exact g32p_row18_cosetWord_4274
  · exact g32p_row18_cosetWord_4275
  · exact g32p_row18_cosetWord_4276
  · exact g32p_row18_cosetWord_4277
  · exact g32p_row18_cosetWord_4278
  · exact g32p_row18_cosetWord_4279
  · exact g32p_row18_cosetWord_4280
  · exact g32p_row18_cosetWord_4281
  · exact g32p_row18_cosetWord_4282
  · exact g32p_row18_cosetWord_4283
  · exact g32p_row18_cosetWord_4284
  · exact g32p_row18_cosetWord_4285
  · exact g32p_row18_cosetWord_4286
  · exact g32p_row18_cosetWord_4287

theorem g32p_row18_cosetGeneratorBlock_0267 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 267 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 267 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 267 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4272 s
  · exact g32p_row18_cosetGeneratorStep_4273 s
  · exact g32p_row18_cosetGeneratorStep_4274 s
  · exact g32p_row18_cosetGeneratorStep_4275 s
  · exact g32p_row18_cosetGeneratorStep_4276 s
  · exact g32p_row18_cosetGeneratorStep_4277 s
  · exact g32p_row18_cosetGeneratorStep_4278 s
  · exact g32p_row18_cosetGeneratorStep_4279 s
  · exact g32p_row18_cosetGeneratorStep_4280 s
  · exact g32p_row18_cosetGeneratorStep_4281 s
  · exact g32p_row18_cosetGeneratorStep_4282 s
  · exact g32p_row18_cosetGeneratorStep_4283 s
  · exact g32p_row18_cosetGeneratorStep_4284 s
  · exact g32p_row18_cosetGeneratorStep_4285 s
  · exact g32p_row18_cosetGeneratorStep_4286 s
  · exact g32p_row18_cosetGeneratorStep_4287 s

theorem g32p_row18_cosetBranchBlock_0267 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 267 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 267 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 267 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4272 s
  · exact g32p_row18_cosetBranchStep_4273 s
  · exact g32p_row18_cosetBranchStep_4274 s
  · exact g32p_row18_cosetBranchStep_4275 s
  · exact g32p_row18_cosetBranchStep_4276 s
  · exact g32p_row18_cosetBranchStep_4277 s
  · exact g32p_row18_cosetBranchStep_4278 s
  · exact g32p_row18_cosetBranchStep_4279 s
  · exact g32p_row18_cosetBranchStep_4280 s
  · exact g32p_row18_cosetBranchStep_4281 s
  · exact g32p_row18_cosetBranchStep_4282 s
  · exact g32p_row18_cosetBranchStep_4283 s
  · exact g32p_row18_cosetBranchStep_4284 s
  · exact g32p_row18_cosetBranchStep_4285 s
  · exact g32p_row18_cosetBranchStep_4286 s
  · exact g32p_row18_cosetBranchStep_4287 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4288 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4288) = g32p_row18_cosetRepresentatives 4288 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4288) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4288))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4288)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4288) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4288))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4288)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4289 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4289) = g32p_row18_cosetRepresentatives 4289 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4289) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4289))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4289)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4289) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4289))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4289)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4290 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4290) = g32p_row18_cosetRepresentatives 4290 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4290) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4290))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4290)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4290) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4290))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4290)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4291 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4291) = g32p_row18_cosetRepresentatives 4291 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4291) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4291))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4291)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4291) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4291))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4291)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4292 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4292) = g32p_row18_cosetRepresentatives 4292 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4292) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4292))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4292)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4292) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4292))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4292)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4293 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4293) = g32p_row18_cosetRepresentatives 4293 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4293) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4293))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4293)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4293) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4293))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4293)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4294 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4294) = g32p_row18_cosetRepresentatives 4294 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4294) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4294))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4294)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4294) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4294))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4294)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4295 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4295) = g32p_row18_cosetRepresentatives 4295 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4295) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4295))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4295)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4295) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4295))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4295)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4296 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4296) = g32p_row18_cosetRepresentatives 4296 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4296) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4296))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4296)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4296) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4296))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4296)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4297 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4297) = g32p_row18_cosetRepresentatives 4297 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4297) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4297))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4297)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4297) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4297))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4297)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4298 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4298) = g32p_row18_cosetRepresentatives 4298 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4298) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4298))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4298)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4298) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4298))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4298)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4299 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4299) = g32p_row18_cosetRepresentatives 4299 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4299) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4299))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4299)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4299) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4299))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4299)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4300 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4300) = g32p_row18_cosetRepresentatives 4300 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4300) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4300))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4300)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4300) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4300))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4300)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4301 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4301) = g32p_row18_cosetRepresentatives 4301 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4301) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4301))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4301)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4301) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4301))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4301)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4302 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4302) = g32p_row18_cosetRepresentatives 4302 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4302) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4302))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4302)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4302) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4302))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4302)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4303 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4303) = g32p_row18_cosetRepresentatives 4303 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4303) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4303))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4303)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4303) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4303))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4303)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0268 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 268 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 268 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4288
  · exact g32p_row18_cosetWord_4289
  · exact g32p_row18_cosetWord_4290
  · exact g32p_row18_cosetWord_4291
  · exact g32p_row18_cosetWord_4292
  · exact g32p_row18_cosetWord_4293
  · exact g32p_row18_cosetWord_4294
  · exact g32p_row18_cosetWord_4295
  · exact g32p_row18_cosetWord_4296
  · exact g32p_row18_cosetWord_4297
  · exact g32p_row18_cosetWord_4298
  · exact g32p_row18_cosetWord_4299
  · exact g32p_row18_cosetWord_4300
  · exact g32p_row18_cosetWord_4301
  · exact g32p_row18_cosetWord_4302
  · exact g32p_row18_cosetWord_4303

theorem g32p_row18_cosetGeneratorBlock_0268 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 268 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 268 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 268 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4288 s
  · exact g32p_row18_cosetGeneratorStep_4289 s
  · exact g32p_row18_cosetGeneratorStep_4290 s
  · exact g32p_row18_cosetGeneratorStep_4291 s
  · exact g32p_row18_cosetGeneratorStep_4292 s
  · exact g32p_row18_cosetGeneratorStep_4293 s
  · exact g32p_row18_cosetGeneratorStep_4294 s
  · exact g32p_row18_cosetGeneratorStep_4295 s
  · exact g32p_row18_cosetGeneratorStep_4296 s
  · exact g32p_row18_cosetGeneratorStep_4297 s
  · exact g32p_row18_cosetGeneratorStep_4298 s
  · exact g32p_row18_cosetGeneratorStep_4299 s
  · exact g32p_row18_cosetGeneratorStep_4300 s
  · exact g32p_row18_cosetGeneratorStep_4301 s
  · exact g32p_row18_cosetGeneratorStep_4302 s
  · exact g32p_row18_cosetGeneratorStep_4303 s

theorem g32p_row18_cosetBranchBlock_0268 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 268 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 268 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 268 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4288 s
  · exact g32p_row18_cosetBranchStep_4289 s
  · exact g32p_row18_cosetBranchStep_4290 s
  · exact g32p_row18_cosetBranchStep_4291 s
  · exact g32p_row18_cosetBranchStep_4292 s
  · exact g32p_row18_cosetBranchStep_4293 s
  · exact g32p_row18_cosetBranchStep_4294 s
  · exact g32p_row18_cosetBranchStep_4295 s
  · exact g32p_row18_cosetBranchStep_4296 s
  · exact g32p_row18_cosetBranchStep_4297 s
  · exact g32p_row18_cosetBranchStep_4298 s
  · exact g32p_row18_cosetBranchStep_4299 s
  · exact g32p_row18_cosetBranchStep_4300 s
  · exact g32p_row18_cosetBranchStep_4301 s
  · exact g32p_row18_cosetBranchStep_4302 s
  · exact g32p_row18_cosetBranchStep_4303 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_4304 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4304) = g32p_row18_cosetRepresentatives 4304 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4304) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4304))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4304)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4304) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4304))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4304)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4305 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4305) = g32p_row18_cosetRepresentatives 4305 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4305) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4305))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4305)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4305) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4305))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4305)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4306 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4306) = g32p_row18_cosetRepresentatives 4306 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4306) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4306))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4306)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4306) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4306))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4306)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4307 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4307) = g32p_row18_cosetRepresentatives 4307 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4307) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4307))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4307)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4307) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4307))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4307)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4308 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4308) = g32p_row18_cosetRepresentatives 4308 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4308) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4308))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4308)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4308) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4308))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4308)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4309 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4309) = g32p_row18_cosetRepresentatives 4309 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4309) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4309))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4309)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4309) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4309))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4309)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4310 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4310) = g32p_row18_cosetRepresentatives 4310 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4310) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4310))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4310)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4310) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4310))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4310)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4311 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4311) = g32p_row18_cosetRepresentatives 4311 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4311) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4311))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4311)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4311) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4311))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4311)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4312 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4312) = g32p_row18_cosetRepresentatives 4312 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4312) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4312))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4312)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4312) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4312))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4312)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4313 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4313) = g32p_row18_cosetRepresentatives 4313 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4313) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4313))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4313)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4313) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4313))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4313)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4314 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4314) = g32p_row18_cosetRepresentatives 4314 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4314) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4314))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4314)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4314) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4314))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4314)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4315 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4315) = g32p_row18_cosetRepresentatives 4315 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4315) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4315))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4315)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4315) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4315))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4315)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4316 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4316) = g32p_row18_cosetRepresentatives 4316 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4316) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4316))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4316)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4316) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4316))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4316)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4317 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4317) = g32p_row18_cosetRepresentatives 4317 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4317) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4317))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4317)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4317) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4317))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4317)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4318 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4318) = g32p_row18_cosetRepresentatives 4318 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4318) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4318))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4318)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4318) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4318))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4318)) := by
  decide +kernel

theorem g32p_row18_cosetWord_4319 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 4319) = g32p_row18_cosetRepresentatives 4319 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_4319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 4319) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 4319))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 4319)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_4319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 4319) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 4319))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 4319)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0269 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 269 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 269 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_4304
  · exact g32p_row18_cosetWord_4305
  · exact g32p_row18_cosetWord_4306
  · exact g32p_row18_cosetWord_4307
  · exact g32p_row18_cosetWord_4308
  · exact g32p_row18_cosetWord_4309
  · exact g32p_row18_cosetWord_4310
  · exact g32p_row18_cosetWord_4311
  · exact g32p_row18_cosetWord_4312
  · exact g32p_row18_cosetWord_4313
  · exact g32p_row18_cosetWord_4314
  · exact g32p_row18_cosetWord_4315
  · exact g32p_row18_cosetWord_4316
  · exact g32p_row18_cosetWord_4317
  · exact g32p_row18_cosetWord_4318
  · exact g32p_row18_cosetWord_4319

theorem g32p_row18_cosetGeneratorBlock_0269 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 269 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 269 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 269 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_4304 s
  · exact g32p_row18_cosetGeneratorStep_4305 s
  · exact g32p_row18_cosetGeneratorStep_4306 s
  · exact g32p_row18_cosetGeneratorStep_4307 s
  · exact g32p_row18_cosetGeneratorStep_4308 s
  · exact g32p_row18_cosetGeneratorStep_4309 s
  · exact g32p_row18_cosetGeneratorStep_4310 s
  · exact g32p_row18_cosetGeneratorStep_4311 s
  · exact g32p_row18_cosetGeneratorStep_4312 s
  · exact g32p_row18_cosetGeneratorStep_4313 s
  · exact g32p_row18_cosetGeneratorStep_4314 s
  · exact g32p_row18_cosetGeneratorStep_4315 s
  · exact g32p_row18_cosetGeneratorStep_4316 s
  · exact g32p_row18_cosetGeneratorStep_4317 s
  · exact g32p_row18_cosetGeneratorStep_4318 s
  · exact g32p_row18_cosetGeneratorStep_4319 s

theorem g32p_row18_cosetBranchBlock_0269 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 269 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 269 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 269 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_4304 s
  · exact g32p_row18_cosetBranchStep_4305 s
  · exact g32p_row18_cosetBranchStep_4306 s
  · exact g32p_row18_cosetBranchStep_4307 s
  · exact g32p_row18_cosetBranchStep_4308 s
  · exact g32p_row18_cosetBranchStep_4309 s
  · exact g32p_row18_cosetBranchStep_4310 s
  · exact g32p_row18_cosetBranchStep_4311 s
  · exact g32p_row18_cosetBranchStep_4312 s
  · exact g32p_row18_cosetBranchStep_4313 s
  · exact g32p_row18_cosetBranchStep_4314 s
  · exact g32p_row18_cosetBranchStep_4315 s
  · exact g32p_row18_cosetBranchStep_4316 s
  · exact g32p_row18_cosetBranchStep_4317 s
  · exact g32p_row18_cosetBranchStep_4318 s
  · exact g32p_row18_cosetBranchStep_4319 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

theorem g32p_row18_cosetWord (i : Fin 4320) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords i) = g32p_row18_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row18_cosetWordBlock_0000
  · exact g32p_row18_cosetWordBlock_0001
  · exact g32p_row18_cosetWordBlock_0002
  · exact g32p_row18_cosetWordBlock_0003
  · exact g32p_row18_cosetWordBlock_0004
  · exact g32p_row18_cosetWordBlock_0005
  · exact g32p_row18_cosetWordBlock_0006
  · exact g32p_row18_cosetWordBlock_0007
  · exact g32p_row18_cosetWordBlock_0008
  · exact g32p_row18_cosetWordBlock_0009
  · exact g32p_row18_cosetWordBlock_0010
  · exact g32p_row18_cosetWordBlock_0011
  · exact g32p_row18_cosetWordBlock_0012
  · exact g32p_row18_cosetWordBlock_0013
  · exact g32p_row18_cosetWordBlock_0014
  · exact g32p_row18_cosetWordBlock_0015
  · exact g32p_row18_cosetWordBlock_0016
  · exact g32p_row18_cosetWordBlock_0017
  · exact g32p_row18_cosetWordBlock_0018
  · exact g32p_row18_cosetWordBlock_0019
  · exact g32p_row18_cosetWordBlock_0020
  · exact g32p_row18_cosetWordBlock_0021
  · exact g32p_row18_cosetWordBlock_0022
  · exact g32p_row18_cosetWordBlock_0023
  · exact g32p_row18_cosetWordBlock_0024
  · exact g32p_row18_cosetWordBlock_0025
  · exact g32p_row18_cosetWordBlock_0026
  · exact g32p_row18_cosetWordBlock_0027
  · exact g32p_row18_cosetWordBlock_0028
  · exact g32p_row18_cosetWordBlock_0029
  · exact g32p_row18_cosetWordBlock_0030
  · exact g32p_row18_cosetWordBlock_0031
  · exact g32p_row18_cosetWordBlock_0032
  · exact g32p_row18_cosetWordBlock_0033
  · exact g32p_row18_cosetWordBlock_0034
  · exact g32p_row18_cosetWordBlock_0035
  · exact g32p_row18_cosetWordBlock_0036
  · exact g32p_row18_cosetWordBlock_0037
  · exact g32p_row18_cosetWordBlock_0038
  · exact g32p_row18_cosetWordBlock_0039
  · exact g32p_row18_cosetWordBlock_0040
  · exact g32p_row18_cosetWordBlock_0041
  · exact g32p_row18_cosetWordBlock_0042
  · exact g32p_row18_cosetWordBlock_0043
  · exact g32p_row18_cosetWordBlock_0044
  · exact g32p_row18_cosetWordBlock_0045
  · exact g32p_row18_cosetWordBlock_0046
  · exact g32p_row18_cosetWordBlock_0047
  · exact g32p_row18_cosetWordBlock_0048
  · exact g32p_row18_cosetWordBlock_0049
  · exact g32p_row18_cosetWordBlock_0050
  · exact g32p_row18_cosetWordBlock_0051
  · exact g32p_row18_cosetWordBlock_0052
  · exact g32p_row18_cosetWordBlock_0053
  · exact g32p_row18_cosetWordBlock_0054
  · exact g32p_row18_cosetWordBlock_0055
  · exact g32p_row18_cosetWordBlock_0056
  · exact g32p_row18_cosetWordBlock_0057
  · exact g32p_row18_cosetWordBlock_0058
  · exact g32p_row18_cosetWordBlock_0059
  · exact g32p_row18_cosetWordBlock_0060
  · exact g32p_row18_cosetWordBlock_0061
  · exact g32p_row18_cosetWordBlock_0062
  · exact g32p_row18_cosetWordBlock_0063
  · exact g32p_row18_cosetWordBlock_0064
  · exact g32p_row18_cosetWordBlock_0065
  · exact g32p_row18_cosetWordBlock_0066
  · exact g32p_row18_cosetWordBlock_0067
  · exact g32p_row18_cosetWordBlock_0068
  · exact g32p_row18_cosetWordBlock_0069
  · exact g32p_row18_cosetWordBlock_0070
  · exact g32p_row18_cosetWordBlock_0071
  · exact g32p_row18_cosetWordBlock_0072
  · exact g32p_row18_cosetWordBlock_0073
  · exact g32p_row18_cosetWordBlock_0074
  · exact g32p_row18_cosetWordBlock_0075
  · exact g32p_row18_cosetWordBlock_0076
  · exact g32p_row18_cosetWordBlock_0077
  · exact g32p_row18_cosetWordBlock_0078
  · exact g32p_row18_cosetWordBlock_0079
  · exact g32p_row18_cosetWordBlock_0080
  · exact g32p_row18_cosetWordBlock_0081
  · exact g32p_row18_cosetWordBlock_0082
  · exact g32p_row18_cosetWordBlock_0083
  · exact g32p_row18_cosetWordBlock_0084
  · exact g32p_row18_cosetWordBlock_0085
  · exact g32p_row18_cosetWordBlock_0086
  · exact g32p_row18_cosetWordBlock_0087
  · exact g32p_row18_cosetWordBlock_0088
  · exact g32p_row18_cosetWordBlock_0089
  · exact g32p_row18_cosetWordBlock_0090
  · exact g32p_row18_cosetWordBlock_0091
  · exact g32p_row18_cosetWordBlock_0092
  · exact g32p_row18_cosetWordBlock_0093
  · exact g32p_row18_cosetWordBlock_0094
  · exact g32p_row18_cosetWordBlock_0095
  · exact g32p_row18_cosetWordBlock_0096
  · exact g32p_row18_cosetWordBlock_0097
  · exact g32p_row18_cosetWordBlock_0098
  · exact g32p_row18_cosetWordBlock_0099
  · exact g32p_row18_cosetWordBlock_0100
  · exact g32p_row18_cosetWordBlock_0101
  · exact g32p_row18_cosetWordBlock_0102
  · exact g32p_row18_cosetWordBlock_0103
  · exact g32p_row18_cosetWordBlock_0104
  · exact g32p_row18_cosetWordBlock_0105
  · exact g32p_row18_cosetWordBlock_0106
  · exact g32p_row18_cosetWordBlock_0107
  · exact g32p_row18_cosetWordBlock_0108
  · exact g32p_row18_cosetWordBlock_0109
  · exact g32p_row18_cosetWordBlock_0110
  · exact g32p_row18_cosetWordBlock_0111
  · exact g32p_row18_cosetWordBlock_0112
  · exact g32p_row18_cosetWordBlock_0113
  · exact g32p_row18_cosetWordBlock_0114
  · exact g32p_row18_cosetWordBlock_0115
  · exact g32p_row18_cosetWordBlock_0116
  · exact g32p_row18_cosetWordBlock_0117
  · exact g32p_row18_cosetWordBlock_0118
  · exact g32p_row18_cosetWordBlock_0119
  · exact g32p_row18_cosetWordBlock_0120
  · exact g32p_row18_cosetWordBlock_0121
  · exact g32p_row18_cosetWordBlock_0122
  · exact g32p_row18_cosetWordBlock_0123
  · exact g32p_row18_cosetWordBlock_0124
  · exact g32p_row18_cosetWordBlock_0125
  · exact g32p_row18_cosetWordBlock_0126
  · exact g32p_row18_cosetWordBlock_0127
  · exact g32p_row18_cosetWordBlock_0128
  · exact g32p_row18_cosetWordBlock_0129
  · exact g32p_row18_cosetWordBlock_0130
  · exact g32p_row18_cosetWordBlock_0131
  · exact g32p_row18_cosetWordBlock_0132
  · exact g32p_row18_cosetWordBlock_0133
  · exact g32p_row18_cosetWordBlock_0134
  · exact g32p_row18_cosetWordBlock_0135
  · exact g32p_row18_cosetWordBlock_0136
  · exact g32p_row18_cosetWordBlock_0137
  · exact g32p_row18_cosetWordBlock_0138
  · exact g32p_row18_cosetWordBlock_0139
  · exact g32p_row18_cosetWordBlock_0140
  · exact g32p_row18_cosetWordBlock_0141
  · exact g32p_row18_cosetWordBlock_0142
  · exact g32p_row18_cosetWordBlock_0143
  · exact g32p_row18_cosetWordBlock_0144
  · exact g32p_row18_cosetWordBlock_0145
  · exact g32p_row18_cosetWordBlock_0146
  · exact g32p_row18_cosetWordBlock_0147
  · exact g32p_row18_cosetWordBlock_0148
  · exact g32p_row18_cosetWordBlock_0149
  · exact g32p_row18_cosetWordBlock_0150
  · exact g32p_row18_cosetWordBlock_0151
  · exact g32p_row18_cosetWordBlock_0152
  · exact g32p_row18_cosetWordBlock_0153
  · exact g32p_row18_cosetWordBlock_0154
  · exact g32p_row18_cosetWordBlock_0155
  · exact g32p_row18_cosetWordBlock_0156
  · exact g32p_row18_cosetWordBlock_0157
  · exact g32p_row18_cosetWordBlock_0158
  · exact g32p_row18_cosetWordBlock_0159
  · exact g32p_row18_cosetWordBlock_0160
  · exact g32p_row18_cosetWordBlock_0161
  · exact g32p_row18_cosetWordBlock_0162
  · exact g32p_row18_cosetWordBlock_0163
  · exact g32p_row18_cosetWordBlock_0164
  · exact g32p_row18_cosetWordBlock_0165
  · exact g32p_row18_cosetWordBlock_0166
  · exact g32p_row18_cosetWordBlock_0167
  · exact g32p_row18_cosetWordBlock_0168
  · exact g32p_row18_cosetWordBlock_0169
  · exact g32p_row18_cosetWordBlock_0170
  · exact g32p_row18_cosetWordBlock_0171
  · exact g32p_row18_cosetWordBlock_0172
  · exact g32p_row18_cosetWordBlock_0173
  · exact g32p_row18_cosetWordBlock_0174
  · exact g32p_row18_cosetWordBlock_0175
  · exact g32p_row18_cosetWordBlock_0176
  · exact g32p_row18_cosetWordBlock_0177
  · exact g32p_row18_cosetWordBlock_0178
  · exact g32p_row18_cosetWordBlock_0179
  · exact g32p_row18_cosetWordBlock_0180
  · exact g32p_row18_cosetWordBlock_0181
  · exact g32p_row18_cosetWordBlock_0182
  · exact g32p_row18_cosetWordBlock_0183
  · exact g32p_row18_cosetWordBlock_0184
  · exact g32p_row18_cosetWordBlock_0185
  · exact g32p_row18_cosetWordBlock_0186
  · exact g32p_row18_cosetWordBlock_0187
  · exact g32p_row18_cosetWordBlock_0188
  · exact g32p_row18_cosetWordBlock_0189
  · exact g32p_row18_cosetWordBlock_0190
  · exact g32p_row18_cosetWordBlock_0191
  · exact g32p_row18_cosetWordBlock_0192
  · exact g32p_row18_cosetWordBlock_0193
  · exact g32p_row18_cosetWordBlock_0194
  · exact g32p_row18_cosetWordBlock_0195
  · exact g32p_row18_cosetWordBlock_0196
  · exact g32p_row18_cosetWordBlock_0197
  · exact g32p_row18_cosetWordBlock_0198
  · exact g32p_row18_cosetWordBlock_0199
  · exact g32p_row18_cosetWordBlock_0200
  · exact g32p_row18_cosetWordBlock_0201
  · exact g32p_row18_cosetWordBlock_0202
  · exact g32p_row18_cosetWordBlock_0203
  · exact g32p_row18_cosetWordBlock_0204
  · exact g32p_row18_cosetWordBlock_0205
  · exact g32p_row18_cosetWordBlock_0206
  · exact g32p_row18_cosetWordBlock_0207
  · exact g32p_row18_cosetWordBlock_0208
  · exact g32p_row18_cosetWordBlock_0209
  · exact g32p_row18_cosetWordBlock_0210
  · exact g32p_row18_cosetWordBlock_0211
  · exact g32p_row18_cosetWordBlock_0212
  · exact g32p_row18_cosetWordBlock_0213
  · exact g32p_row18_cosetWordBlock_0214
  · exact g32p_row18_cosetWordBlock_0215
  · exact g32p_row18_cosetWordBlock_0216
  · exact g32p_row18_cosetWordBlock_0217
  · exact g32p_row18_cosetWordBlock_0218
  · exact g32p_row18_cosetWordBlock_0219
  · exact g32p_row18_cosetWordBlock_0220
  · exact g32p_row18_cosetWordBlock_0221
  · exact g32p_row18_cosetWordBlock_0222
  · exact g32p_row18_cosetWordBlock_0223
  · exact g32p_row18_cosetWordBlock_0224
  · exact g32p_row18_cosetWordBlock_0225
  · exact g32p_row18_cosetWordBlock_0226
  · exact g32p_row18_cosetWordBlock_0227
  · exact g32p_row18_cosetWordBlock_0228
  · exact g32p_row18_cosetWordBlock_0229
  · exact g32p_row18_cosetWordBlock_0230
  · exact g32p_row18_cosetWordBlock_0231
  · exact g32p_row18_cosetWordBlock_0232
  · exact g32p_row18_cosetWordBlock_0233
  · exact g32p_row18_cosetWordBlock_0234
  · exact g32p_row18_cosetWordBlock_0235
  · exact g32p_row18_cosetWordBlock_0236
  · exact g32p_row18_cosetWordBlock_0237
  · exact g32p_row18_cosetWordBlock_0238
  · exact g32p_row18_cosetWordBlock_0239
  · exact g32p_row18_cosetWordBlock_0240
  · exact g32p_row18_cosetWordBlock_0241
  · exact g32p_row18_cosetWordBlock_0242
  · exact g32p_row18_cosetWordBlock_0243
  · exact g32p_row18_cosetWordBlock_0244
  · exact g32p_row18_cosetWordBlock_0245
  · exact g32p_row18_cosetWordBlock_0246
  · exact g32p_row18_cosetWordBlock_0247
  · exact g32p_row18_cosetWordBlock_0248
  · exact g32p_row18_cosetWordBlock_0249
  · exact g32p_row18_cosetWordBlock_0250
  · exact g32p_row18_cosetWordBlock_0251
  · exact g32p_row18_cosetWordBlock_0252
  · exact g32p_row18_cosetWordBlock_0253
  · exact g32p_row18_cosetWordBlock_0254
  · exact g32p_row18_cosetWordBlock_0255
  · exact g32p_row18_cosetWordBlock_0256
  · exact g32p_row18_cosetWordBlock_0257
  · exact g32p_row18_cosetWordBlock_0258
  · exact g32p_row18_cosetWordBlock_0259
  · exact g32p_row18_cosetWordBlock_0260
  · exact g32p_row18_cosetWordBlock_0261
  · exact g32p_row18_cosetWordBlock_0262
  · exact g32p_row18_cosetWordBlock_0263
  · exact g32p_row18_cosetWordBlock_0264
  · exact g32p_row18_cosetWordBlock_0265
  · exact g32p_row18_cosetWordBlock_0266
  · exact g32p_row18_cosetWordBlock_0267
  · exact g32p_row18_cosetWordBlock_0268
  · exact g32p_row18_cosetWordBlock_0269


def g32p_row18_cosetActualRepresentatives (i : Fin 4320) : g32p_G := g32p_archiveWord (g32p_row18_cosetWords i)

theorem g32p_row18_cosetActualRepresentatives_map (i : Fin 4320) :
    b4b_toMatrix (g32p_row18_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row18_cosetRepresentatives i)) := by
  rw [g32p_row18_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row18_cosetWord]

theorem g32p_row18_cosetGeneratorStep (s : Fin 4) (i : Fin 4320) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s i))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row18_cosetGeneratorBlock_0000 s
  · exact g32p_row18_cosetGeneratorBlock_0001 s
  · exact g32p_row18_cosetGeneratorBlock_0002 s
  · exact g32p_row18_cosetGeneratorBlock_0003 s
  · exact g32p_row18_cosetGeneratorBlock_0004 s
  · exact g32p_row18_cosetGeneratorBlock_0005 s
  · exact g32p_row18_cosetGeneratorBlock_0006 s
  · exact g32p_row18_cosetGeneratorBlock_0007 s
  · exact g32p_row18_cosetGeneratorBlock_0008 s
  · exact g32p_row18_cosetGeneratorBlock_0009 s
  · exact g32p_row18_cosetGeneratorBlock_0010 s
  · exact g32p_row18_cosetGeneratorBlock_0011 s
  · exact g32p_row18_cosetGeneratorBlock_0012 s
  · exact g32p_row18_cosetGeneratorBlock_0013 s
  · exact g32p_row18_cosetGeneratorBlock_0014 s
  · exact g32p_row18_cosetGeneratorBlock_0015 s
  · exact g32p_row18_cosetGeneratorBlock_0016 s
  · exact g32p_row18_cosetGeneratorBlock_0017 s
  · exact g32p_row18_cosetGeneratorBlock_0018 s
  · exact g32p_row18_cosetGeneratorBlock_0019 s
  · exact g32p_row18_cosetGeneratorBlock_0020 s
  · exact g32p_row18_cosetGeneratorBlock_0021 s
  · exact g32p_row18_cosetGeneratorBlock_0022 s
  · exact g32p_row18_cosetGeneratorBlock_0023 s
  · exact g32p_row18_cosetGeneratorBlock_0024 s
  · exact g32p_row18_cosetGeneratorBlock_0025 s
  · exact g32p_row18_cosetGeneratorBlock_0026 s
  · exact g32p_row18_cosetGeneratorBlock_0027 s
  · exact g32p_row18_cosetGeneratorBlock_0028 s
  · exact g32p_row18_cosetGeneratorBlock_0029 s
  · exact g32p_row18_cosetGeneratorBlock_0030 s
  · exact g32p_row18_cosetGeneratorBlock_0031 s
  · exact g32p_row18_cosetGeneratorBlock_0032 s
  · exact g32p_row18_cosetGeneratorBlock_0033 s
  · exact g32p_row18_cosetGeneratorBlock_0034 s
  · exact g32p_row18_cosetGeneratorBlock_0035 s
  · exact g32p_row18_cosetGeneratorBlock_0036 s
  · exact g32p_row18_cosetGeneratorBlock_0037 s
  · exact g32p_row18_cosetGeneratorBlock_0038 s
  · exact g32p_row18_cosetGeneratorBlock_0039 s
  · exact g32p_row18_cosetGeneratorBlock_0040 s
  · exact g32p_row18_cosetGeneratorBlock_0041 s
  · exact g32p_row18_cosetGeneratorBlock_0042 s
  · exact g32p_row18_cosetGeneratorBlock_0043 s
  · exact g32p_row18_cosetGeneratorBlock_0044 s
  · exact g32p_row18_cosetGeneratorBlock_0045 s
  · exact g32p_row18_cosetGeneratorBlock_0046 s
  · exact g32p_row18_cosetGeneratorBlock_0047 s
  · exact g32p_row18_cosetGeneratorBlock_0048 s
  · exact g32p_row18_cosetGeneratorBlock_0049 s
  · exact g32p_row18_cosetGeneratorBlock_0050 s
  · exact g32p_row18_cosetGeneratorBlock_0051 s
  · exact g32p_row18_cosetGeneratorBlock_0052 s
  · exact g32p_row18_cosetGeneratorBlock_0053 s
  · exact g32p_row18_cosetGeneratorBlock_0054 s
  · exact g32p_row18_cosetGeneratorBlock_0055 s
  · exact g32p_row18_cosetGeneratorBlock_0056 s
  · exact g32p_row18_cosetGeneratorBlock_0057 s
  · exact g32p_row18_cosetGeneratorBlock_0058 s
  · exact g32p_row18_cosetGeneratorBlock_0059 s
  · exact g32p_row18_cosetGeneratorBlock_0060 s
  · exact g32p_row18_cosetGeneratorBlock_0061 s
  · exact g32p_row18_cosetGeneratorBlock_0062 s
  · exact g32p_row18_cosetGeneratorBlock_0063 s
  · exact g32p_row18_cosetGeneratorBlock_0064 s
  · exact g32p_row18_cosetGeneratorBlock_0065 s
  · exact g32p_row18_cosetGeneratorBlock_0066 s
  · exact g32p_row18_cosetGeneratorBlock_0067 s
  · exact g32p_row18_cosetGeneratorBlock_0068 s
  · exact g32p_row18_cosetGeneratorBlock_0069 s
  · exact g32p_row18_cosetGeneratorBlock_0070 s
  · exact g32p_row18_cosetGeneratorBlock_0071 s
  · exact g32p_row18_cosetGeneratorBlock_0072 s
  · exact g32p_row18_cosetGeneratorBlock_0073 s
  · exact g32p_row18_cosetGeneratorBlock_0074 s
  · exact g32p_row18_cosetGeneratorBlock_0075 s
  · exact g32p_row18_cosetGeneratorBlock_0076 s
  · exact g32p_row18_cosetGeneratorBlock_0077 s
  · exact g32p_row18_cosetGeneratorBlock_0078 s
  · exact g32p_row18_cosetGeneratorBlock_0079 s
  · exact g32p_row18_cosetGeneratorBlock_0080 s
  · exact g32p_row18_cosetGeneratorBlock_0081 s
  · exact g32p_row18_cosetGeneratorBlock_0082 s
  · exact g32p_row18_cosetGeneratorBlock_0083 s
  · exact g32p_row18_cosetGeneratorBlock_0084 s
  · exact g32p_row18_cosetGeneratorBlock_0085 s
  · exact g32p_row18_cosetGeneratorBlock_0086 s
  · exact g32p_row18_cosetGeneratorBlock_0087 s
  · exact g32p_row18_cosetGeneratorBlock_0088 s
  · exact g32p_row18_cosetGeneratorBlock_0089 s
  · exact g32p_row18_cosetGeneratorBlock_0090 s
  · exact g32p_row18_cosetGeneratorBlock_0091 s
  · exact g32p_row18_cosetGeneratorBlock_0092 s
  · exact g32p_row18_cosetGeneratorBlock_0093 s
  · exact g32p_row18_cosetGeneratorBlock_0094 s
  · exact g32p_row18_cosetGeneratorBlock_0095 s
  · exact g32p_row18_cosetGeneratorBlock_0096 s
  · exact g32p_row18_cosetGeneratorBlock_0097 s
  · exact g32p_row18_cosetGeneratorBlock_0098 s
  · exact g32p_row18_cosetGeneratorBlock_0099 s
  · exact g32p_row18_cosetGeneratorBlock_0100 s
  · exact g32p_row18_cosetGeneratorBlock_0101 s
  · exact g32p_row18_cosetGeneratorBlock_0102 s
  · exact g32p_row18_cosetGeneratorBlock_0103 s
  · exact g32p_row18_cosetGeneratorBlock_0104 s
  · exact g32p_row18_cosetGeneratorBlock_0105 s
  · exact g32p_row18_cosetGeneratorBlock_0106 s
  · exact g32p_row18_cosetGeneratorBlock_0107 s
  · exact g32p_row18_cosetGeneratorBlock_0108 s
  · exact g32p_row18_cosetGeneratorBlock_0109 s
  · exact g32p_row18_cosetGeneratorBlock_0110 s
  · exact g32p_row18_cosetGeneratorBlock_0111 s
  · exact g32p_row18_cosetGeneratorBlock_0112 s
  · exact g32p_row18_cosetGeneratorBlock_0113 s
  · exact g32p_row18_cosetGeneratorBlock_0114 s
  · exact g32p_row18_cosetGeneratorBlock_0115 s
  · exact g32p_row18_cosetGeneratorBlock_0116 s
  · exact g32p_row18_cosetGeneratorBlock_0117 s
  · exact g32p_row18_cosetGeneratorBlock_0118 s
  · exact g32p_row18_cosetGeneratorBlock_0119 s
  · exact g32p_row18_cosetGeneratorBlock_0120 s
  · exact g32p_row18_cosetGeneratorBlock_0121 s
  · exact g32p_row18_cosetGeneratorBlock_0122 s
  · exact g32p_row18_cosetGeneratorBlock_0123 s
  · exact g32p_row18_cosetGeneratorBlock_0124 s
  · exact g32p_row18_cosetGeneratorBlock_0125 s
  · exact g32p_row18_cosetGeneratorBlock_0126 s
  · exact g32p_row18_cosetGeneratorBlock_0127 s
  · exact g32p_row18_cosetGeneratorBlock_0128 s
  · exact g32p_row18_cosetGeneratorBlock_0129 s
  · exact g32p_row18_cosetGeneratorBlock_0130 s
  · exact g32p_row18_cosetGeneratorBlock_0131 s
  · exact g32p_row18_cosetGeneratorBlock_0132 s
  · exact g32p_row18_cosetGeneratorBlock_0133 s
  · exact g32p_row18_cosetGeneratorBlock_0134 s
  · exact g32p_row18_cosetGeneratorBlock_0135 s
  · exact g32p_row18_cosetGeneratorBlock_0136 s
  · exact g32p_row18_cosetGeneratorBlock_0137 s
  · exact g32p_row18_cosetGeneratorBlock_0138 s
  · exact g32p_row18_cosetGeneratorBlock_0139 s
  · exact g32p_row18_cosetGeneratorBlock_0140 s
  · exact g32p_row18_cosetGeneratorBlock_0141 s
  · exact g32p_row18_cosetGeneratorBlock_0142 s
  · exact g32p_row18_cosetGeneratorBlock_0143 s
  · exact g32p_row18_cosetGeneratorBlock_0144 s
  · exact g32p_row18_cosetGeneratorBlock_0145 s
  · exact g32p_row18_cosetGeneratorBlock_0146 s
  · exact g32p_row18_cosetGeneratorBlock_0147 s
  · exact g32p_row18_cosetGeneratorBlock_0148 s
  · exact g32p_row18_cosetGeneratorBlock_0149 s
  · exact g32p_row18_cosetGeneratorBlock_0150 s
  · exact g32p_row18_cosetGeneratorBlock_0151 s
  · exact g32p_row18_cosetGeneratorBlock_0152 s
  · exact g32p_row18_cosetGeneratorBlock_0153 s
  · exact g32p_row18_cosetGeneratorBlock_0154 s
  · exact g32p_row18_cosetGeneratorBlock_0155 s
  · exact g32p_row18_cosetGeneratorBlock_0156 s
  · exact g32p_row18_cosetGeneratorBlock_0157 s
  · exact g32p_row18_cosetGeneratorBlock_0158 s
  · exact g32p_row18_cosetGeneratorBlock_0159 s
  · exact g32p_row18_cosetGeneratorBlock_0160 s
  · exact g32p_row18_cosetGeneratorBlock_0161 s
  · exact g32p_row18_cosetGeneratorBlock_0162 s
  · exact g32p_row18_cosetGeneratorBlock_0163 s
  · exact g32p_row18_cosetGeneratorBlock_0164 s
  · exact g32p_row18_cosetGeneratorBlock_0165 s
  · exact g32p_row18_cosetGeneratorBlock_0166 s
  · exact g32p_row18_cosetGeneratorBlock_0167 s
  · exact g32p_row18_cosetGeneratorBlock_0168 s
  · exact g32p_row18_cosetGeneratorBlock_0169 s
  · exact g32p_row18_cosetGeneratorBlock_0170 s
  · exact g32p_row18_cosetGeneratorBlock_0171 s
  · exact g32p_row18_cosetGeneratorBlock_0172 s
  · exact g32p_row18_cosetGeneratorBlock_0173 s
  · exact g32p_row18_cosetGeneratorBlock_0174 s
  · exact g32p_row18_cosetGeneratorBlock_0175 s
  · exact g32p_row18_cosetGeneratorBlock_0176 s
  · exact g32p_row18_cosetGeneratorBlock_0177 s
  · exact g32p_row18_cosetGeneratorBlock_0178 s
  · exact g32p_row18_cosetGeneratorBlock_0179 s
  · exact g32p_row18_cosetGeneratorBlock_0180 s
  · exact g32p_row18_cosetGeneratorBlock_0181 s
  · exact g32p_row18_cosetGeneratorBlock_0182 s
  · exact g32p_row18_cosetGeneratorBlock_0183 s
  · exact g32p_row18_cosetGeneratorBlock_0184 s
  · exact g32p_row18_cosetGeneratorBlock_0185 s
  · exact g32p_row18_cosetGeneratorBlock_0186 s
  · exact g32p_row18_cosetGeneratorBlock_0187 s
  · exact g32p_row18_cosetGeneratorBlock_0188 s
  · exact g32p_row18_cosetGeneratorBlock_0189 s
  · exact g32p_row18_cosetGeneratorBlock_0190 s
  · exact g32p_row18_cosetGeneratorBlock_0191 s
  · exact g32p_row18_cosetGeneratorBlock_0192 s
  · exact g32p_row18_cosetGeneratorBlock_0193 s
  · exact g32p_row18_cosetGeneratorBlock_0194 s
  · exact g32p_row18_cosetGeneratorBlock_0195 s
  · exact g32p_row18_cosetGeneratorBlock_0196 s
  · exact g32p_row18_cosetGeneratorBlock_0197 s
  · exact g32p_row18_cosetGeneratorBlock_0198 s
  · exact g32p_row18_cosetGeneratorBlock_0199 s
  · exact g32p_row18_cosetGeneratorBlock_0200 s
  · exact g32p_row18_cosetGeneratorBlock_0201 s
  · exact g32p_row18_cosetGeneratorBlock_0202 s
  · exact g32p_row18_cosetGeneratorBlock_0203 s
  · exact g32p_row18_cosetGeneratorBlock_0204 s
  · exact g32p_row18_cosetGeneratorBlock_0205 s
  · exact g32p_row18_cosetGeneratorBlock_0206 s
  · exact g32p_row18_cosetGeneratorBlock_0207 s
  · exact g32p_row18_cosetGeneratorBlock_0208 s
  · exact g32p_row18_cosetGeneratorBlock_0209 s
  · exact g32p_row18_cosetGeneratorBlock_0210 s
  · exact g32p_row18_cosetGeneratorBlock_0211 s
  · exact g32p_row18_cosetGeneratorBlock_0212 s
  · exact g32p_row18_cosetGeneratorBlock_0213 s
  · exact g32p_row18_cosetGeneratorBlock_0214 s
  · exact g32p_row18_cosetGeneratorBlock_0215 s
  · exact g32p_row18_cosetGeneratorBlock_0216 s
  · exact g32p_row18_cosetGeneratorBlock_0217 s
  · exact g32p_row18_cosetGeneratorBlock_0218 s
  · exact g32p_row18_cosetGeneratorBlock_0219 s
  · exact g32p_row18_cosetGeneratorBlock_0220 s
  · exact g32p_row18_cosetGeneratorBlock_0221 s
  · exact g32p_row18_cosetGeneratorBlock_0222 s
  · exact g32p_row18_cosetGeneratorBlock_0223 s
  · exact g32p_row18_cosetGeneratorBlock_0224 s
  · exact g32p_row18_cosetGeneratorBlock_0225 s
  · exact g32p_row18_cosetGeneratorBlock_0226 s
  · exact g32p_row18_cosetGeneratorBlock_0227 s
  · exact g32p_row18_cosetGeneratorBlock_0228 s
  · exact g32p_row18_cosetGeneratorBlock_0229 s
  · exact g32p_row18_cosetGeneratorBlock_0230 s
  · exact g32p_row18_cosetGeneratorBlock_0231 s
  · exact g32p_row18_cosetGeneratorBlock_0232 s
  · exact g32p_row18_cosetGeneratorBlock_0233 s
  · exact g32p_row18_cosetGeneratorBlock_0234 s
  · exact g32p_row18_cosetGeneratorBlock_0235 s
  · exact g32p_row18_cosetGeneratorBlock_0236 s
  · exact g32p_row18_cosetGeneratorBlock_0237 s
  · exact g32p_row18_cosetGeneratorBlock_0238 s
  · exact g32p_row18_cosetGeneratorBlock_0239 s
  · exact g32p_row18_cosetGeneratorBlock_0240 s
  · exact g32p_row18_cosetGeneratorBlock_0241 s
  · exact g32p_row18_cosetGeneratorBlock_0242 s
  · exact g32p_row18_cosetGeneratorBlock_0243 s
  · exact g32p_row18_cosetGeneratorBlock_0244 s
  · exact g32p_row18_cosetGeneratorBlock_0245 s
  · exact g32p_row18_cosetGeneratorBlock_0246 s
  · exact g32p_row18_cosetGeneratorBlock_0247 s
  · exact g32p_row18_cosetGeneratorBlock_0248 s
  · exact g32p_row18_cosetGeneratorBlock_0249 s
  · exact g32p_row18_cosetGeneratorBlock_0250 s
  · exact g32p_row18_cosetGeneratorBlock_0251 s
  · exact g32p_row18_cosetGeneratorBlock_0252 s
  · exact g32p_row18_cosetGeneratorBlock_0253 s
  · exact g32p_row18_cosetGeneratorBlock_0254 s
  · exact g32p_row18_cosetGeneratorBlock_0255 s
  · exact g32p_row18_cosetGeneratorBlock_0256 s
  · exact g32p_row18_cosetGeneratorBlock_0257 s
  · exact g32p_row18_cosetGeneratorBlock_0258 s
  · exact g32p_row18_cosetGeneratorBlock_0259 s
  · exact g32p_row18_cosetGeneratorBlock_0260 s
  · exact g32p_row18_cosetGeneratorBlock_0261 s
  · exact g32p_row18_cosetGeneratorBlock_0262 s
  · exact g32p_row18_cosetGeneratorBlock_0263 s
  · exact g32p_row18_cosetGeneratorBlock_0264 s
  · exact g32p_row18_cosetGeneratorBlock_0265 s
  · exact g32p_row18_cosetGeneratorBlock_0266 s
  · exact g32p_row18_cosetGeneratorBlock_0267 s
  · exact g32p_row18_cosetGeneratorBlock_0268 s
  · exact g32p_row18_cosetGeneratorBlock_0269 s


theorem g32p_row18_cosetActualStep (s : Fin 4) (i : Fin 4320) :
    g32p_word (g32p_archiveWords s) * g32p_row18_cosetActualRepresentatives i =
      g32p_row18_cosetActualRepresentatives (g32p_row18_cosetGeneratorNext s i) *
        (g32p_row18_groupEquiv (g32p_row18_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row18_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row18_cosetActualRepresentatives (g32p_row18_cosetGeneratorNext s i) *
      (g32p_row18_groupEquiv (g32p_row18_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row18_cosetActualRepresentatives_map,
    g32p_row18_cosetActualRepresentatives_map, g32p_row18_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row18_cosetGeneratorStep]

theorem g32p_row18_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row18_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row18_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row18_cosetGeneratorNext
      (fun s i => g32p_row18_groupEquiv (g32p_row18_cosetGeneratorFactor s i))
    exact g32p_row18_cosetActualStep
  · rw [g32p_row18_finiteSupplier_order]
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

theorem g32p_row18_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 0)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 0)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 0) = g32p_row18_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 1)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 1)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 1) = g32p_row18_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 2)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 2)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 2) = g32p_row18_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 3)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 3)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 3) = g32p_row18_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 4)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 4)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 4) = g32p_row18_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 5)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 5)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 5) = g32p_row18_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 6)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 6)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 6) = g32p_row18_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 7)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 7)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 7) = g32p_row18_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 8)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 8)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 8) = g32p_row18_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 9)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 9)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 9) = g32p_row18_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 10)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 10)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 10) = g32p_row18_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 11)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 11)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 11) = g32p_row18_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 12)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 12)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 12) = g32p_row18_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 13)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 13)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 13) = g32p_row18_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 14)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 14)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 14) = g32p_row18_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row18_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row18_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives 15)
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 15)) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 15) = g32p_row18_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row18_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row18_cosetBranchMatrices 0) (g32p_row18_cosetLengths0 (g32p_finBlockIndex 1440 0 r)))
      (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots0 (g32p_finBlockIndex 1440 0 r))) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetRoots0 (g32p_finBlockIndex 1440 0 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetMonodromies0 (g32p_finBlockIndex 1440 0 r))) ∧
    g32p_row18_characterValues (g32p_row18_cosetMonodromies0 (g32p_finBlockIndex 1440 0 r)) = g32p_row18_cosetExponents0 (g32p_finBlockIndex 1440 0 r) := by
  fin_cases r
  · exact g32p_row18_cosetMonodromy_0_0000
  · exact g32p_row18_cosetMonodromy_0_0001
  · exact g32p_row18_cosetMonodromy_0_0002
  · exact g32p_row18_cosetMonodromy_0_0003
  · exact g32p_row18_cosetMonodromy_0_0004
  · exact g32p_row18_cosetMonodromy_0_0005
  · exact g32p_row18_cosetMonodromy_0_0006
  · exact g32p_row18_cosetMonodromy_0_0007
  · exact g32p_row18_cosetMonodromy_0_0008
  · exact g32p_row18_cosetMonodromy_0_0009
  · exact g32p_row18_cosetMonodromy_0_0010
  · exact g32p_row18_cosetMonodromy_0_0011
  · exact g32p_row18_cosetMonodromy_0_0012
  · exact g32p_row18_cosetMonodromy_0_0013
  · exact g32p_row18_cosetMonodromy_0_0014
  · exact g32p_row18_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end
