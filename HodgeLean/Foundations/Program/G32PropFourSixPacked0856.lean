import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0835

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5120 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5120) = g32p_row31_cosetRepresentatives 5120 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5120 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5120) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5120))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5120)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5120 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5120) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5120))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5120)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5121 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5121) = g32p_row31_cosetRepresentatives 5121 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5121 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5121) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5121))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5121)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5121 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5121) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5121))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5121)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5122 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5122) = g32p_row31_cosetRepresentatives 5122 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5122 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5122) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5122))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5122)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5122 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5122) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5122))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5122)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5123 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5123) = g32p_row31_cosetRepresentatives 5123 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5123 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5123) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5123))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5123)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5123 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5123) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5123))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5123)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5124 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5124) = g32p_row31_cosetRepresentatives 5124 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5124 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5124) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5124))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5124)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5124 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5124) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5124))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5124)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5125 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5125) = g32p_row31_cosetRepresentatives 5125 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5125 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5125) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5125))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5125)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5125 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5125) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5125))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5125)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5126 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5126) = g32p_row31_cosetRepresentatives 5126 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5126 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5126) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5126))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5126)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5126 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5126) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5126))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5126)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5127 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5127) = g32p_row31_cosetRepresentatives 5127 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5127 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5127) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5127))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5127)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5127 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5127) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5127))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5127)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5128 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5128) = g32p_row31_cosetRepresentatives 5128 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5128 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5128) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5128))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5128)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5128 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5128) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5128))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5128)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5129 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5129) = g32p_row31_cosetRepresentatives 5129 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5129 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5129) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5129))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5129)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5129 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5129) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5129))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5129)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5130 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5130) = g32p_row31_cosetRepresentatives 5130 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5130 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5130) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5130))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5130)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5130 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5130) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5130))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5130)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5131 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5131) = g32p_row31_cosetRepresentatives 5131 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5131 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5131) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5131))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5131)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5131 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5131) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5131))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5131)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5132 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5132) = g32p_row31_cosetRepresentatives 5132 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5132 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5132) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5132))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5132)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5132 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5132) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5132))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5132)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5133 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5133) = g32p_row31_cosetRepresentatives 5133 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5133 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5133) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5133))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5133)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5133 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5133) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5133))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5133)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5134 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5134) = g32p_row31_cosetRepresentatives 5134 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5134 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5134) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5134))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5134)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5134 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5134) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5134))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5134)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5135 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5135) = g32p_row31_cosetRepresentatives 5135 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5135 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5135) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5135))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5135)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5135 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5135) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5135))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5135)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0320 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 320 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 320 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5120
  · exact g32p_row31_cosetWord_5121
  · exact g32p_row31_cosetWord_5122
  · exact g32p_row31_cosetWord_5123
  · exact g32p_row31_cosetWord_5124
  · exact g32p_row31_cosetWord_5125
  · exact g32p_row31_cosetWord_5126
  · exact g32p_row31_cosetWord_5127
  · exact g32p_row31_cosetWord_5128
  · exact g32p_row31_cosetWord_5129
  · exact g32p_row31_cosetWord_5130
  · exact g32p_row31_cosetWord_5131
  · exact g32p_row31_cosetWord_5132
  · exact g32p_row31_cosetWord_5133
  · exact g32p_row31_cosetWord_5134
  · exact g32p_row31_cosetWord_5135

theorem g32p_row31_cosetGeneratorBlock_0320 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 320 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 320 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 320 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5120 s
  · exact g32p_row31_cosetGeneratorStep_5121 s
  · exact g32p_row31_cosetGeneratorStep_5122 s
  · exact g32p_row31_cosetGeneratorStep_5123 s
  · exact g32p_row31_cosetGeneratorStep_5124 s
  · exact g32p_row31_cosetGeneratorStep_5125 s
  · exact g32p_row31_cosetGeneratorStep_5126 s
  · exact g32p_row31_cosetGeneratorStep_5127 s
  · exact g32p_row31_cosetGeneratorStep_5128 s
  · exact g32p_row31_cosetGeneratorStep_5129 s
  · exact g32p_row31_cosetGeneratorStep_5130 s
  · exact g32p_row31_cosetGeneratorStep_5131 s
  · exact g32p_row31_cosetGeneratorStep_5132 s
  · exact g32p_row31_cosetGeneratorStep_5133 s
  · exact g32p_row31_cosetGeneratorStep_5134 s
  · exact g32p_row31_cosetGeneratorStep_5135 s

theorem g32p_row31_cosetBranchBlock_0320 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 320 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 320 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 320 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5120 s
  · exact g32p_row31_cosetBranchStep_5121 s
  · exact g32p_row31_cosetBranchStep_5122 s
  · exact g32p_row31_cosetBranchStep_5123 s
  · exact g32p_row31_cosetBranchStep_5124 s
  · exact g32p_row31_cosetBranchStep_5125 s
  · exact g32p_row31_cosetBranchStep_5126 s
  · exact g32p_row31_cosetBranchStep_5127 s
  · exact g32p_row31_cosetBranchStep_5128 s
  · exact g32p_row31_cosetBranchStep_5129 s
  · exact g32p_row31_cosetBranchStep_5130 s
  · exact g32p_row31_cosetBranchStep_5131 s
  · exact g32p_row31_cosetBranchStep_5132 s
  · exact g32p_row31_cosetBranchStep_5133 s
  · exact g32p_row31_cosetBranchStep_5134 s
  · exact g32p_row31_cosetBranchStep_5135 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5136 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5136) = g32p_row31_cosetRepresentatives 5136 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5136 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5136) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5136))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5136)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5136 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5136) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5136))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5136)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5137 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5137) = g32p_row31_cosetRepresentatives 5137 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5137 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5137) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5137))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5137)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5137 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5137) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5137))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5137)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5138 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5138) = g32p_row31_cosetRepresentatives 5138 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5138 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5138) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5138))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5138)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5138 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5138) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5138))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5138)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5139 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5139) = g32p_row31_cosetRepresentatives 5139 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5139 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5139) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5139))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5139)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5139 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5139) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5139))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5139)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5140 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5140) = g32p_row31_cosetRepresentatives 5140 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5140 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5140) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5140))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5140)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5140 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5140) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5140))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5140)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5141 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5141) = g32p_row31_cosetRepresentatives 5141 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5141 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5141) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5141))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5141)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5141 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5141) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5141))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5141)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5142 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5142) = g32p_row31_cosetRepresentatives 5142 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5142 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5142) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5142))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5142)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5142 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5142) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5142))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5142)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5143 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5143) = g32p_row31_cosetRepresentatives 5143 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5143 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5143) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5143))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5143)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5143 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5143) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5143))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5143)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5144 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5144) = g32p_row31_cosetRepresentatives 5144 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5144 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5144) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5144))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5144)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5144 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5144) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5144))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5144)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5145 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5145) = g32p_row31_cosetRepresentatives 5145 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5145 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5145) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5145))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5145)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5145 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5145) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5145))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5145)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5146 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5146) = g32p_row31_cosetRepresentatives 5146 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5146 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5146) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5146))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5146)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5146 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5146) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5146))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5146)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5147 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5147) = g32p_row31_cosetRepresentatives 5147 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5147 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5147) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5147))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5147)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5147 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5147) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5147))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5147)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5148 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5148) = g32p_row31_cosetRepresentatives 5148 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5148 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5148) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5148))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5148)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5148 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5148) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5148))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5148)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5149 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5149) = g32p_row31_cosetRepresentatives 5149 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5149 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5149) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5149))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5149)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5149 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5149) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5149))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5149)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5150 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5150) = g32p_row31_cosetRepresentatives 5150 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5150 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5150) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5150))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5150)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5150 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5150) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5150))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5150)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5151 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5151) = g32p_row31_cosetRepresentatives 5151 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5151 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5151) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5151))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5151)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5151 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5151) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5151))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5151)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0321 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 321 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 321 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5136
  · exact g32p_row31_cosetWord_5137
  · exact g32p_row31_cosetWord_5138
  · exact g32p_row31_cosetWord_5139
  · exact g32p_row31_cosetWord_5140
  · exact g32p_row31_cosetWord_5141
  · exact g32p_row31_cosetWord_5142
  · exact g32p_row31_cosetWord_5143
  · exact g32p_row31_cosetWord_5144
  · exact g32p_row31_cosetWord_5145
  · exact g32p_row31_cosetWord_5146
  · exact g32p_row31_cosetWord_5147
  · exact g32p_row31_cosetWord_5148
  · exact g32p_row31_cosetWord_5149
  · exact g32p_row31_cosetWord_5150
  · exact g32p_row31_cosetWord_5151

theorem g32p_row31_cosetGeneratorBlock_0321 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 321 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 321 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 321 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5136 s
  · exact g32p_row31_cosetGeneratorStep_5137 s
  · exact g32p_row31_cosetGeneratorStep_5138 s
  · exact g32p_row31_cosetGeneratorStep_5139 s
  · exact g32p_row31_cosetGeneratorStep_5140 s
  · exact g32p_row31_cosetGeneratorStep_5141 s
  · exact g32p_row31_cosetGeneratorStep_5142 s
  · exact g32p_row31_cosetGeneratorStep_5143 s
  · exact g32p_row31_cosetGeneratorStep_5144 s
  · exact g32p_row31_cosetGeneratorStep_5145 s
  · exact g32p_row31_cosetGeneratorStep_5146 s
  · exact g32p_row31_cosetGeneratorStep_5147 s
  · exact g32p_row31_cosetGeneratorStep_5148 s
  · exact g32p_row31_cosetGeneratorStep_5149 s
  · exact g32p_row31_cosetGeneratorStep_5150 s
  · exact g32p_row31_cosetGeneratorStep_5151 s

theorem g32p_row31_cosetBranchBlock_0321 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 321 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 321 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 321 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5136 s
  · exact g32p_row31_cosetBranchStep_5137 s
  · exact g32p_row31_cosetBranchStep_5138 s
  · exact g32p_row31_cosetBranchStep_5139 s
  · exact g32p_row31_cosetBranchStep_5140 s
  · exact g32p_row31_cosetBranchStep_5141 s
  · exact g32p_row31_cosetBranchStep_5142 s
  · exact g32p_row31_cosetBranchStep_5143 s
  · exact g32p_row31_cosetBranchStep_5144 s
  · exact g32p_row31_cosetBranchStep_5145 s
  · exact g32p_row31_cosetBranchStep_5146 s
  · exact g32p_row31_cosetBranchStep_5147 s
  · exact g32p_row31_cosetBranchStep_5148 s
  · exact g32p_row31_cosetBranchStep_5149 s
  · exact g32p_row31_cosetBranchStep_5150 s
  · exact g32p_row31_cosetBranchStep_5151 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5152 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5152) = g32p_row31_cosetRepresentatives 5152 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5152 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5152) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5152))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5152)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5152 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5152) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5152))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5152)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5153 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5153) = g32p_row31_cosetRepresentatives 5153 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5153 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5153) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5153))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5153)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5153 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5153) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5153))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5153)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5154 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5154) = g32p_row31_cosetRepresentatives 5154 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5154 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5154) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5154))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5154)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5154 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5154) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5154))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5154)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5155 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5155) = g32p_row31_cosetRepresentatives 5155 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5155 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5155) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5155))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5155)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5155 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5155) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5155))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5155)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5156 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5156) = g32p_row31_cosetRepresentatives 5156 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5156 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5156) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5156))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5156)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5156 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5156) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5156))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5156)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5157 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5157) = g32p_row31_cosetRepresentatives 5157 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5157 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5157) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5157))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5157)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5157 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5157) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5157))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5157)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5158 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5158) = g32p_row31_cosetRepresentatives 5158 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5158 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5158) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5158))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5158)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5158 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5158) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5158))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5158)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5159 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5159) = g32p_row31_cosetRepresentatives 5159 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5159 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5159) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5159))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5159)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5159 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5159) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5159))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5159)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5160 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5160) = g32p_row31_cosetRepresentatives 5160 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5160 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5160) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5160))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5160)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5160 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5160) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5160))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5160)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5161 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5161) = g32p_row31_cosetRepresentatives 5161 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5161 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5161) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5161))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5161)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5161 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5161) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5161))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5161)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5162 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5162) = g32p_row31_cosetRepresentatives 5162 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5162 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5162) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5162))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5162)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5162 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5162) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5162))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5162)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5163 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5163) = g32p_row31_cosetRepresentatives 5163 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5163 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5163) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5163))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5163)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5163 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5163) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5163))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5163)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5164 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5164) = g32p_row31_cosetRepresentatives 5164 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5164 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5164) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5164))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5164)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5164 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5164) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5164))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5164)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5165 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5165) = g32p_row31_cosetRepresentatives 5165 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5165 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5165) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5165))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5165)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5165 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5165) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5165))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5165)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5166 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5166) = g32p_row31_cosetRepresentatives 5166 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5166 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5166) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5166))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5166)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5166 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5166) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5166))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5166)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5167 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5167) = g32p_row31_cosetRepresentatives 5167 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5167 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5167) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5167))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5167)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5167 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5167) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5167))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5167)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0322 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 322 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 322 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5152
  · exact g32p_row31_cosetWord_5153
  · exact g32p_row31_cosetWord_5154
  · exact g32p_row31_cosetWord_5155
  · exact g32p_row31_cosetWord_5156
  · exact g32p_row31_cosetWord_5157
  · exact g32p_row31_cosetWord_5158
  · exact g32p_row31_cosetWord_5159
  · exact g32p_row31_cosetWord_5160
  · exact g32p_row31_cosetWord_5161
  · exact g32p_row31_cosetWord_5162
  · exact g32p_row31_cosetWord_5163
  · exact g32p_row31_cosetWord_5164
  · exact g32p_row31_cosetWord_5165
  · exact g32p_row31_cosetWord_5166
  · exact g32p_row31_cosetWord_5167

theorem g32p_row31_cosetGeneratorBlock_0322 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 322 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 322 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 322 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5152 s
  · exact g32p_row31_cosetGeneratorStep_5153 s
  · exact g32p_row31_cosetGeneratorStep_5154 s
  · exact g32p_row31_cosetGeneratorStep_5155 s
  · exact g32p_row31_cosetGeneratorStep_5156 s
  · exact g32p_row31_cosetGeneratorStep_5157 s
  · exact g32p_row31_cosetGeneratorStep_5158 s
  · exact g32p_row31_cosetGeneratorStep_5159 s
  · exact g32p_row31_cosetGeneratorStep_5160 s
  · exact g32p_row31_cosetGeneratorStep_5161 s
  · exact g32p_row31_cosetGeneratorStep_5162 s
  · exact g32p_row31_cosetGeneratorStep_5163 s
  · exact g32p_row31_cosetGeneratorStep_5164 s
  · exact g32p_row31_cosetGeneratorStep_5165 s
  · exact g32p_row31_cosetGeneratorStep_5166 s
  · exact g32p_row31_cosetGeneratorStep_5167 s

theorem g32p_row31_cosetBranchBlock_0322 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 322 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 322 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 322 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5152 s
  · exact g32p_row31_cosetBranchStep_5153 s
  · exact g32p_row31_cosetBranchStep_5154 s
  · exact g32p_row31_cosetBranchStep_5155 s
  · exact g32p_row31_cosetBranchStep_5156 s
  · exact g32p_row31_cosetBranchStep_5157 s
  · exact g32p_row31_cosetBranchStep_5158 s
  · exact g32p_row31_cosetBranchStep_5159 s
  · exact g32p_row31_cosetBranchStep_5160 s
  · exact g32p_row31_cosetBranchStep_5161 s
  · exact g32p_row31_cosetBranchStep_5162 s
  · exact g32p_row31_cosetBranchStep_5163 s
  · exact g32p_row31_cosetBranchStep_5164 s
  · exact g32p_row31_cosetBranchStep_5165 s
  · exact g32p_row31_cosetBranchStep_5166 s
  · exact g32p_row31_cosetBranchStep_5167 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5168 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5168) = g32p_row31_cosetRepresentatives 5168 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5168 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5168) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5168))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5168)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5168 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5168) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5168))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5168)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5169 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5169) = g32p_row31_cosetRepresentatives 5169 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5169 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5169) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5169))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5169)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5169 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5169) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5169))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5169)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5170 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5170) = g32p_row31_cosetRepresentatives 5170 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5170 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5170) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5170))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5170)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5170 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5170) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5170))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5170)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5171 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5171) = g32p_row31_cosetRepresentatives 5171 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5171 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5171) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5171))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5171)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5171 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5171) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5171))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5171)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5172 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5172) = g32p_row31_cosetRepresentatives 5172 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5172 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5172) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5172))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5172)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5172 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5172) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5172))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5172)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5173 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5173) = g32p_row31_cosetRepresentatives 5173 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5173 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5173) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5173))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5173)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5173 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5173) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5173))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5173)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5174 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5174) = g32p_row31_cosetRepresentatives 5174 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5174 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5174) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5174))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5174)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5174 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5174) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5174))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5174)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5175 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5175) = g32p_row31_cosetRepresentatives 5175 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5175 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5175) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5175))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5175)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5175 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5175) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5175))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5175)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5176 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5176) = g32p_row31_cosetRepresentatives 5176 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5176 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5176) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5176))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5176)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5176 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5176) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5176))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5176)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5177 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5177) = g32p_row31_cosetRepresentatives 5177 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5177 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5177) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5177))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5177)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5177 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5177) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5177))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5177)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5178 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5178) = g32p_row31_cosetRepresentatives 5178 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5178 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5178) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5178))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5178)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5178 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5178) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5178))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5178)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5179 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5179) = g32p_row31_cosetRepresentatives 5179 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5179 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5179) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5179))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5179)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5179 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5179) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5179))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5179)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5180 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5180) = g32p_row31_cosetRepresentatives 5180 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5180 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5180) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5180))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5180)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5180 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5180) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5180))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5180)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5181 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5181) = g32p_row31_cosetRepresentatives 5181 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5181 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5181) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5181))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5181)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5181 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5181) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5181))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5181)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5182 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5182) = g32p_row31_cosetRepresentatives 5182 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5182 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5182) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5182))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5182)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5182 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5182) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5182))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5182)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5183 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5183) = g32p_row31_cosetRepresentatives 5183 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5183 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5183) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5183))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5183)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5183 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5183) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5183))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5183)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0323 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 323 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 323 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5168
  · exact g32p_row31_cosetWord_5169
  · exact g32p_row31_cosetWord_5170
  · exact g32p_row31_cosetWord_5171
  · exact g32p_row31_cosetWord_5172
  · exact g32p_row31_cosetWord_5173
  · exact g32p_row31_cosetWord_5174
  · exact g32p_row31_cosetWord_5175
  · exact g32p_row31_cosetWord_5176
  · exact g32p_row31_cosetWord_5177
  · exact g32p_row31_cosetWord_5178
  · exact g32p_row31_cosetWord_5179
  · exact g32p_row31_cosetWord_5180
  · exact g32p_row31_cosetWord_5181
  · exact g32p_row31_cosetWord_5182
  · exact g32p_row31_cosetWord_5183

theorem g32p_row31_cosetGeneratorBlock_0323 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 323 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 323 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 323 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5168 s
  · exact g32p_row31_cosetGeneratorStep_5169 s
  · exact g32p_row31_cosetGeneratorStep_5170 s
  · exact g32p_row31_cosetGeneratorStep_5171 s
  · exact g32p_row31_cosetGeneratorStep_5172 s
  · exact g32p_row31_cosetGeneratorStep_5173 s
  · exact g32p_row31_cosetGeneratorStep_5174 s
  · exact g32p_row31_cosetGeneratorStep_5175 s
  · exact g32p_row31_cosetGeneratorStep_5176 s
  · exact g32p_row31_cosetGeneratorStep_5177 s
  · exact g32p_row31_cosetGeneratorStep_5178 s
  · exact g32p_row31_cosetGeneratorStep_5179 s
  · exact g32p_row31_cosetGeneratorStep_5180 s
  · exact g32p_row31_cosetGeneratorStep_5181 s
  · exact g32p_row31_cosetGeneratorStep_5182 s
  · exact g32p_row31_cosetGeneratorStep_5183 s

theorem g32p_row31_cosetBranchBlock_0323 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 323 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 323 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 323 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5168 s
  · exact g32p_row31_cosetBranchStep_5169 s
  · exact g32p_row31_cosetBranchStep_5170 s
  · exact g32p_row31_cosetBranchStep_5171 s
  · exact g32p_row31_cosetBranchStep_5172 s
  · exact g32p_row31_cosetBranchStep_5173 s
  · exact g32p_row31_cosetBranchStep_5174 s
  · exact g32p_row31_cosetBranchStep_5175 s
  · exact g32p_row31_cosetBranchStep_5176 s
  · exact g32p_row31_cosetBranchStep_5177 s
  · exact g32p_row31_cosetBranchStep_5178 s
  · exact g32p_row31_cosetBranchStep_5179 s
  · exact g32p_row31_cosetBranchStep_5180 s
  · exact g32p_row31_cosetBranchStep_5181 s
  · exact g32p_row31_cosetBranchStep_5182 s
  · exact g32p_row31_cosetBranchStep_5183 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5184 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5184) = g32p_row31_cosetRepresentatives 5184 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5184 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5184) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5184))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5184)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5184 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5184) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5184))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5184)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5185 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5185) = g32p_row31_cosetRepresentatives 5185 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5185 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5185) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5185))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5185)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5185 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5185) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5185))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5185)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5186 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5186) = g32p_row31_cosetRepresentatives 5186 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5186 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5186) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5186))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5186)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5186 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5186) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5186))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5186)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5187 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5187) = g32p_row31_cosetRepresentatives 5187 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5187 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5187) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5187))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5187)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5187 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5187) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5187))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5187)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5188 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5188) = g32p_row31_cosetRepresentatives 5188 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5188 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5188) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5188))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5188)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5188 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5188) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5188))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5188)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5189 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5189) = g32p_row31_cosetRepresentatives 5189 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5189 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5189) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5189))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5189)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5189 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5189) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5189))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5189)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5190 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5190) = g32p_row31_cosetRepresentatives 5190 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5190 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5190) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5190))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5190)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5190 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5190) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5190))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5190)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5191 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5191) = g32p_row31_cosetRepresentatives 5191 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5191 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5191) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5191))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5191)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5191 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5191) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5191))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5191)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5192 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5192) = g32p_row31_cosetRepresentatives 5192 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5192 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5192) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5192))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5192)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5192 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5192) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5192))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5192)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5193 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5193) = g32p_row31_cosetRepresentatives 5193 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5193 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5193) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5193))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5193)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5193 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5193) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5193))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5193)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5194 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5194) = g32p_row31_cosetRepresentatives 5194 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5194 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5194) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5194))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5194)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5194 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5194) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5194))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5194)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5195 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5195) = g32p_row31_cosetRepresentatives 5195 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5195 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5195) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5195))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5195)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5195 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5195) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5195))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5195)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5196 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5196) = g32p_row31_cosetRepresentatives 5196 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5196 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5196) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5196))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5196)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5196 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5196) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5196))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5196)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5197 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5197) = g32p_row31_cosetRepresentatives 5197 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5197 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5197) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5197))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5197)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5197 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5197) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5197))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5197)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5198 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5198) = g32p_row31_cosetRepresentatives 5198 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5198 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5198) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5198))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5198)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5198 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5198) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5198))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5198)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5199 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5199) = g32p_row31_cosetRepresentatives 5199 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5199 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5199) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5199))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5199)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5199 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5199) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5199))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5199)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0324 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 324 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 324 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5184
  · exact g32p_row31_cosetWord_5185
  · exact g32p_row31_cosetWord_5186
  · exact g32p_row31_cosetWord_5187
  · exact g32p_row31_cosetWord_5188
  · exact g32p_row31_cosetWord_5189
  · exact g32p_row31_cosetWord_5190
  · exact g32p_row31_cosetWord_5191
  · exact g32p_row31_cosetWord_5192
  · exact g32p_row31_cosetWord_5193
  · exact g32p_row31_cosetWord_5194
  · exact g32p_row31_cosetWord_5195
  · exact g32p_row31_cosetWord_5196
  · exact g32p_row31_cosetWord_5197
  · exact g32p_row31_cosetWord_5198
  · exact g32p_row31_cosetWord_5199

theorem g32p_row31_cosetGeneratorBlock_0324 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 324 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 324 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 324 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5184 s
  · exact g32p_row31_cosetGeneratorStep_5185 s
  · exact g32p_row31_cosetGeneratorStep_5186 s
  · exact g32p_row31_cosetGeneratorStep_5187 s
  · exact g32p_row31_cosetGeneratorStep_5188 s
  · exact g32p_row31_cosetGeneratorStep_5189 s
  · exact g32p_row31_cosetGeneratorStep_5190 s
  · exact g32p_row31_cosetGeneratorStep_5191 s
  · exact g32p_row31_cosetGeneratorStep_5192 s
  · exact g32p_row31_cosetGeneratorStep_5193 s
  · exact g32p_row31_cosetGeneratorStep_5194 s
  · exact g32p_row31_cosetGeneratorStep_5195 s
  · exact g32p_row31_cosetGeneratorStep_5196 s
  · exact g32p_row31_cosetGeneratorStep_5197 s
  · exact g32p_row31_cosetGeneratorStep_5198 s
  · exact g32p_row31_cosetGeneratorStep_5199 s

theorem g32p_row31_cosetBranchBlock_0324 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 324 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 324 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 324 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5184 s
  · exact g32p_row31_cosetBranchStep_5185 s
  · exact g32p_row31_cosetBranchStep_5186 s
  · exact g32p_row31_cosetBranchStep_5187 s
  · exact g32p_row31_cosetBranchStep_5188 s
  · exact g32p_row31_cosetBranchStep_5189 s
  · exact g32p_row31_cosetBranchStep_5190 s
  · exact g32p_row31_cosetBranchStep_5191 s
  · exact g32p_row31_cosetBranchStep_5192 s
  · exact g32p_row31_cosetBranchStep_5193 s
  · exact g32p_row31_cosetBranchStep_5194 s
  · exact g32p_row31_cosetBranchStep_5195 s
  · exact g32p_row31_cosetBranchStep_5196 s
  · exact g32p_row31_cosetBranchStep_5197 s
  · exact g32p_row31_cosetBranchStep_5198 s
  · exact g32p_row31_cosetBranchStep_5199 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5200 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5200) = g32p_row31_cosetRepresentatives 5200 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5200 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5200) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5200))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5200)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5200 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5200) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5200))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5200)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5201 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5201) = g32p_row31_cosetRepresentatives 5201 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5201 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5201) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5201))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5201)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5201 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5201) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5201))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5201)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5202 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5202) = g32p_row31_cosetRepresentatives 5202 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5202 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5202) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5202))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5202)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5202 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5202) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5202))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5202)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5203 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5203) = g32p_row31_cosetRepresentatives 5203 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5203 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5203) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5203))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5203)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5203 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5203) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5203))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5203)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5204 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5204) = g32p_row31_cosetRepresentatives 5204 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5204 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5204) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5204))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5204)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5204 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5204) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5204))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5204)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5205 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5205) = g32p_row31_cosetRepresentatives 5205 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5205 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5205) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5205))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5205)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5205 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5205) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5205))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5205)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5206 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5206) = g32p_row31_cosetRepresentatives 5206 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5206 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5206) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5206))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5206)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5206 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5206) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5206))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5206)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5207 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5207) = g32p_row31_cosetRepresentatives 5207 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5207 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5207) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5207))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5207)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5207 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5207) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5207))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5207)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5208 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5208) = g32p_row31_cosetRepresentatives 5208 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5208 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5208) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5208))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5208)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5208 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5208) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5208))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5208)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5209 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5209) = g32p_row31_cosetRepresentatives 5209 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5209 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5209) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5209))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5209)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5209 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5209) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5209))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5209)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5210 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5210) = g32p_row31_cosetRepresentatives 5210 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5210 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5210) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5210))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5210)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5210 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5210) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5210))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5210)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5211 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5211) = g32p_row31_cosetRepresentatives 5211 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5211 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5211) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5211))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5211)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5211 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5211) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5211))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5211)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5212 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5212) = g32p_row31_cosetRepresentatives 5212 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5212 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5212) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5212))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5212)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5212 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5212) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5212))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5212)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5213 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5213) = g32p_row31_cosetRepresentatives 5213 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5213 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5213) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5213))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5213)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5213 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5213) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5213))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5213)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5214 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5214) = g32p_row31_cosetRepresentatives 5214 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5214 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5214) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5214))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5214)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5214 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5214) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5214))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5214)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5215 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5215) = g32p_row31_cosetRepresentatives 5215 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5215 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5215) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5215))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5215)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5215 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5215) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5215))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5215)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0325 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 325 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 325 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5200
  · exact g32p_row31_cosetWord_5201
  · exact g32p_row31_cosetWord_5202
  · exact g32p_row31_cosetWord_5203
  · exact g32p_row31_cosetWord_5204
  · exact g32p_row31_cosetWord_5205
  · exact g32p_row31_cosetWord_5206
  · exact g32p_row31_cosetWord_5207
  · exact g32p_row31_cosetWord_5208
  · exact g32p_row31_cosetWord_5209
  · exact g32p_row31_cosetWord_5210
  · exact g32p_row31_cosetWord_5211
  · exact g32p_row31_cosetWord_5212
  · exact g32p_row31_cosetWord_5213
  · exact g32p_row31_cosetWord_5214
  · exact g32p_row31_cosetWord_5215

theorem g32p_row31_cosetGeneratorBlock_0325 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 325 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 325 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 325 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5200 s
  · exact g32p_row31_cosetGeneratorStep_5201 s
  · exact g32p_row31_cosetGeneratorStep_5202 s
  · exact g32p_row31_cosetGeneratorStep_5203 s
  · exact g32p_row31_cosetGeneratorStep_5204 s
  · exact g32p_row31_cosetGeneratorStep_5205 s
  · exact g32p_row31_cosetGeneratorStep_5206 s
  · exact g32p_row31_cosetGeneratorStep_5207 s
  · exact g32p_row31_cosetGeneratorStep_5208 s
  · exact g32p_row31_cosetGeneratorStep_5209 s
  · exact g32p_row31_cosetGeneratorStep_5210 s
  · exact g32p_row31_cosetGeneratorStep_5211 s
  · exact g32p_row31_cosetGeneratorStep_5212 s
  · exact g32p_row31_cosetGeneratorStep_5213 s
  · exact g32p_row31_cosetGeneratorStep_5214 s
  · exact g32p_row31_cosetGeneratorStep_5215 s

theorem g32p_row31_cosetBranchBlock_0325 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 325 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 325 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 325 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5200 s
  · exact g32p_row31_cosetBranchStep_5201 s
  · exact g32p_row31_cosetBranchStep_5202 s
  · exact g32p_row31_cosetBranchStep_5203 s
  · exact g32p_row31_cosetBranchStep_5204 s
  · exact g32p_row31_cosetBranchStep_5205 s
  · exact g32p_row31_cosetBranchStep_5206 s
  · exact g32p_row31_cosetBranchStep_5207 s
  · exact g32p_row31_cosetBranchStep_5208 s
  · exact g32p_row31_cosetBranchStep_5209 s
  · exact g32p_row31_cosetBranchStep_5210 s
  · exact g32p_row31_cosetBranchStep_5211 s
  · exact g32p_row31_cosetBranchStep_5212 s
  · exact g32p_row31_cosetBranchStep_5213 s
  · exact g32p_row31_cosetBranchStep_5214 s
  · exact g32p_row31_cosetBranchStep_5215 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5216 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5216) = g32p_row31_cosetRepresentatives 5216 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5216 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5216) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5216))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5216)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5216 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5216) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5216))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5216)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5217 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5217) = g32p_row31_cosetRepresentatives 5217 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5217 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5217) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5217))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5217)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5217 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5217) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5217))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5217)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5218 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5218) = g32p_row31_cosetRepresentatives 5218 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5218 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5218) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5218))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5218)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5218 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5218) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5218))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5218)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5219 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5219) = g32p_row31_cosetRepresentatives 5219 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5219 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5219) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5219))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5219)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5219 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5219) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5219))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5219)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5220 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5220) = g32p_row31_cosetRepresentatives 5220 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5220 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5220) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5220))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5220)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5220 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5220) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5220))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5220)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5221 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5221) = g32p_row31_cosetRepresentatives 5221 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5221 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5221) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5221))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5221)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5221 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5221) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5221))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5221)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5222 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5222) = g32p_row31_cosetRepresentatives 5222 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5222 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5222) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5222))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5222)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5222 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5222) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5222))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5222)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5223 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5223) = g32p_row31_cosetRepresentatives 5223 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5223 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5223) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5223))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5223)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5223 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5223) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5223))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5223)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5224 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5224) = g32p_row31_cosetRepresentatives 5224 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5224 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5224) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5224))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5224)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5224 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5224) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5224))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5224)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5225 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5225) = g32p_row31_cosetRepresentatives 5225 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5225 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5225) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5225))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5225)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5225 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5225) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5225))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5225)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5226 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5226) = g32p_row31_cosetRepresentatives 5226 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5226 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5226) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5226))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5226)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5226 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5226) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5226))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5226)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5227 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5227) = g32p_row31_cosetRepresentatives 5227 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5227 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5227) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5227))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5227)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5227 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5227) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5227))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5227)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5228 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5228) = g32p_row31_cosetRepresentatives 5228 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5228 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5228) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5228))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5228)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5228 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5228) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5228))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5228)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5229 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5229) = g32p_row31_cosetRepresentatives 5229 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5229 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5229) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5229))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5229)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5229 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5229) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5229))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5229)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5230 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5230) = g32p_row31_cosetRepresentatives 5230 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5230 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5230) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5230))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5230)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5230 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5230) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5230))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5230)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5231 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5231) = g32p_row31_cosetRepresentatives 5231 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5231 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5231) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5231))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5231)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5231 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5231) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5231))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5231)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0326 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 326 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 326 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5216
  · exact g32p_row31_cosetWord_5217
  · exact g32p_row31_cosetWord_5218
  · exact g32p_row31_cosetWord_5219
  · exact g32p_row31_cosetWord_5220
  · exact g32p_row31_cosetWord_5221
  · exact g32p_row31_cosetWord_5222
  · exact g32p_row31_cosetWord_5223
  · exact g32p_row31_cosetWord_5224
  · exact g32p_row31_cosetWord_5225
  · exact g32p_row31_cosetWord_5226
  · exact g32p_row31_cosetWord_5227
  · exact g32p_row31_cosetWord_5228
  · exact g32p_row31_cosetWord_5229
  · exact g32p_row31_cosetWord_5230
  · exact g32p_row31_cosetWord_5231

theorem g32p_row31_cosetGeneratorBlock_0326 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 326 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 326 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 326 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5216 s
  · exact g32p_row31_cosetGeneratorStep_5217 s
  · exact g32p_row31_cosetGeneratorStep_5218 s
  · exact g32p_row31_cosetGeneratorStep_5219 s
  · exact g32p_row31_cosetGeneratorStep_5220 s
  · exact g32p_row31_cosetGeneratorStep_5221 s
  · exact g32p_row31_cosetGeneratorStep_5222 s
  · exact g32p_row31_cosetGeneratorStep_5223 s
  · exact g32p_row31_cosetGeneratorStep_5224 s
  · exact g32p_row31_cosetGeneratorStep_5225 s
  · exact g32p_row31_cosetGeneratorStep_5226 s
  · exact g32p_row31_cosetGeneratorStep_5227 s
  · exact g32p_row31_cosetGeneratorStep_5228 s
  · exact g32p_row31_cosetGeneratorStep_5229 s
  · exact g32p_row31_cosetGeneratorStep_5230 s
  · exact g32p_row31_cosetGeneratorStep_5231 s

theorem g32p_row31_cosetBranchBlock_0326 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 326 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 326 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 326 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5216 s
  · exact g32p_row31_cosetBranchStep_5217 s
  · exact g32p_row31_cosetBranchStep_5218 s
  · exact g32p_row31_cosetBranchStep_5219 s
  · exact g32p_row31_cosetBranchStep_5220 s
  · exact g32p_row31_cosetBranchStep_5221 s
  · exact g32p_row31_cosetBranchStep_5222 s
  · exact g32p_row31_cosetBranchStep_5223 s
  · exact g32p_row31_cosetBranchStep_5224 s
  · exact g32p_row31_cosetBranchStep_5225 s
  · exact g32p_row31_cosetBranchStep_5226 s
  · exact g32p_row31_cosetBranchStep_5227 s
  · exact g32p_row31_cosetBranchStep_5228 s
  · exact g32p_row31_cosetBranchStep_5229 s
  · exact g32p_row31_cosetBranchStep_5230 s
  · exact g32p_row31_cosetBranchStep_5231 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5232 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5232) = g32p_row31_cosetRepresentatives 5232 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5232 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5232) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5232))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5232)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5232 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5232) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5232))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5232)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5233 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5233) = g32p_row31_cosetRepresentatives 5233 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5233 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5233) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5233))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5233)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5233 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5233) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5233))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5233)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5234 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5234) = g32p_row31_cosetRepresentatives 5234 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5234 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5234) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5234))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5234)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5234 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5234) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5234))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5234)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5235 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5235) = g32p_row31_cosetRepresentatives 5235 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5235 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5235) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5235))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5235)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5235 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5235) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5235))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5235)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5236 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5236) = g32p_row31_cosetRepresentatives 5236 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5236 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5236) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5236))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5236)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5236 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5236) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5236))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5236)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5237 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5237) = g32p_row31_cosetRepresentatives 5237 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5237 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5237) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5237))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5237)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5237 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5237) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5237))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5237)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5238 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5238) = g32p_row31_cosetRepresentatives 5238 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5238 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5238) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5238))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5238)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5238 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5238) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5238))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5238)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5239 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5239) = g32p_row31_cosetRepresentatives 5239 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5239 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5239) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5239))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5239)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5239 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5239) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5239))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5239)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5240 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5240) = g32p_row31_cosetRepresentatives 5240 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5240 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5240) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5240))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5240)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5240 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5240) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5240))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5240)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5241 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5241) = g32p_row31_cosetRepresentatives 5241 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5241 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5241) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5241))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5241)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5241 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5241) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5241))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5241)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5242 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5242) = g32p_row31_cosetRepresentatives 5242 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5242 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5242) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5242))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5242)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5242 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5242) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5242))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5242)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5243 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5243) = g32p_row31_cosetRepresentatives 5243 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5243 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5243) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5243))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5243)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5243 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5243) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5243))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5243)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5244 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5244) = g32p_row31_cosetRepresentatives 5244 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5244 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5244) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5244))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5244)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5244 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5244) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5244))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5244)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5245 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5245) = g32p_row31_cosetRepresentatives 5245 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5245 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5245) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5245))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5245)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5245 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5245) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5245))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5245)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5246 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5246) = g32p_row31_cosetRepresentatives 5246 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5246 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5246) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5246))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5246)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5246 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5246) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5246))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5246)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5247 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5247) = g32p_row31_cosetRepresentatives 5247 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5247 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5247) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5247))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5247)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5247 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5247) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5247))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5247)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0327 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 327 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 327 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5232
  · exact g32p_row31_cosetWord_5233
  · exact g32p_row31_cosetWord_5234
  · exact g32p_row31_cosetWord_5235
  · exact g32p_row31_cosetWord_5236
  · exact g32p_row31_cosetWord_5237
  · exact g32p_row31_cosetWord_5238
  · exact g32p_row31_cosetWord_5239
  · exact g32p_row31_cosetWord_5240
  · exact g32p_row31_cosetWord_5241
  · exact g32p_row31_cosetWord_5242
  · exact g32p_row31_cosetWord_5243
  · exact g32p_row31_cosetWord_5244
  · exact g32p_row31_cosetWord_5245
  · exact g32p_row31_cosetWord_5246
  · exact g32p_row31_cosetWord_5247

theorem g32p_row31_cosetGeneratorBlock_0327 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 327 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 327 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 327 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5232 s
  · exact g32p_row31_cosetGeneratorStep_5233 s
  · exact g32p_row31_cosetGeneratorStep_5234 s
  · exact g32p_row31_cosetGeneratorStep_5235 s
  · exact g32p_row31_cosetGeneratorStep_5236 s
  · exact g32p_row31_cosetGeneratorStep_5237 s
  · exact g32p_row31_cosetGeneratorStep_5238 s
  · exact g32p_row31_cosetGeneratorStep_5239 s
  · exact g32p_row31_cosetGeneratorStep_5240 s
  · exact g32p_row31_cosetGeneratorStep_5241 s
  · exact g32p_row31_cosetGeneratorStep_5242 s
  · exact g32p_row31_cosetGeneratorStep_5243 s
  · exact g32p_row31_cosetGeneratorStep_5244 s
  · exact g32p_row31_cosetGeneratorStep_5245 s
  · exact g32p_row31_cosetGeneratorStep_5246 s
  · exact g32p_row31_cosetGeneratorStep_5247 s

theorem g32p_row31_cosetBranchBlock_0327 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 327 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 327 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 327 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5232 s
  · exact g32p_row31_cosetBranchStep_5233 s
  · exact g32p_row31_cosetBranchStep_5234 s
  · exact g32p_row31_cosetBranchStep_5235 s
  · exact g32p_row31_cosetBranchStep_5236 s
  · exact g32p_row31_cosetBranchStep_5237 s
  · exact g32p_row31_cosetBranchStep_5238 s
  · exact g32p_row31_cosetBranchStep_5239 s
  · exact g32p_row31_cosetBranchStep_5240 s
  · exact g32p_row31_cosetBranchStep_5241 s
  · exact g32p_row31_cosetBranchStep_5242 s
  · exact g32p_row31_cosetBranchStep_5243 s
  · exact g32p_row31_cosetBranchStep_5244 s
  · exact g32p_row31_cosetBranchStep_5245 s
  · exact g32p_row31_cosetBranchStep_5246 s
  · exact g32p_row31_cosetBranchStep_5247 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5248 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5248) = g32p_row31_cosetRepresentatives 5248 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5248 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5248) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5248))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5248)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5248 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5248) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5248))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5248)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5249 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5249) = g32p_row31_cosetRepresentatives 5249 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5249 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5249) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5249))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5249)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5249 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5249) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5249))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5249)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5250 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5250) = g32p_row31_cosetRepresentatives 5250 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5250 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5250) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5250))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5250)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5250 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5250) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5250))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5250)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5251 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5251) = g32p_row31_cosetRepresentatives 5251 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5251 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5251) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5251))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5251)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5251 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5251) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5251))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5251)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5252 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5252) = g32p_row31_cosetRepresentatives 5252 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5252 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5252) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5252))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5252)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5252 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5252) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5252))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5252)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5253 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5253) = g32p_row31_cosetRepresentatives 5253 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5253 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5253) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5253))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5253)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5253 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5253) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5253))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5253)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5254 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5254) = g32p_row31_cosetRepresentatives 5254 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5254 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5254) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5254))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5254)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5254 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5254) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5254))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5254)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5255 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5255) = g32p_row31_cosetRepresentatives 5255 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5255 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5255) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5255))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5255)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5255 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5255) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5255))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5255)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5256 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5256) = g32p_row31_cosetRepresentatives 5256 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5256) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5256))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5256)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5256) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5256))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5256)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5257 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5257) = g32p_row31_cosetRepresentatives 5257 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5257) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5257))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5257)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5257) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5257))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5257)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5258 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5258) = g32p_row31_cosetRepresentatives 5258 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5258) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5258))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5258)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5258) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5258))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5258)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5259 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5259) = g32p_row31_cosetRepresentatives 5259 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5259) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5259))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5259)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5259) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5259))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5259)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5260 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5260) = g32p_row31_cosetRepresentatives 5260 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5260) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5260))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5260)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5260) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5260))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5260)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5261 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5261) = g32p_row31_cosetRepresentatives 5261 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5261) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5261))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5261)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5261) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5261))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5261)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5262 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5262) = g32p_row31_cosetRepresentatives 5262 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5262) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5262))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5262)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5262) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5262))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5262)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5263 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5263) = g32p_row31_cosetRepresentatives 5263 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5263) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5263))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5263)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5263) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5263))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5263)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0328 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 328 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 328 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5248
  · exact g32p_row31_cosetWord_5249
  · exact g32p_row31_cosetWord_5250
  · exact g32p_row31_cosetWord_5251
  · exact g32p_row31_cosetWord_5252
  · exact g32p_row31_cosetWord_5253
  · exact g32p_row31_cosetWord_5254
  · exact g32p_row31_cosetWord_5255
  · exact g32p_row31_cosetWord_5256
  · exact g32p_row31_cosetWord_5257
  · exact g32p_row31_cosetWord_5258
  · exact g32p_row31_cosetWord_5259
  · exact g32p_row31_cosetWord_5260
  · exact g32p_row31_cosetWord_5261
  · exact g32p_row31_cosetWord_5262
  · exact g32p_row31_cosetWord_5263

theorem g32p_row31_cosetGeneratorBlock_0328 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 328 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 328 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 328 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5248 s
  · exact g32p_row31_cosetGeneratorStep_5249 s
  · exact g32p_row31_cosetGeneratorStep_5250 s
  · exact g32p_row31_cosetGeneratorStep_5251 s
  · exact g32p_row31_cosetGeneratorStep_5252 s
  · exact g32p_row31_cosetGeneratorStep_5253 s
  · exact g32p_row31_cosetGeneratorStep_5254 s
  · exact g32p_row31_cosetGeneratorStep_5255 s
  · exact g32p_row31_cosetGeneratorStep_5256 s
  · exact g32p_row31_cosetGeneratorStep_5257 s
  · exact g32p_row31_cosetGeneratorStep_5258 s
  · exact g32p_row31_cosetGeneratorStep_5259 s
  · exact g32p_row31_cosetGeneratorStep_5260 s
  · exact g32p_row31_cosetGeneratorStep_5261 s
  · exact g32p_row31_cosetGeneratorStep_5262 s
  · exact g32p_row31_cosetGeneratorStep_5263 s

theorem g32p_row31_cosetBranchBlock_0328 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 328 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 328 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 328 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5248 s
  · exact g32p_row31_cosetBranchStep_5249 s
  · exact g32p_row31_cosetBranchStep_5250 s
  · exact g32p_row31_cosetBranchStep_5251 s
  · exact g32p_row31_cosetBranchStep_5252 s
  · exact g32p_row31_cosetBranchStep_5253 s
  · exact g32p_row31_cosetBranchStep_5254 s
  · exact g32p_row31_cosetBranchStep_5255 s
  · exact g32p_row31_cosetBranchStep_5256 s
  · exact g32p_row31_cosetBranchStep_5257 s
  · exact g32p_row31_cosetBranchStep_5258 s
  · exact g32p_row31_cosetBranchStep_5259 s
  · exact g32p_row31_cosetBranchStep_5260 s
  · exact g32p_row31_cosetBranchStep_5261 s
  · exact g32p_row31_cosetBranchStep_5262 s
  · exact g32p_row31_cosetBranchStep_5263 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5264 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5264) = g32p_row31_cosetRepresentatives 5264 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5264) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5264))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5264)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5264) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5264))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5264)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5265 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5265) = g32p_row31_cosetRepresentatives 5265 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5265) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5265))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5265)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5265) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5265))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5265)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5266 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5266) = g32p_row31_cosetRepresentatives 5266 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5266) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5266))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5266)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5266) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5266))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5266)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5267 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5267) = g32p_row31_cosetRepresentatives 5267 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5267) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5267))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5267)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5267) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5267))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5267)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5268 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5268) = g32p_row31_cosetRepresentatives 5268 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5268) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5268))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5268)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5268) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5268))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5268)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5269 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5269) = g32p_row31_cosetRepresentatives 5269 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5269) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5269))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5269)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5269) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5269))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5269)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5270 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5270) = g32p_row31_cosetRepresentatives 5270 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5270) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5270))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5270)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5270) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5270))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5270)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5271 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5271) = g32p_row31_cosetRepresentatives 5271 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5271) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5271))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5271)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5271) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5271))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5271)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5272 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5272) = g32p_row31_cosetRepresentatives 5272 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5272) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5272))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5272)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5272) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5272))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5272)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5273 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5273) = g32p_row31_cosetRepresentatives 5273 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5273) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5273))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5273)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5273) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5273))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5273)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5274 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5274) = g32p_row31_cosetRepresentatives 5274 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5274) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5274))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5274)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5274) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5274))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5274)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5275 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5275) = g32p_row31_cosetRepresentatives 5275 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5275) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5275))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5275)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5275) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5275))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5275)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5276 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5276) = g32p_row31_cosetRepresentatives 5276 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5276) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5276))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5276)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5276) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5276))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5276)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5277 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5277) = g32p_row31_cosetRepresentatives 5277 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5277) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5277))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5277)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5277) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5277))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5277)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5278 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5278) = g32p_row31_cosetRepresentatives 5278 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5278) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5278))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5278)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5278) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5278))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5278)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5279 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5279) = g32p_row31_cosetRepresentatives 5279 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5279) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5279))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5279)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5279) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5279))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5279)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0329 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 329 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 329 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5264
  · exact g32p_row31_cosetWord_5265
  · exact g32p_row31_cosetWord_5266
  · exact g32p_row31_cosetWord_5267
  · exact g32p_row31_cosetWord_5268
  · exact g32p_row31_cosetWord_5269
  · exact g32p_row31_cosetWord_5270
  · exact g32p_row31_cosetWord_5271
  · exact g32p_row31_cosetWord_5272
  · exact g32p_row31_cosetWord_5273
  · exact g32p_row31_cosetWord_5274
  · exact g32p_row31_cosetWord_5275
  · exact g32p_row31_cosetWord_5276
  · exact g32p_row31_cosetWord_5277
  · exact g32p_row31_cosetWord_5278
  · exact g32p_row31_cosetWord_5279

theorem g32p_row31_cosetGeneratorBlock_0329 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 329 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 329 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 329 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5264 s
  · exact g32p_row31_cosetGeneratorStep_5265 s
  · exact g32p_row31_cosetGeneratorStep_5266 s
  · exact g32p_row31_cosetGeneratorStep_5267 s
  · exact g32p_row31_cosetGeneratorStep_5268 s
  · exact g32p_row31_cosetGeneratorStep_5269 s
  · exact g32p_row31_cosetGeneratorStep_5270 s
  · exact g32p_row31_cosetGeneratorStep_5271 s
  · exact g32p_row31_cosetGeneratorStep_5272 s
  · exact g32p_row31_cosetGeneratorStep_5273 s
  · exact g32p_row31_cosetGeneratorStep_5274 s
  · exact g32p_row31_cosetGeneratorStep_5275 s
  · exact g32p_row31_cosetGeneratorStep_5276 s
  · exact g32p_row31_cosetGeneratorStep_5277 s
  · exact g32p_row31_cosetGeneratorStep_5278 s
  · exact g32p_row31_cosetGeneratorStep_5279 s

theorem g32p_row31_cosetBranchBlock_0329 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 329 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 329 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 329 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5264 s
  · exact g32p_row31_cosetBranchStep_5265 s
  · exact g32p_row31_cosetBranchStep_5266 s
  · exact g32p_row31_cosetBranchStep_5267 s
  · exact g32p_row31_cosetBranchStep_5268 s
  · exact g32p_row31_cosetBranchStep_5269 s
  · exact g32p_row31_cosetBranchStep_5270 s
  · exact g32p_row31_cosetBranchStep_5271 s
  · exact g32p_row31_cosetBranchStep_5272 s
  · exact g32p_row31_cosetBranchStep_5273 s
  · exact g32p_row31_cosetBranchStep_5274 s
  · exact g32p_row31_cosetBranchStep_5275 s
  · exact g32p_row31_cosetBranchStep_5276 s
  · exact g32p_row31_cosetBranchStep_5277 s
  · exact g32p_row31_cosetBranchStep_5278 s
  · exact g32p_row31_cosetBranchStep_5279 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5280 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5280) = g32p_row31_cosetRepresentatives 5280 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5280) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5280))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5280)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5280) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5280))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5280)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5281 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5281) = g32p_row31_cosetRepresentatives 5281 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5281) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5281))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5281)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5281) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5281))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5281)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5282 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5282) = g32p_row31_cosetRepresentatives 5282 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5282) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5282))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5282)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5282) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5282))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5282)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5283 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5283) = g32p_row31_cosetRepresentatives 5283 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5283) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5283))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5283)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5283) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5283))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5283)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5284 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5284) = g32p_row31_cosetRepresentatives 5284 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5284) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5284))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5284)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5284) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5284))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5284)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5285 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5285) = g32p_row31_cosetRepresentatives 5285 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5285) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5285))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5285)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5285) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5285))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5285)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5286 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5286) = g32p_row31_cosetRepresentatives 5286 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5286) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5286))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5286)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5286) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5286))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5286)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5287 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5287) = g32p_row31_cosetRepresentatives 5287 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5287) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5287))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5287)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5287) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5287))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5287)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5288 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5288) = g32p_row31_cosetRepresentatives 5288 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5288) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5288))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5288)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5288) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5288))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5288)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5289 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5289) = g32p_row31_cosetRepresentatives 5289 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5289) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5289))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5289)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5289) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5289))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5289)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5290 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5290) = g32p_row31_cosetRepresentatives 5290 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5290) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5290))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5290)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5290) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5290))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5290)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5291 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5291) = g32p_row31_cosetRepresentatives 5291 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5291) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5291))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5291)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5291) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5291))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5291)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5292 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5292) = g32p_row31_cosetRepresentatives 5292 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5292) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5292))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5292)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5292) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5292))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5292)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5293 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5293) = g32p_row31_cosetRepresentatives 5293 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5293) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5293))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5293)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5293) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5293))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5293)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5294 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5294) = g32p_row31_cosetRepresentatives 5294 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5294) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5294))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5294)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5294) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5294))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5294)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5295 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5295) = g32p_row31_cosetRepresentatives 5295 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5295) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5295))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5295)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5295) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5295))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5295)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0330 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 330 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 330 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5280
  · exact g32p_row31_cosetWord_5281
  · exact g32p_row31_cosetWord_5282
  · exact g32p_row31_cosetWord_5283
  · exact g32p_row31_cosetWord_5284
  · exact g32p_row31_cosetWord_5285
  · exact g32p_row31_cosetWord_5286
  · exact g32p_row31_cosetWord_5287
  · exact g32p_row31_cosetWord_5288
  · exact g32p_row31_cosetWord_5289
  · exact g32p_row31_cosetWord_5290
  · exact g32p_row31_cosetWord_5291
  · exact g32p_row31_cosetWord_5292
  · exact g32p_row31_cosetWord_5293
  · exact g32p_row31_cosetWord_5294
  · exact g32p_row31_cosetWord_5295

theorem g32p_row31_cosetGeneratorBlock_0330 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 330 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 330 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 330 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5280 s
  · exact g32p_row31_cosetGeneratorStep_5281 s
  · exact g32p_row31_cosetGeneratorStep_5282 s
  · exact g32p_row31_cosetGeneratorStep_5283 s
  · exact g32p_row31_cosetGeneratorStep_5284 s
  · exact g32p_row31_cosetGeneratorStep_5285 s
  · exact g32p_row31_cosetGeneratorStep_5286 s
  · exact g32p_row31_cosetGeneratorStep_5287 s
  · exact g32p_row31_cosetGeneratorStep_5288 s
  · exact g32p_row31_cosetGeneratorStep_5289 s
  · exact g32p_row31_cosetGeneratorStep_5290 s
  · exact g32p_row31_cosetGeneratorStep_5291 s
  · exact g32p_row31_cosetGeneratorStep_5292 s
  · exact g32p_row31_cosetGeneratorStep_5293 s
  · exact g32p_row31_cosetGeneratorStep_5294 s
  · exact g32p_row31_cosetGeneratorStep_5295 s

theorem g32p_row31_cosetBranchBlock_0330 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 330 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 330 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 330 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5280 s
  · exact g32p_row31_cosetBranchStep_5281 s
  · exact g32p_row31_cosetBranchStep_5282 s
  · exact g32p_row31_cosetBranchStep_5283 s
  · exact g32p_row31_cosetBranchStep_5284 s
  · exact g32p_row31_cosetBranchStep_5285 s
  · exact g32p_row31_cosetBranchStep_5286 s
  · exact g32p_row31_cosetBranchStep_5287 s
  · exact g32p_row31_cosetBranchStep_5288 s
  · exact g32p_row31_cosetBranchStep_5289 s
  · exact g32p_row31_cosetBranchStep_5290 s
  · exact g32p_row31_cosetBranchStep_5291 s
  · exact g32p_row31_cosetBranchStep_5292 s
  · exact g32p_row31_cosetBranchStep_5293 s
  · exact g32p_row31_cosetBranchStep_5294 s
  · exact g32p_row31_cosetBranchStep_5295 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5296 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5296) = g32p_row31_cosetRepresentatives 5296 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5296) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5296))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5296)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5296) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5296))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5296)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5297 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5297) = g32p_row31_cosetRepresentatives 5297 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5297) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5297))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5297)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5297) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5297))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5297)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5298 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5298) = g32p_row31_cosetRepresentatives 5298 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5298) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5298))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5298)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5298) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5298))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5298)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5299 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5299) = g32p_row31_cosetRepresentatives 5299 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5299) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5299))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5299)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5299) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5299))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5299)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5300 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5300) = g32p_row31_cosetRepresentatives 5300 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5300) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5300))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5300)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5300) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5300))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5300)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5301 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5301) = g32p_row31_cosetRepresentatives 5301 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5301) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5301))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5301)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5301) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5301))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5301)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5302 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5302) = g32p_row31_cosetRepresentatives 5302 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5302) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5302))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5302)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5302) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5302))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5302)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5303 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5303) = g32p_row31_cosetRepresentatives 5303 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5303) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5303))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5303)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5303) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5303))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5303)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5304 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5304) = g32p_row31_cosetRepresentatives 5304 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5304) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5304))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5304)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5304) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5304))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5304)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5305 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5305) = g32p_row31_cosetRepresentatives 5305 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5305) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5305))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5305)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5305) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5305))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5305)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5306 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5306) = g32p_row31_cosetRepresentatives 5306 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5306) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5306))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5306)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5306) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5306))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5306)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5307 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5307) = g32p_row31_cosetRepresentatives 5307 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5307) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5307))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5307)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5307) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5307))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5307)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5308 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5308) = g32p_row31_cosetRepresentatives 5308 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5308) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5308))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5308)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5308) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5308))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5308)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5309 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5309) = g32p_row31_cosetRepresentatives 5309 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5309) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5309))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5309)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5309) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5309))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5309)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5310 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5310) = g32p_row31_cosetRepresentatives 5310 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5310) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5310))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5310)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5310) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5310))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5310)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5311 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5311) = g32p_row31_cosetRepresentatives 5311 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5311) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5311))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5311)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5311) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5311))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5311)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0331 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 331 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 331 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5296
  · exact g32p_row31_cosetWord_5297
  · exact g32p_row31_cosetWord_5298
  · exact g32p_row31_cosetWord_5299
  · exact g32p_row31_cosetWord_5300
  · exact g32p_row31_cosetWord_5301
  · exact g32p_row31_cosetWord_5302
  · exact g32p_row31_cosetWord_5303
  · exact g32p_row31_cosetWord_5304
  · exact g32p_row31_cosetWord_5305
  · exact g32p_row31_cosetWord_5306
  · exact g32p_row31_cosetWord_5307
  · exact g32p_row31_cosetWord_5308
  · exact g32p_row31_cosetWord_5309
  · exact g32p_row31_cosetWord_5310
  · exact g32p_row31_cosetWord_5311

theorem g32p_row31_cosetGeneratorBlock_0331 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 331 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 331 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 331 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5296 s
  · exact g32p_row31_cosetGeneratorStep_5297 s
  · exact g32p_row31_cosetGeneratorStep_5298 s
  · exact g32p_row31_cosetGeneratorStep_5299 s
  · exact g32p_row31_cosetGeneratorStep_5300 s
  · exact g32p_row31_cosetGeneratorStep_5301 s
  · exact g32p_row31_cosetGeneratorStep_5302 s
  · exact g32p_row31_cosetGeneratorStep_5303 s
  · exact g32p_row31_cosetGeneratorStep_5304 s
  · exact g32p_row31_cosetGeneratorStep_5305 s
  · exact g32p_row31_cosetGeneratorStep_5306 s
  · exact g32p_row31_cosetGeneratorStep_5307 s
  · exact g32p_row31_cosetGeneratorStep_5308 s
  · exact g32p_row31_cosetGeneratorStep_5309 s
  · exact g32p_row31_cosetGeneratorStep_5310 s
  · exact g32p_row31_cosetGeneratorStep_5311 s

theorem g32p_row31_cosetBranchBlock_0331 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 331 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 331 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 331 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5296 s
  · exact g32p_row31_cosetBranchStep_5297 s
  · exact g32p_row31_cosetBranchStep_5298 s
  · exact g32p_row31_cosetBranchStep_5299 s
  · exact g32p_row31_cosetBranchStep_5300 s
  · exact g32p_row31_cosetBranchStep_5301 s
  · exact g32p_row31_cosetBranchStep_5302 s
  · exact g32p_row31_cosetBranchStep_5303 s
  · exact g32p_row31_cosetBranchStep_5304 s
  · exact g32p_row31_cosetBranchStep_5305 s
  · exact g32p_row31_cosetBranchStep_5306 s
  · exact g32p_row31_cosetBranchStep_5307 s
  · exact g32p_row31_cosetBranchStep_5308 s
  · exact g32p_row31_cosetBranchStep_5309 s
  · exact g32p_row31_cosetBranchStep_5310 s
  · exact g32p_row31_cosetBranchStep_5311 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5312 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5312) = g32p_row31_cosetRepresentatives 5312 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5312) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5312))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5312)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5312) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5312))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5312)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5313 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5313) = g32p_row31_cosetRepresentatives 5313 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5313) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5313))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5313)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5313) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5313))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5313)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5314 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5314) = g32p_row31_cosetRepresentatives 5314 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5314) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5314))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5314)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5314) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5314))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5314)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5315 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5315) = g32p_row31_cosetRepresentatives 5315 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5315) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5315))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5315)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5315) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5315))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5315)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5316 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5316) = g32p_row31_cosetRepresentatives 5316 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5316) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5316))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5316)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5316) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5316))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5316)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5317 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5317) = g32p_row31_cosetRepresentatives 5317 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5317) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5317))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5317)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5317) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5317))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5317)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5318 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5318) = g32p_row31_cosetRepresentatives 5318 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5318) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5318))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5318)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5318) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5318))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5318)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5319 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5319) = g32p_row31_cosetRepresentatives 5319 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5319) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5319))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5319)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5319) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5319))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5319)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5320 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5320) = g32p_row31_cosetRepresentatives 5320 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5320) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5320))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5320)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5320) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5320))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5320)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5321 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5321) = g32p_row31_cosetRepresentatives 5321 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5321) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5321))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5321)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5321) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5321))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5321)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5322 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5322) = g32p_row31_cosetRepresentatives 5322 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5322) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5322))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5322)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5322) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5322))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5322)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5323 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5323) = g32p_row31_cosetRepresentatives 5323 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5323) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5323))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5323)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5323) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5323))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5323)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5324 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5324) = g32p_row31_cosetRepresentatives 5324 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5324) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5324))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5324)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5324) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5324))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5324)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5325 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5325) = g32p_row31_cosetRepresentatives 5325 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5325) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5325))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5325)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5325) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5325))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5325)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5326 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5326) = g32p_row31_cosetRepresentatives 5326 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5326) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5326))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5326)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5326) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5326))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5326)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5327 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5327) = g32p_row31_cosetRepresentatives 5327 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5327) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5327))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5327)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5327) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5327))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5327)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0332 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 332 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 332 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5312
  · exact g32p_row31_cosetWord_5313
  · exact g32p_row31_cosetWord_5314
  · exact g32p_row31_cosetWord_5315
  · exact g32p_row31_cosetWord_5316
  · exact g32p_row31_cosetWord_5317
  · exact g32p_row31_cosetWord_5318
  · exact g32p_row31_cosetWord_5319
  · exact g32p_row31_cosetWord_5320
  · exact g32p_row31_cosetWord_5321
  · exact g32p_row31_cosetWord_5322
  · exact g32p_row31_cosetWord_5323
  · exact g32p_row31_cosetWord_5324
  · exact g32p_row31_cosetWord_5325
  · exact g32p_row31_cosetWord_5326
  · exact g32p_row31_cosetWord_5327

theorem g32p_row31_cosetGeneratorBlock_0332 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 332 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 332 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 332 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5312 s
  · exact g32p_row31_cosetGeneratorStep_5313 s
  · exact g32p_row31_cosetGeneratorStep_5314 s
  · exact g32p_row31_cosetGeneratorStep_5315 s
  · exact g32p_row31_cosetGeneratorStep_5316 s
  · exact g32p_row31_cosetGeneratorStep_5317 s
  · exact g32p_row31_cosetGeneratorStep_5318 s
  · exact g32p_row31_cosetGeneratorStep_5319 s
  · exact g32p_row31_cosetGeneratorStep_5320 s
  · exact g32p_row31_cosetGeneratorStep_5321 s
  · exact g32p_row31_cosetGeneratorStep_5322 s
  · exact g32p_row31_cosetGeneratorStep_5323 s
  · exact g32p_row31_cosetGeneratorStep_5324 s
  · exact g32p_row31_cosetGeneratorStep_5325 s
  · exact g32p_row31_cosetGeneratorStep_5326 s
  · exact g32p_row31_cosetGeneratorStep_5327 s

theorem g32p_row31_cosetBranchBlock_0332 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 332 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 332 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 332 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5312 s
  · exact g32p_row31_cosetBranchStep_5313 s
  · exact g32p_row31_cosetBranchStep_5314 s
  · exact g32p_row31_cosetBranchStep_5315 s
  · exact g32p_row31_cosetBranchStep_5316 s
  · exact g32p_row31_cosetBranchStep_5317 s
  · exact g32p_row31_cosetBranchStep_5318 s
  · exact g32p_row31_cosetBranchStep_5319 s
  · exact g32p_row31_cosetBranchStep_5320 s
  · exact g32p_row31_cosetBranchStep_5321 s
  · exact g32p_row31_cosetBranchStep_5322 s
  · exact g32p_row31_cosetBranchStep_5323 s
  · exact g32p_row31_cosetBranchStep_5324 s
  · exact g32p_row31_cosetBranchStep_5325 s
  · exact g32p_row31_cosetBranchStep_5326 s
  · exact g32p_row31_cosetBranchStep_5327 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5328 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5328) = g32p_row31_cosetRepresentatives 5328 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5328 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5328) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5328))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5328)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5328 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5328) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5328))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5328)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5329 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5329) = g32p_row31_cosetRepresentatives 5329 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5329 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5329) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5329))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5329)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5329 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5329) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5329))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5329)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5330 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5330) = g32p_row31_cosetRepresentatives 5330 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5330 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5330) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5330))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5330)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5330 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5330) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5330))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5330)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5331 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5331) = g32p_row31_cosetRepresentatives 5331 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5331 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5331) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5331))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5331)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5331 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5331) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5331))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5331)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5332 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5332) = g32p_row31_cosetRepresentatives 5332 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5332 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5332) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5332))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5332)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5332 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5332) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5332))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5332)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5333 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5333) = g32p_row31_cosetRepresentatives 5333 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5333 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5333) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5333))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5333)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5333 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5333) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5333))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5333)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5334 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5334) = g32p_row31_cosetRepresentatives 5334 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5334 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5334) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5334))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5334)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5334 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5334) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5334))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5334)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5335 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5335) = g32p_row31_cosetRepresentatives 5335 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5335 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5335) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5335))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5335)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5335 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5335) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5335))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5335)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5336 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5336) = g32p_row31_cosetRepresentatives 5336 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5336 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5336) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5336))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5336)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5336 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5336) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5336))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5336)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5337 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5337) = g32p_row31_cosetRepresentatives 5337 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5337 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5337) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5337))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5337)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5337 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5337) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5337))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5337)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5338 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5338) = g32p_row31_cosetRepresentatives 5338 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5338 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5338) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5338))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5338)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5338 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5338) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5338))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5338)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5339 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5339) = g32p_row31_cosetRepresentatives 5339 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5339 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5339) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5339))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5339)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5339 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5339) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5339))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5339)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5340 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5340) = g32p_row31_cosetRepresentatives 5340 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5340 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5340) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5340))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5340)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5340 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5340) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5340))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5340)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5341 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5341) = g32p_row31_cosetRepresentatives 5341 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5341 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5341) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5341))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5341)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5341 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5341) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5341))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5341)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5342 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5342) = g32p_row31_cosetRepresentatives 5342 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5342 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5342) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5342))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5342)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5342 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5342) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5342))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5342)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5343 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5343) = g32p_row31_cosetRepresentatives 5343 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5343 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5343) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5343))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5343)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5343 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5343) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5343))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5343)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0333 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 333 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 333 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5328
  · exact g32p_row31_cosetWord_5329
  · exact g32p_row31_cosetWord_5330
  · exact g32p_row31_cosetWord_5331
  · exact g32p_row31_cosetWord_5332
  · exact g32p_row31_cosetWord_5333
  · exact g32p_row31_cosetWord_5334
  · exact g32p_row31_cosetWord_5335
  · exact g32p_row31_cosetWord_5336
  · exact g32p_row31_cosetWord_5337
  · exact g32p_row31_cosetWord_5338
  · exact g32p_row31_cosetWord_5339
  · exact g32p_row31_cosetWord_5340
  · exact g32p_row31_cosetWord_5341
  · exact g32p_row31_cosetWord_5342
  · exact g32p_row31_cosetWord_5343

theorem g32p_row31_cosetGeneratorBlock_0333 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 333 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 333 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 333 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5328 s
  · exact g32p_row31_cosetGeneratorStep_5329 s
  · exact g32p_row31_cosetGeneratorStep_5330 s
  · exact g32p_row31_cosetGeneratorStep_5331 s
  · exact g32p_row31_cosetGeneratorStep_5332 s
  · exact g32p_row31_cosetGeneratorStep_5333 s
  · exact g32p_row31_cosetGeneratorStep_5334 s
  · exact g32p_row31_cosetGeneratorStep_5335 s
  · exact g32p_row31_cosetGeneratorStep_5336 s
  · exact g32p_row31_cosetGeneratorStep_5337 s
  · exact g32p_row31_cosetGeneratorStep_5338 s
  · exact g32p_row31_cosetGeneratorStep_5339 s
  · exact g32p_row31_cosetGeneratorStep_5340 s
  · exact g32p_row31_cosetGeneratorStep_5341 s
  · exact g32p_row31_cosetGeneratorStep_5342 s
  · exact g32p_row31_cosetGeneratorStep_5343 s

theorem g32p_row31_cosetBranchBlock_0333 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 333 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 333 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 333 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5328 s
  · exact g32p_row31_cosetBranchStep_5329 s
  · exact g32p_row31_cosetBranchStep_5330 s
  · exact g32p_row31_cosetBranchStep_5331 s
  · exact g32p_row31_cosetBranchStep_5332 s
  · exact g32p_row31_cosetBranchStep_5333 s
  · exact g32p_row31_cosetBranchStep_5334 s
  · exact g32p_row31_cosetBranchStep_5335 s
  · exact g32p_row31_cosetBranchStep_5336 s
  · exact g32p_row31_cosetBranchStep_5337 s
  · exact g32p_row31_cosetBranchStep_5338 s
  · exact g32p_row31_cosetBranchStep_5339 s
  · exact g32p_row31_cosetBranchStep_5340 s
  · exact g32p_row31_cosetBranchStep_5341 s
  · exact g32p_row31_cosetBranchStep_5342 s
  · exact g32p_row31_cosetBranchStep_5343 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5344 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5344) = g32p_row31_cosetRepresentatives 5344 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5344 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5344) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5344))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5344)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5344 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5344) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5344))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5344)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5345 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5345) = g32p_row31_cosetRepresentatives 5345 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5345 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5345) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5345))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5345)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5345 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5345) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5345))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5345)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5346 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5346) = g32p_row31_cosetRepresentatives 5346 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5346 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5346) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5346))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5346)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5346 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5346) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5346))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5346)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5347 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5347) = g32p_row31_cosetRepresentatives 5347 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5347 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5347) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5347))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5347)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5347 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5347) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5347))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5347)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5348 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5348) = g32p_row31_cosetRepresentatives 5348 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5348 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5348) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5348))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5348)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5348 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5348) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5348))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5348)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5349 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5349) = g32p_row31_cosetRepresentatives 5349 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5349 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5349) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5349))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5349)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5349 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5349) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5349))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5349)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5350 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5350) = g32p_row31_cosetRepresentatives 5350 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5350 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5350) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5350))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5350)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5350 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5350) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5350))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5350)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5351 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5351) = g32p_row31_cosetRepresentatives 5351 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5351 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5351) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5351))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5351)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5351 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5351) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5351))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5351)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5352 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5352) = g32p_row31_cosetRepresentatives 5352 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5352 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5352) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5352))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5352)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5352 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5352) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5352))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5352)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5353 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5353) = g32p_row31_cosetRepresentatives 5353 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5353 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5353) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5353))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5353)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5353 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5353) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5353))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5353)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5354 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5354) = g32p_row31_cosetRepresentatives 5354 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5354 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5354) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5354))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5354)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5354 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5354) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5354))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5354)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5355 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5355) = g32p_row31_cosetRepresentatives 5355 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5355 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5355) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5355))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5355)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5355 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5355) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5355))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5355)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5356 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5356) = g32p_row31_cosetRepresentatives 5356 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5356 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5356) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5356))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5356)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5356 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5356) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5356))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5356)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5357 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5357) = g32p_row31_cosetRepresentatives 5357 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5357 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5357) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5357))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5357)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5357 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5357) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5357))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5357)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5358 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5358) = g32p_row31_cosetRepresentatives 5358 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5358 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5358) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5358))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5358)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5358 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5358) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5358))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5358)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5359 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5359) = g32p_row31_cosetRepresentatives 5359 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5359 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5359) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5359))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5359)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5359 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5359) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5359))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5359)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0334 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 334 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 334 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5344
  · exact g32p_row31_cosetWord_5345
  · exact g32p_row31_cosetWord_5346
  · exact g32p_row31_cosetWord_5347
  · exact g32p_row31_cosetWord_5348
  · exact g32p_row31_cosetWord_5349
  · exact g32p_row31_cosetWord_5350
  · exact g32p_row31_cosetWord_5351
  · exact g32p_row31_cosetWord_5352
  · exact g32p_row31_cosetWord_5353
  · exact g32p_row31_cosetWord_5354
  · exact g32p_row31_cosetWord_5355
  · exact g32p_row31_cosetWord_5356
  · exact g32p_row31_cosetWord_5357
  · exact g32p_row31_cosetWord_5358
  · exact g32p_row31_cosetWord_5359

theorem g32p_row31_cosetGeneratorBlock_0334 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 334 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 334 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 334 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5344 s
  · exact g32p_row31_cosetGeneratorStep_5345 s
  · exact g32p_row31_cosetGeneratorStep_5346 s
  · exact g32p_row31_cosetGeneratorStep_5347 s
  · exact g32p_row31_cosetGeneratorStep_5348 s
  · exact g32p_row31_cosetGeneratorStep_5349 s
  · exact g32p_row31_cosetGeneratorStep_5350 s
  · exact g32p_row31_cosetGeneratorStep_5351 s
  · exact g32p_row31_cosetGeneratorStep_5352 s
  · exact g32p_row31_cosetGeneratorStep_5353 s
  · exact g32p_row31_cosetGeneratorStep_5354 s
  · exact g32p_row31_cosetGeneratorStep_5355 s
  · exact g32p_row31_cosetGeneratorStep_5356 s
  · exact g32p_row31_cosetGeneratorStep_5357 s
  · exact g32p_row31_cosetGeneratorStep_5358 s
  · exact g32p_row31_cosetGeneratorStep_5359 s

theorem g32p_row31_cosetBranchBlock_0334 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 334 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 334 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 334 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5344 s
  · exact g32p_row31_cosetBranchStep_5345 s
  · exact g32p_row31_cosetBranchStep_5346 s
  · exact g32p_row31_cosetBranchStep_5347 s
  · exact g32p_row31_cosetBranchStep_5348 s
  · exact g32p_row31_cosetBranchStep_5349 s
  · exact g32p_row31_cosetBranchStep_5350 s
  · exact g32p_row31_cosetBranchStep_5351 s
  · exact g32p_row31_cosetBranchStep_5352 s
  · exact g32p_row31_cosetBranchStep_5353 s
  · exact g32p_row31_cosetBranchStep_5354 s
  · exact g32p_row31_cosetBranchStep_5355 s
  · exact g32p_row31_cosetBranchStep_5356 s
  · exact g32p_row31_cosetBranchStep_5357 s
  · exact g32p_row31_cosetBranchStep_5358 s
  · exact g32p_row31_cosetBranchStep_5359 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_5360 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5360) = g32p_row31_cosetRepresentatives 5360 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5360 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5360) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5360))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5360)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5360 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5360) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5360))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5360)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5361 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5361) = g32p_row31_cosetRepresentatives 5361 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5361 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5361) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5361))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5361)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5361 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5361) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5361))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5361)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5362 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5362) = g32p_row31_cosetRepresentatives 5362 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5362 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5362) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5362))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5362)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5362 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5362) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5362))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5362)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5363 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5363) = g32p_row31_cosetRepresentatives 5363 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5363 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5363) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5363))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5363)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5363 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5363) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5363))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5363)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5364 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5364) = g32p_row31_cosetRepresentatives 5364 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5364 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5364) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5364))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5364)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5364 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5364) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5364))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5364)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5365 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5365) = g32p_row31_cosetRepresentatives 5365 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5365 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5365) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5365))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5365)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5365 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5365) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5365))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5365)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5366 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5366) = g32p_row31_cosetRepresentatives 5366 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5366 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5366) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5366))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5366)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5366 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5366) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5366))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5366)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5367 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5367) = g32p_row31_cosetRepresentatives 5367 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5367 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5367) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5367))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5367)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5367 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5367) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5367))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5367)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5368 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5368) = g32p_row31_cosetRepresentatives 5368 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5368 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5368) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5368))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5368)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5368 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5368) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5368))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5368)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5369 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5369) = g32p_row31_cosetRepresentatives 5369 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5369 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5369) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5369))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5369)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5369 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5369) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5369))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5369)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5370 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5370) = g32p_row31_cosetRepresentatives 5370 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5370 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5370) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5370))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5370)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5370 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5370) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5370))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5370)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5371 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5371) = g32p_row31_cosetRepresentatives 5371 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5371 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5371) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5371))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5371)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5371 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5371) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5371))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5371)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5372 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5372) = g32p_row31_cosetRepresentatives 5372 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5372 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5372) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5372))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5372)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5372 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5372) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5372))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5372)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5373 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5373) = g32p_row31_cosetRepresentatives 5373 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5373 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5373) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5373))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5373)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5373 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5373) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5373))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5373)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5374 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5374) = g32p_row31_cosetRepresentatives 5374 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5374 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5374) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5374))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5374)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5374 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5374) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5374))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5374)) := by
  decide +kernel

theorem g32p_row31_cosetWord_5375 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 5375) = g32p_row31_cosetRepresentatives 5375 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_5375 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 5375) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 5375))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 5375)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_5375 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 5375) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 5375))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 5375)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0335 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 335 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 335 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_5360
  · exact g32p_row31_cosetWord_5361
  · exact g32p_row31_cosetWord_5362
  · exact g32p_row31_cosetWord_5363
  · exact g32p_row31_cosetWord_5364
  · exact g32p_row31_cosetWord_5365
  · exact g32p_row31_cosetWord_5366
  · exact g32p_row31_cosetWord_5367
  · exact g32p_row31_cosetWord_5368
  · exact g32p_row31_cosetWord_5369
  · exact g32p_row31_cosetWord_5370
  · exact g32p_row31_cosetWord_5371
  · exact g32p_row31_cosetWord_5372
  · exact g32p_row31_cosetWord_5373
  · exact g32p_row31_cosetWord_5374
  · exact g32p_row31_cosetWord_5375

theorem g32p_row31_cosetGeneratorBlock_0335 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 335 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 335 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 335 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_5360 s
  · exact g32p_row31_cosetGeneratorStep_5361 s
  · exact g32p_row31_cosetGeneratorStep_5362 s
  · exact g32p_row31_cosetGeneratorStep_5363 s
  · exact g32p_row31_cosetGeneratorStep_5364 s
  · exact g32p_row31_cosetGeneratorStep_5365 s
  · exact g32p_row31_cosetGeneratorStep_5366 s
  · exact g32p_row31_cosetGeneratorStep_5367 s
  · exact g32p_row31_cosetGeneratorStep_5368 s
  · exact g32p_row31_cosetGeneratorStep_5369 s
  · exact g32p_row31_cosetGeneratorStep_5370 s
  · exact g32p_row31_cosetGeneratorStep_5371 s
  · exact g32p_row31_cosetGeneratorStep_5372 s
  · exact g32p_row31_cosetGeneratorStep_5373 s
  · exact g32p_row31_cosetGeneratorStep_5374 s
  · exact g32p_row31_cosetGeneratorStep_5375 s

theorem g32p_row31_cosetBranchBlock_0335 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 335 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 335 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 335 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_5360 s
  · exact g32p_row31_cosetBranchStep_5361 s
  · exact g32p_row31_cosetBranchStep_5362 s
  · exact g32p_row31_cosetBranchStep_5363 s
  · exact g32p_row31_cosetBranchStep_5364 s
  · exact g32p_row31_cosetBranchStep_5365 s
  · exact g32p_row31_cosetBranchStep_5366 s
  · exact g32p_row31_cosetBranchStep_5367 s
  · exact g32p_row31_cosetBranchStep_5368 s
  · exact g32p_row31_cosetBranchStep_5369 s
  · exact g32p_row31_cosetBranchStep_5370 s
  · exact g32p_row31_cosetBranchStep_5371 s
  · exact g32p_row31_cosetBranchStep_5372 s
  · exact g32p_row31_cosetBranchStep_5373 s
  · exact g32p_row31_cosetBranchStep_5374 s
  · exact g32p_row31_cosetBranchStep_5375 s


end HodgeLean.Foundations.Program

end
