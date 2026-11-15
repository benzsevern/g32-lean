import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness28CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0799
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow28
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetWord_0256 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 256) = g32p_row28_cosetRepresentatives 256 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 256) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 256))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 256)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 256) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 256))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 256)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0257 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 257) = g32p_row28_cosetRepresentatives 257 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 257))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 257)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 257))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 257)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0258 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 258) = g32p_row28_cosetRepresentatives 258 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 258) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 258))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 258)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 258) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 258))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 258)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0259 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 259) = g32p_row28_cosetRepresentatives 259 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 259) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 259))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 259)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 259) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 259))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 259)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0260 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 260) = g32p_row28_cosetRepresentatives 260 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 260) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 260))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 260)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 260) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 260))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 260)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0261 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 261) = g32p_row28_cosetRepresentatives 261 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 261) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 261))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 261)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 261) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 261))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 261)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0262 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 262) = g32p_row28_cosetRepresentatives 262 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 262) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 262))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 262)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 262) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 262))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 262)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0263 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 263) = g32p_row28_cosetRepresentatives 263 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 263) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 263))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 263)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 263) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 263))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 263)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0264 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 264) = g32p_row28_cosetRepresentatives 264 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 264) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 264))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 264)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 264) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 264))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 264)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0265 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 265) = g32p_row28_cosetRepresentatives 265 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 265) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 265))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 265)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 265) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 265))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 265)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0266 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 266) = g32p_row28_cosetRepresentatives 266 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 266) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 266))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 266)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 266) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 266))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 266)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0267 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 267) = g32p_row28_cosetRepresentatives 267 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 267) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 267))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 267)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 267) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 267))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 267)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0268 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 268) = g32p_row28_cosetRepresentatives 268 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 268))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 268)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 268))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 268)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0269 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 269) = g32p_row28_cosetRepresentatives 269 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 269) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 269))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 269)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 269) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 269))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 269)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0270 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 270) = g32p_row28_cosetRepresentatives 270 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 270) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 270))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 270)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 270) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 270))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 270)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0271 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 271) = g32p_row28_cosetRepresentatives 271 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 271) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 271))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 271)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 271) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 271))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 271)) := by
  decide +kernel

theorem g32p_row28_cosetWordBlock_0016 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row28_cosetWords (g32p_finBlockIndex 320 16 r)) = g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 16 r) := by
  fin_cases r
  · exact g32p_row28_cosetWord_0256
  · exact g32p_row28_cosetWord_0257
  · exact g32p_row28_cosetWord_0258
  · exact g32p_row28_cosetWord_0259
  · exact g32p_row28_cosetWord_0260
  · exact g32p_row28_cosetWord_0261
  · exact g32p_row28_cosetWord_0262
  · exact g32p_row28_cosetWord_0263
  · exact g32p_row28_cosetWord_0264
  · exact g32p_row28_cosetWord_0265
  · exact g32p_row28_cosetWord_0266
  · exact g32p_row28_cosetWord_0267
  · exact g32p_row28_cosetWord_0268
  · exact g32p_row28_cosetWord_0269
  · exact g32p_row28_cosetWord_0270
  · exact g32p_row28_cosetWord_0271

theorem g32p_row28_cosetGeneratorBlock_0016 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 16 r)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s (g32p_finBlockIndex 320 16 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s (g32p_finBlockIndex 320 16 r))) := by
  fin_cases r
  · exact g32p_row28_cosetGeneratorStep_0256 s
  · exact g32p_row28_cosetGeneratorStep_0257 s
  · exact g32p_row28_cosetGeneratorStep_0258 s
  · exact g32p_row28_cosetGeneratorStep_0259 s
  · exact g32p_row28_cosetGeneratorStep_0260 s
  · exact g32p_row28_cosetGeneratorStep_0261 s
  · exact g32p_row28_cosetGeneratorStep_0262 s
  · exact g32p_row28_cosetGeneratorStep_0263 s
  · exact g32p_row28_cosetGeneratorStep_0264 s
  · exact g32p_row28_cosetGeneratorStep_0265 s
  · exact g32p_row28_cosetGeneratorStep_0266 s
  · exact g32p_row28_cosetGeneratorStep_0267 s
  · exact g32p_row28_cosetGeneratorStep_0268 s
  · exact g32p_row28_cosetGeneratorStep_0269 s
  · exact g32p_row28_cosetGeneratorStep_0270 s
  · exact g32p_row28_cosetGeneratorStep_0271 s

theorem g32p_row28_cosetBranchBlock_0016 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 16 r)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s (g32p_finBlockIndex 320 16 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s (g32p_finBlockIndex 320 16 r))) := by
  fin_cases r
  · exact g32p_row28_cosetBranchStep_0256 s
  · exact g32p_row28_cosetBranchStep_0257 s
  · exact g32p_row28_cosetBranchStep_0258 s
  · exact g32p_row28_cosetBranchStep_0259 s
  · exact g32p_row28_cosetBranchStep_0260 s
  · exact g32p_row28_cosetBranchStep_0261 s
  · exact g32p_row28_cosetBranchStep_0262 s
  · exact g32p_row28_cosetBranchStep_0263 s
  · exact g32p_row28_cosetBranchStep_0264 s
  · exact g32p_row28_cosetBranchStep_0265 s
  · exact g32p_row28_cosetBranchStep_0266 s
  · exact g32p_row28_cosetBranchStep_0267 s
  · exact g32p_row28_cosetBranchStep_0268 s
  · exact g32p_row28_cosetBranchStep_0269 s
  · exact g32p_row28_cosetBranchStep_0270 s
  · exact g32p_row28_cosetBranchStep_0271 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetWord_0272 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 272) = g32p_row28_cosetRepresentatives 272 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 272) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 272))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 272)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 272) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 272))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 272)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0273 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 273) = g32p_row28_cosetRepresentatives 273 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 273) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 273))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 273)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 273) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 273))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 273)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0274 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 274) = g32p_row28_cosetRepresentatives 274 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 274) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 274))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 274)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 274) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 274))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 274)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0275 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 275) = g32p_row28_cosetRepresentatives 275 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 275) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 275))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 275)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 275) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 275))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 275)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0276 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 276) = g32p_row28_cosetRepresentatives 276 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 276) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 276))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 276)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 276) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 276))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 276)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0277 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 277) = g32p_row28_cosetRepresentatives 277 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 277) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 277))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 277)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 277) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 277))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 277)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0278 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 278) = g32p_row28_cosetRepresentatives 278 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 278) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 278))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 278)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 278) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 278))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 278)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0279 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 279) = g32p_row28_cosetRepresentatives 279 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 279) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 279))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 279)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 279) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 279))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 279)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0280 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 280) = g32p_row28_cosetRepresentatives 280 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 280) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 280))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 280)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 280) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 280))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 280)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0281 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 281) = g32p_row28_cosetRepresentatives 281 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 281) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 281))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 281)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 281) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 281))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 281)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0282 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 282) = g32p_row28_cosetRepresentatives 282 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 282) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 282))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 282)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 282) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 282))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 282)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0283 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 283) = g32p_row28_cosetRepresentatives 283 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 283) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 283))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 283)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 283) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 283))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 283)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0284 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 284) = g32p_row28_cosetRepresentatives 284 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 284) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 284))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 284)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 284) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 284))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 284)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0285 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 285) = g32p_row28_cosetRepresentatives 285 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 285) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 285))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 285)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 285) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 285))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 285)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0286 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 286) = g32p_row28_cosetRepresentatives 286 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 286) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 286))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 286)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 286) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 286))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 286)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0287 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 287) = g32p_row28_cosetRepresentatives 287 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 287) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 287))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 287)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 287) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 287))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 287)) := by
  decide +kernel

theorem g32p_row28_cosetWordBlock_0017 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row28_cosetWords (g32p_finBlockIndex 320 17 r)) = g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 17 r) := by
  fin_cases r
  · exact g32p_row28_cosetWord_0272
  · exact g32p_row28_cosetWord_0273
  · exact g32p_row28_cosetWord_0274
  · exact g32p_row28_cosetWord_0275
  · exact g32p_row28_cosetWord_0276
  · exact g32p_row28_cosetWord_0277
  · exact g32p_row28_cosetWord_0278
  · exact g32p_row28_cosetWord_0279
  · exact g32p_row28_cosetWord_0280
  · exact g32p_row28_cosetWord_0281
  · exact g32p_row28_cosetWord_0282
  · exact g32p_row28_cosetWord_0283
  · exact g32p_row28_cosetWord_0284
  · exact g32p_row28_cosetWord_0285
  · exact g32p_row28_cosetWord_0286
  · exact g32p_row28_cosetWord_0287

theorem g32p_row28_cosetGeneratorBlock_0017 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 17 r)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s (g32p_finBlockIndex 320 17 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s (g32p_finBlockIndex 320 17 r))) := by
  fin_cases r
  · exact g32p_row28_cosetGeneratorStep_0272 s
  · exact g32p_row28_cosetGeneratorStep_0273 s
  · exact g32p_row28_cosetGeneratorStep_0274 s
  · exact g32p_row28_cosetGeneratorStep_0275 s
  · exact g32p_row28_cosetGeneratorStep_0276 s
  · exact g32p_row28_cosetGeneratorStep_0277 s
  · exact g32p_row28_cosetGeneratorStep_0278 s
  · exact g32p_row28_cosetGeneratorStep_0279 s
  · exact g32p_row28_cosetGeneratorStep_0280 s
  · exact g32p_row28_cosetGeneratorStep_0281 s
  · exact g32p_row28_cosetGeneratorStep_0282 s
  · exact g32p_row28_cosetGeneratorStep_0283 s
  · exact g32p_row28_cosetGeneratorStep_0284 s
  · exact g32p_row28_cosetGeneratorStep_0285 s
  · exact g32p_row28_cosetGeneratorStep_0286 s
  · exact g32p_row28_cosetGeneratorStep_0287 s

theorem g32p_row28_cosetBranchBlock_0017 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 17 r)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s (g32p_finBlockIndex 320 17 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s (g32p_finBlockIndex 320 17 r))) := by
  fin_cases r
  · exact g32p_row28_cosetBranchStep_0272 s
  · exact g32p_row28_cosetBranchStep_0273 s
  · exact g32p_row28_cosetBranchStep_0274 s
  · exact g32p_row28_cosetBranchStep_0275 s
  · exact g32p_row28_cosetBranchStep_0276 s
  · exact g32p_row28_cosetBranchStep_0277 s
  · exact g32p_row28_cosetBranchStep_0278 s
  · exact g32p_row28_cosetBranchStep_0279 s
  · exact g32p_row28_cosetBranchStep_0280 s
  · exact g32p_row28_cosetBranchStep_0281 s
  · exact g32p_row28_cosetBranchStep_0282 s
  · exact g32p_row28_cosetBranchStep_0283 s
  · exact g32p_row28_cosetBranchStep_0284 s
  · exact g32p_row28_cosetBranchStep_0285 s
  · exact g32p_row28_cosetBranchStep_0286 s
  · exact g32p_row28_cosetBranchStep_0287 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetWord_0288 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 288) = g32p_row28_cosetRepresentatives 288 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 288) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 288))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 288)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 288) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 288))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 288)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0289 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 289) = g32p_row28_cosetRepresentatives 289 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 289) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 289))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 289)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 289) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 289))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 289)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0290 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 290) = g32p_row28_cosetRepresentatives 290 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 290) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 290))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 290)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 290) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 290))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 290)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0291 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 291) = g32p_row28_cosetRepresentatives 291 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 291) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 291))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 291)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 291) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 291))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 291)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0292 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 292) = g32p_row28_cosetRepresentatives 292 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 292) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 292))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 292)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 292) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 292))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 292)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0293 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 293) = g32p_row28_cosetRepresentatives 293 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 293) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 293))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 293)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 293) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 293))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 293)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0294 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 294) = g32p_row28_cosetRepresentatives 294 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 294) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 294))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 294)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 294) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 294))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 294)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0295 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 295) = g32p_row28_cosetRepresentatives 295 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 295) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 295))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 295)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 295) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 295))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 295)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0296 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 296) = g32p_row28_cosetRepresentatives 296 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 296) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 296))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 296)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 296) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 296))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 296)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0297 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 297) = g32p_row28_cosetRepresentatives 297 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 297) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 297))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 297)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 297) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 297))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 297)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0298 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 298) = g32p_row28_cosetRepresentatives 298 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 298) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 298))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 298)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 298) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 298))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 298)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0299 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 299) = g32p_row28_cosetRepresentatives 299 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 299) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 299))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 299)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 299) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 299))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 299)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0300 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 300) = g32p_row28_cosetRepresentatives 300 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 300) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 300))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 300)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 300) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 300))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 300)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0301 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 301) = g32p_row28_cosetRepresentatives 301 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 301) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 301))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 301)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 301) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 301))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 301)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0302 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 302) = g32p_row28_cosetRepresentatives 302 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 302) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 302))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 302)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 302) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 302))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 302)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0303 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 303) = g32p_row28_cosetRepresentatives 303 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 303) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 303))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 303)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 303) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 303))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 303)) := by
  decide +kernel

theorem g32p_row28_cosetWordBlock_0018 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row28_cosetWords (g32p_finBlockIndex 320 18 r)) = g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 18 r) := by
  fin_cases r
  · exact g32p_row28_cosetWord_0288
  · exact g32p_row28_cosetWord_0289
  · exact g32p_row28_cosetWord_0290
  · exact g32p_row28_cosetWord_0291
  · exact g32p_row28_cosetWord_0292
  · exact g32p_row28_cosetWord_0293
  · exact g32p_row28_cosetWord_0294
  · exact g32p_row28_cosetWord_0295
  · exact g32p_row28_cosetWord_0296
  · exact g32p_row28_cosetWord_0297
  · exact g32p_row28_cosetWord_0298
  · exact g32p_row28_cosetWord_0299
  · exact g32p_row28_cosetWord_0300
  · exact g32p_row28_cosetWord_0301
  · exact g32p_row28_cosetWord_0302
  · exact g32p_row28_cosetWord_0303

theorem g32p_row28_cosetGeneratorBlock_0018 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 18 r)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s (g32p_finBlockIndex 320 18 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s (g32p_finBlockIndex 320 18 r))) := by
  fin_cases r
  · exact g32p_row28_cosetGeneratorStep_0288 s
  · exact g32p_row28_cosetGeneratorStep_0289 s
  · exact g32p_row28_cosetGeneratorStep_0290 s
  · exact g32p_row28_cosetGeneratorStep_0291 s
  · exact g32p_row28_cosetGeneratorStep_0292 s
  · exact g32p_row28_cosetGeneratorStep_0293 s
  · exact g32p_row28_cosetGeneratorStep_0294 s
  · exact g32p_row28_cosetGeneratorStep_0295 s
  · exact g32p_row28_cosetGeneratorStep_0296 s
  · exact g32p_row28_cosetGeneratorStep_0297 s
  · exact g32p_row28_cosetGeneratorStep_0298 s
  · exact g32p_row28_cosetGeneratorStep_0299 s
  · exact g32p_row28_cosetGeneratorStep_0300 s
  · exact g32p_row28_cosetGeneratorStep_0301 s
  · exact g32p_row28_cosetGeneratorStep_0302 s
  · exact g32p_row28_cosetGeneratorStep_0303 s

theorem g32p_row28_cosetBranchBlock_0018 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 18 r)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s (g32p_finBlockIndex 320 18 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s (g32p_finBlockIndex 320 18 r))) := by
  fin_cases r
  · exact g32p_row28_cosetBranchStep_0288 s
  · exact g32p_row28_cosetBranchStep_0289 s
  · exact g32p_row28_cosetBranchStep_0290 s
  · exact g32p_row28_cosetBranchStep_0291 s
  · exact g32p_row28_cosetBranchStep_0292 s
  · exact g32p_row28_cosetBranchStep_0293 s
  · exact g32p_row28_cosetBranchStep_0294 s
  · exact g32p_row28_cosetBranchStep_0295 s
  · exact g32p_row28_cosetBranchStep_0296 s
  · exact g32p_row28_cosetBranchStep_0297 s
  · exact g32p_row28_cosetBranchStep_0298 s
  · exact g32p_row28_cosetBranchStep_0299 s
  · exact g32p_row28_cosetBranchStep_0300 s
  · exact g32p_row28_cosetBranchStep_0301 s
  · exact g32p_row28_cosetBranchStep_0302 s
  · exact g32p_row28_cosetBranchStep_0303 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetWord_0304 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 304) = g32p_row28_cosetRepresentatives 304 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 304) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 304))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 304)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 304) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 304))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 304)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0305 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 305) = g32p_row28_cosetRepresentatives 305 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 305) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 305))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 305)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 305) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 305))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 305)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0306 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 306) = g32p_row28_cosetRepresentatives 306 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 306) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 306))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 306)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 306) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 306))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 306)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0307 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 307) = g32p_row28_cosetRepresentatives 307 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 307) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 307))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 307)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 307) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 307))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 307)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0308 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 308) = g32p_row28_cosetRepresentatives 308 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 308) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 308))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 308)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 308) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 308))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 308)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0309 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 309) = g32p_row28_cosetRepresentatives 309 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 309) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 309))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 309)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 309) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 309))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 309)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0310 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 310) = g32p_row28_cosetRepresentatives 310 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 310) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 310))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 310)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 310) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 310))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 310)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0311 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 311) = g32p_row28_cosetRepresentatives 311 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 311) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 311))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 311)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 311) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 311))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 311)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0312 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 312) = g32p_row28_cosetRepresentatives 312 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 312) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 312))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 312)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 312) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 312))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 312)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0313 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 313) = g32p_row28_cosetRepresentatives 313 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 313) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 313))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 313)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 313) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 313))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 313)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0314 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 314) = g32p_row28_cosetRepresentatives 314 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 314) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 314))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 314)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 314) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 314))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 314)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0315 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 315) = g32p_row28_cosetRepresentatives 315 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 315) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 315))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 315)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 315) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 315))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 315)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0316 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 316) = g32p_row28_cosetRepresentatives 316 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 316) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 316))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 316)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 316) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 316))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 316)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0317 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 317) = g32p_row28_cosetRepresentatives 317 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 317) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 317))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 317)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 317) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 317))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 317)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0318 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 318) = g32p_row28_cosetRepresentatives 318 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 318) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 318))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 318)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 318) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 318))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 318)) := by
  decide +kernel

theorem g32p_row28_cosetWord_0319 :
    g32p_archiveIntegralWord (g32p_row28_cosetWords 319) = g32p_row28_cosetRepresentatives 319 := by
  decide +kernel

theorem g32p_row28_cosetGeneratorStep_0319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives 319) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s 319))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s 319)) := by
  decide +kernel

theorem g32p_row28_cosetBranchStep_0319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives 319) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s 319))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s 319)) := by
  decide +kernel

theorem g32p_row28_cosetWordBlock_0019 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row28_cosetWords (g32p_finBlockIndex 320 19 r)) = g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 19 r) := by
  fin_cases r
  · exact g32p_row28_cosetWord_0304
  · exact g32p_row28_cosetWord_0305
  · exact g32p_row28_cosetWord_0306
  · exact g32p_row28_cosetWord_0307
  · exact g32p_row28_cosetWord_0308
  · exact g32p_row28_cosetWord_0309
  · exact g32p_row28_cosetWord_0310
  · exact g32p_row28_cosetWord_0311
  · exact g32p_row28_cosetWord_0312
  · exact g32p_row28_cosetWord_0313
  · exact g32p_row28_cosetWord_0314
  · exact g32p_row28_cosetWord_0315
  · exact g32p_row28_cosetWord_0316
  · exact g32p_row28_cosetWord_0317
  · exact g32p_row28_cosetWord_0318
  · exact g32p_row28_cosetWord_0319

theorem g32p_row28_cosetGeneratorBlock_0019 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 19 r)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s (g32p_finBlockIndex 320 19 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s (g32p_finBlockIndex 320 19 r))) := by
  fin_cases r
  · exact g32p_row28_cosetGeneratorStep_0304 s
  · exact g32p_row28_cosetGeneratorStep_0305 s
  · exact g32p_row28_cosetGeneratorStep_0306 s
  · exact g32p_row28_cosetGeneratorStep_0307 s
  · exact g32p_row28_cosetGeneratorStep_0308 s
  · exact g32p_row28_cosetGeneratorStep_0309 s
  · exact g32p_row28_cosetGeneratorStep_0310 s
  · exact g32p_row28_cosetGeneratorStep_0311 s
  · exact g32p_row28_cosetGeneratorStep_0312 s
  · exact g32p_row28_cosetGeneratorStep_0313 s
  · exact g32p_row28_cosetGeneratorStep_0314 s
  · exact g32p_row28_cosetGeneratorStep_0315 s
  · exact g32p_row28_cosetGeneratorStep_0316 s
  · exact g32p_row28_cosetGeneratorStep_0317 s
  · exact g32p_row28_cosetGeneratorStep_0318 s
  · exact g32p_row28_cosetGeneratorStep_0319 s

theorem g32p_row28_cosetBranchBlock_0019 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices s) (g32p_row28_cosetRepresentatives (g32p_finBlockIndex 320 19 r)) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetBranchNext s (g32p_finBlockIndex 320 19 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetBranchFactor s (g32p_finBlockIndex 320 19 r))) := by
  fin_cases r
  · exact g32p_row28_cosetBranchStep_0304 s
  · exact g32p_row28_cosetBranchStep_0305 s
  · exact g32p_row28_cosetBranchStep_0306 s
  · exact g32p_row28_cosetBranchStep_0307 s
  · exact g32p_row28_cosetBranchStep_0308 s
  · exact g32p_row28_cosetBranchStep_0309 s
  · exact g32p_row28_cosetBranchStep_0310 s
  · exact g32p_row28_cosetBranchStep_0311 s
  · exact g32p_row28_cosetBranchStep_0312 s
  · exact g32p_row28_cosetBranchStep_0313 s
  · exact g32p_row28_cosetBranchStep_0314 s
  · exact g32p_row28_cosetBranchStep_0315 s
  · exact g32p_row28_cosetBranchStep_0316 s
  · exact g32p_row28_cosetBranchStep_0317 s
  · exact g32p_row28_cosetBranchStep_0318 s
  · exact g32p_row28_cosetBranchStep_0319 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row28_cosetWord (i : Fin 320) :
    g32p_archiveIntegralWord (g32p_row28_cosetWords i) = g32p_row28_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row28_cosetWordBlock_0000
  · exact g32p_row28_cosetWordBlock_0001
  · exact g32p_row28_cosetWordBlock_0002
  · exact g32p_row28_cosetWordBlock_0003
  · exact g32p_row28_cosetWordBlock_0004
  · exact g32p_row28_cosetWordBlock_0005
  · exact g32p_row28_cosetWordBlock_0006
  · exact g32p_row28_cosetWordBlock_0007
  · exact g32p_row28_cosetWordBlock_0008
  · exact g32p_row28_cosetWordBlock_0009
  · exact g32p_row28_cosetWordBlock_0010
  · exact g32p_row28_cosetWordBlock_0011
  · exact g32p_row28_cosetWordBlock_0012
  · exact g32p_row28_cosetWordBlock_0013
  · exact g32p_row28_cosetWordBlock_0014
  · exact g32p_row28_cosetWordBlock_0015
  · exact g32p_row28_cosetWordBlock_0016
  · exact g32p_row28_cosetWordBlock_0017
  · exact g32p_row28_cosetWordBlock_0018
  · exact g32p_row28_cosetWordBlock_0019


def g32p_row28_cosetActualRepresentatives (i : Fin 320) : g32p_G := g32p_archiveWord (g32p_row28_cosetWords i)

theorem g32p_row28_cosetActualRepresentatives_map (i : Fin 320) :
    b4b_toMatrix (g32p_row28_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row28_cosetRepresentatives i)) := by
  rw [g32p_row28_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row28_cosetWord]

theorem g32p_row28_cosetGeneratorStep (s : Fin 4) (i : Fin 320) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row28_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetGeneratorNext s i))
        (g32p_row09_groupNodes (g32p_row28_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row28_cosetGeneratorBlock_0000 s
  · exact g32p_row28_cosetGeneratorBlock_0001 s
  · exact g32p_row28_cosetGeneratorBlock_0002 s
  · exact g32p_row28_cosetGeneratorBlock_0003 s
  · exact g32p_row28_cosetGeneratorBlock_0004 s
  · exact g32p_row28_cosetGeneratorBlock_0005 s
  · exact g32p_row28_cosetGeneratorBlock_0006 s
  · exact g32p_row28_cosetGeneratorBlock_0007 s
  · exact g32p_row28_cosetGeneratorBlock_0008 s
  · exact g32p_row28_cosetGeneratorBlock_0009 s
  · exact g32p_row28_cosetGeneratorBlock_0010 s
  · exact g32p_row28_cosetGeneratorBlock_0011 s
  · exact g32p_row28_cosetGeneratorBlock_0012 s
  · exact g32p_row28_cosetGeneratorBlock_0013 s
  · exact g32p_row28_cosetGeneratorBlock_0014 s
  · exact g32p_row28_cosetGeneratorBlock_0015 s
  · exact g32p_row28_cosetGeneratorBlock_0016 s
  · exact g32p_row28_cosetGeneratorBlock_0017 s
  · exact g32p_row28_cosetGeneratorBlock_0018 s
  · exact g32p_row28_cosetGeneratorBlock_0019 s


theorem g32p_row28_cosetActualStep (s : Fin 4) (i : Fin 320) :
    g32p_word (g32p_archiveWords s) * g32p_row28_cosetActualRepresentatives i =
      g32p_row28_cosetActualRepresentatives (g32p_row28_cosetGeneratorNext s i) *
        (g32p_row09_groupEquiv (g32p_row28_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row28_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row28_cosetActualRepresentatives (g32p_row28_cosetGeneratorNext s i) *
      (g32p_row09_groupEquiv (g32p_row28_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row28_cosetActualRepresentatives_map,
    g32p_row28_cosetActualRepresentatives_map, g32p_row09_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row28_cosetGeneratorStep]

theorem g32p_row28_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row28_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row28_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row28_cosetGeneratorNext
      (fun s i => g32p_row09_groupEquiv (g32p_row28_cosetGeneratorFactor s i))
    exact g32p_row28_cosetActualStep
  · rw [g32p_row28_finiteSupplier_order]
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

theorem g32p_row28_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 0)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 0)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 0) = g32p_row28_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 1)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 1)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 1) = g32p_row28_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 2)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 2)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 2) = g32p_row28_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 3)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 3)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 3) = g32p_row28_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 4)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 4)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 4) = g32p_row28_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 5)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 5)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 5) = g32p_row28_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 6)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 6)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 6) = g32p_row28_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 7)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 7)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 7) = g32p_row28_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 8)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 8)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 8) = g32p_row28_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 9)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 9)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 9) = g32p_row28_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 11)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 10)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 10) = g32p_row28_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 12)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 11)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 11) = g32p_row28_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 13)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 12)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 12) = g32p_row28_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 14)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 13)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 13) = g32p_row28_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 15)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 14)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 14) = g32p_row28_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 16)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 15)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 15) = g32p_row28_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 (g32p_finBlockIndex 128 0 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 0 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 0 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 0 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 0 r)) = g32p_row28_cosetExponents0 (g32p_finBlockIndex 128 0 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_0_0000
  · exact g32p_row28_cosetMonodromy_0_0001
  · exact g32p_row28_cosetMonodromy_0_0002
  · exact g32p_row28_cosetMonodromy_0_0003
  · exact g32p_row28_cosetMonodromy_0_0004
  · exact g32p_row28_cosetMonodromy_0_0005
  · exact g32p_row28_cosetMonodromy_0_0006
  · exact g32p_row28_cosetMonodromy_0_0007
  · exact g32p_row28_cosetMonodromy_0_0008
  · exact g32p_row28_cosetMonodromy_0_0009
  · exact g32p_row28_cosetMonodromy_0_0010
  · exact g32p_row28_cosetMonodromy_0_0011
  · exact g32p_row28_cosetMonodromy_0_0012
  · exact g32p_row28_cosetMonodromy_0_0013
  · exact g32p_row28_cosetMonodromy_0_0014
  · exact g32p_row28_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 17)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 16)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 16) = g32p_row28_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 19)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 17)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 17) = g32p_row28_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 20)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 18)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 18) = g32p_row28_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 21)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 19)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 19) = g32p_row28_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 22)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 20)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 20) = g32p_row28_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 23)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 21)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 21) = g32p_row28_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 24)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 22)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 22) = g32p_row28_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 25)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 23)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 23) = g32p_row28_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 26)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 24)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 24) = g32p_row28_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 27)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 25)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 25) = g32p_row28_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 29)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 26)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 26) = g32p_row28_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 31)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 27)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 27) = g32p_row28_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 32)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 28)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 28) = g32p_row28_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 33)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 29)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 29) = g32p_row28_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 35)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 30)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 30) = g32p_row28_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 36)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 31)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 31) = g32p_row28_cosetExponents0 31 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock0_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 (g32p_finBlockIndex 128 1 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 1 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 1 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 1 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 1 r)) = g32p_row28_cosetExponents0 (g32p_finBlockIndex 128 1 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_0_0016
  · exact g32p_row28_cosetMonodromy_0_0017
  · exact g32p_row28_cosetMonodromy_0_0018
  · exact g32p_row28_cosetMonodromy_0_0019
  · exact g32p_row28_cosetMonodromy_0_0020
  · exact g32p_row28_cosetMonodromy_0_0021
  · exact g32p_row28_cosetMonodromy_0_0022
  · exact g32p_row28_cosetMonodromy_0_0023
  · exact g32p_row28_cosetMonodromy_0_0024
  · exact g32p_row28_cosetMonodromy_0_0025
  · exact g32p_row28_cosetMonodromy_0_0026
  · exact g32p_row28_cosetMonodromy_0_0027
  · exact g32p_row28_cosetMonodromy_0_0028
  · exact g32p_row28_cosetMonodromy_0_0029
  · exact g32p_row28_cosetMonodromy_0_0030
  · exact g32p_row28_cosetMonodromy_0_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_0_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 37)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 32)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 32) = g32p_row28_cosetExponents0 32 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 38)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 33)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 33) = g32p_row28_cosetExponents0 33 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 39)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 34)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 34) = g32p_row28_cosetExponents0 34 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 41)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 35)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 35) = g32p_row28_cosetExponents0 35 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 44)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 36)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 36) = g32p_row28_cosetExponents0 36 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 45)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 37)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 37) = g32p_row28_cosetExponents0 37 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 46)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 38)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 38) = g32p_row28_cosetExponents0 38 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 47)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 39)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 39) = g32p_row28_cosetExponents0 39 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 50)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 40)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 40) = g32p_row28_cosetExponents0 40 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 51)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 41)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 41) = g32p_row28_cosetExponents0 41 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 52)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 42)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 42) = g32p_row28_cosetExponents0 42 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 53)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 43)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 43) = g32p_row28_cosetExponents0 43 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 54)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 44)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 44) = g32p_row28_cosetExponents0 44 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 56)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 45)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 45) = g32p_row28_cosetExponents0 45 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 57) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 57)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 46)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 46) = g32p_row28_cosetExponents0 46 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 58)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 47)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 47) = g32p_row28_cosetExponents0 47 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock0_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 (g32p_finBlockIndex 128 2 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 2 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 2 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 2 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 2 r)) = g32p_row28_cosetExponents0 (g32p_finBlockIndex 128 2 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_0_0032
  · exact g32p_row28_cosetMonodromy_0_0033
  · exact g32p_row28_cosetMonodromy_0_0034
  · exact g32p_row28_cosetMonodromy_0_0035
  · exact g32p_row28_cosetMonodromy_0_0036
  · exact g32p_row28_cosetMonodromy_0_0037
  · exact g32p_row28_cosetMonodromy_0_0038
  · exact g32p_row28_cosetMonodromy_0_0039
  · exact g32p_row28_cosetMonodromy_0_0040
  · exact g32p_row28_cosetMonodromy_0_0041
  · exact g32p_row28_cosetMonodromy_0_0042
  · exact g32p_row28_cosetMonodromy_0_0043
  · exact g32p_row28_cosetMonodromy_0_0044
  · exact g32p_row28_cosetMonodromy_0_0045
  · exact g32p_row28_cosetMonodromy_0_0046
  · exact g32p_row28_cosetMonodromy_0_0047


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_0_0048 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 59)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 48)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 48) = g32p_row28_cosetExponents0 48 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0049 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 60) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 60)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 49)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 49) = g32p_row28_cosetExponents0 49 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0050 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 61)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 50)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 50) = g32p_row28_cosetExponents0 50 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0051 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 62)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 51)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 51) = g32p_row28_cosetExponents0 51 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0052 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 64)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 52)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 52) = g32p_row28_cosetExponents0 52 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0053 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 69)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 53)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 53) = g32p_row28_cosetExponents0 53 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0054 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 72)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 54)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 54) = g32p_row28_cosetExponents0 54 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0055 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 73)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 55)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 55) = g32p_row28_cosetExponents0 55 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0056 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 75)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 56)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 56) = g32p_row28_cosetExponents0 56 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0057 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 76)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 57)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 57) = g32p_row28_cosetExponents0 57 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0058 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 77)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 58)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 58) = g32p_row28_cosetExponents0 58 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0059 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 78) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 78)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 59)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 59) = g32p_row28_cosetExponents0 59 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0060 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 80)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 60)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 60) = g32p_row28_cosetExponents0 60 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0061 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 81)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 61)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 61) = g32p_row28_cosetExponents0 61 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0062 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 82)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 62)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 62) = g32p_row28_cosetExponents0 62 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0063 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 84) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 84)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 63)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 63) = g32p_row28_cosetExponents0 63 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock0_0003 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 (g32p_finBlockIndex 128 3 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 3 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 3 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 3 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 3 r)) = g32p_row28_cosetExponents0 (g32p_finBlockIndex 128 3 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_0_0048
  · exact g32p_row28_cosetMonodromy_0_0049
  · exact g32p_row28_cosetMonodromy_0_0050
  · exact g32p_row28_cosetMonodromy_0_0051
  · exact g32p_row28_cosetMonodromy_0_0052
  · exact g32p_row28_cosetMonodromy_0_0053
  · exact g32p_row28_cosetMonodromy_0_0054
  · exact g32p_row28_cosetMonodromy_0_0055
  · exact g32p_row28_cosetMonodromy_0_0056
  · exact g32p_row28_cosetMonodromy_0_0057
  · exact g32p_row28_cosetMonodromy_0_0058
  · exact g32p_row28_cosetMonodromy_0_0059
  · exact g32p_row28_cosetMonodromy_0_0060
  · exact g32p_row28_cosetMonodromy_0_0061
  · exact g32p_row28_cosetMonodromy_0_0062
  · exact g32p_row28_cosetMonodromy_0_0063


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_0_0064 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 85)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 64)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 64) = g32p_row28_cosetExponents0 64 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0065 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 88)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 65)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 65) = g32p_row28_cosetExponents0 65 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0066 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 91) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 91)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 66)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 66) = g32p_row28_cosetExponents0 66 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0067 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 92) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 92)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 67)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 67) = g32p_row28_cosetExponents0 67 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0068 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 93) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 93)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 68)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 68) = g32p_row28_cosetExponents0 68 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0069 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 98) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 98)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 69)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 69) = g32p_row28_cosetExponents0 69 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0070 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 101) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 101)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 70)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 70) = g32p_row28_cosetExponents0 70 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0071 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 102) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 102)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 71)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 71) = g32p_row28_cosetExponents0 71 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0072 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 105) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 105)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 72)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 72) = g32p_row28_cosetExponents0 72 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0073 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 106) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 106)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 73)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 73) = g32p_row28_cosetExponents0 73 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0074 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 107) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 107)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 74)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 74) = g32p_row28_cosetExponents0 74 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0075 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 110) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 110)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 75)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 75) = g32p_row28_cosetExponents0 75 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0076 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 111) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 111)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 76)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 76) = g32p_row28_cosetExponents0 76 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0077 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 113) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 113)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 77)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 77) = g32p_row28_cosetExponents0 77 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0078 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 116) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 116)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 78)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 78) = g32p_row28_cosetExponents0 78 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0079 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 117) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 117)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 79)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 79) = g32p_row28_cosetExponents0 79 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock0_0004 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 (g32p_finBlockIndex 128 4 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 4 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 4 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 4 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 4 r)) = g32p_row28_cosetExponents0 (g32p_finBlockIndex 128 4 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_0_0064
  · exact g32p_row28_cosetMonodromy_0_0065
  · exact g32p_row28_cosetMonodromy_0_0066
  · exact g32p_row28_cosetMonodromy_0_0067
  · exact g32p_row28_cosetMonodromy_0_0068
  · exact g32p_row28_cosetMonodromy_0_0069
  · exact g32p_row28_cosetMonodromy_0_0070
  · exact g32p_row28_cosetMonodromy_0_0071
  · exact g32p_row28_cosetMonodromy_0_0072
  · exact g32p_row28_cosetMonodromy_0_0073
  · exact g32p_row28_cosetMonodromy_0_0074
  · exact g32p_row28_cosetMonodromy_0_0075
  · exact g32p_row28_cosetMonodromy_0_0076
  · exact g32p_row28_cosetMonodromy_0_0077
  · exact g32p_row28_cosetMonodromy_0_0078
  · exact g32p_row28_cosetMonodromy_0_0079


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_0_0080 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 119) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 119)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 80)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 80) = g32p_row28_cosetExponents0 80 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0081 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 120) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 120)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 81)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 81) = g32p_row28_cosetExponents0 81 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0082 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 121) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 121)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 82)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 82) = g32p_row28_cosetExponents0 82 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0083 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 122) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 122)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 83)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 83) = g32p_row28_cosetExponents0 83 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0084 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 123) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 123)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 84)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 84) = g32p_row28_cosetExponents0 84 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0085 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 124) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 124)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 85)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 85) = g32p_row28_cosetExponents0 85 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0086 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 125) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 125)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 86)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 86) = g32p_row28_cosetExponents0 86 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0087 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 133) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 133)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 87)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 87) = g32p_row28_cosetExponents0 87 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0088 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 139) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 139)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 88)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 88) = g32p_row28_cosetExponents0 88 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0089 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 140) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 140)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 89)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 89) = g32p_row28_cosetExponents0 89 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0090 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 142) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 142)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 90)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 90) = g32p_row28_cosetExponents0 90 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0091 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 143) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 143)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 91)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 91) = g32p_row28_cosetExponents0 91 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0092 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 146) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 146)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 92)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 92) = g32p_row28_cosetExponents0 92 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0093 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 147) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 147)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 93)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 93) = g32p_row28_cosetExponents0 93 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0094 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 150) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 150)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 94)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 94) = g32p_row28_cosetExponents0 94 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0095 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 151) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 151)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 95)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 95) = g32p_row28_cosetExponents0 95 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock0_0005 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 (g32p_finBlockIndex 128 5 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 5 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 5 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 5 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 5 r)) = g32p_row28_cosetExponents0 (g32p_finBlockIndex 128 5 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_0_0080
  · exact g32p_row28_cosetMonodromy_0_0081
  · exact g32p_row28_cosetMonodromy_0_0082
  · exact g32p_row28_cosetMonodromy_0_0083
  · exact g32p_row28_cosetMonodromy_0_0084
  · exact g32p_row28_cosetMonodromy_0_0085
  · exact g32p_row28_cosetMonodromy_0_0086
  · exact g32p_row28_cosetMonodromy_0_0087
  · exact g32p_row28_cosetMonodromy_0_0088
  · exact g32p_row28_cosetMonodromy_0_0089
  · exact g32p_row28_cosetMonodromy_0_0090
  · exact g32p_row28_cosetMonodromy_0_0091
  · exact g32p_row28_cosetMonodromy_0_0092
  · exact g32p_row28_cosetMonodromy_0_0093
  · exact g32p_row28_cosetMonodromy_0_0094
  · exact g32p_row28_cosetMonodromy_0_0095


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_0_0096 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 152) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 152)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 96)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 96) = g32p_row28_cosetExponents0 96 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0097 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 157) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 157)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 97)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 97) = g32p_row28_cosetExponents0 97 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0098 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 161) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 161)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 98)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 98) = g32p_row28_cosetExponents0 98 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0099 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 162) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 162)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 99)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 99) = g32p_row28_cosetExponents0 99 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0100 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 163) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 163)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 100)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 100) = g32p_row28_cosetExponents0 100 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0101 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 165) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 165)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 101)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 101) = g32p_row28_cosetExponents0 101 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0102 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 167) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 167)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 102)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 102) = g32p_row28_cosetExponents0 102 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0103 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 176) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 176)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 103)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 103) = g32p_row28_cosetExponents0 103 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0104 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 179) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 179)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 104)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 104) = g32p_row28_cosetExponents0 104 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0105 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 180) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 180)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 105)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 105) = g32p_row28_cosetExponents0 105 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0106 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 185) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 185)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 106)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 106) = g32p_row28_cosetExponents0 106 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0107 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 191) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 191)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 107)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 107) = g32p_row28_cosetExponents0 107 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0108 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 195) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 195)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 108)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 108) = g32p_row28_cosetExponents0 108 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0109 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 199) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 199)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 109)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 109) = g32p_row28_cosetExponents0 109 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0110 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 203) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 203)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 110)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 110) = g32p_row28_cosetExponents0 110 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0111 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 204) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 204)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 111)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 111) = g32p_row28_cosetExponents0 111 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock0_0006 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 (g32p_finBlockIndex 128 6 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 6 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 6 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 6 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 6 r)) = g32p_row28_cosetExponents0 (g32p_finBlockIndex 128 6 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_0_0096
  · exact g32p_row28_cosetMonodromy_0_0097
  · exact g32p_row28_cosetMonodromy_0_0098
  · exact g32p_row28_cosetMonodromy_0_0099
  · exact g32p_row28_cosetMonodromy_0_0100
  · exact g32p_row28_cosetMonodromy_0_0101
  · exact g32p_row28_cosetMonodromy_0_0102
  · exact g32p_row28_cosetMonodromy_0_0103
  · exact g32p_row28_cosetMonodromy_0_0104
  · exact g32p_row28_cosetMonodromy_0_0105
  · exact g32p_row28_cosetMonodromy_0_0106
  · exact g32p_row28_cosetMonodromy_0_0107
  · exact g32p_row28_cosetMonodromy_0_0108
  · exact g32p_row28_cosetMonodromy_0_0109
  · exact g32p_row28_cosetMonodromy_0_0110
  · exact g32p_row28_cosetMonodromy_0_0111


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_0_0112 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 207) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 207)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 112)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 112) = g32p_row28_cosetExponents0 112 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0113 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 208) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 208)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 113)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 113) = g32p_row28_cosetExponents0 113 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0114 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 212) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 212)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 114)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 114) = g32p_row28_cosetExponents0 114 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0115 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 215) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 215)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 115)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 115) = g32p_row28_cosetExponents0 115 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0116 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 216) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 216)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 116)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 116) = g32p_row28_cosetExponents0 116 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0117 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 222) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 222)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 117)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 117) = g32p_row28_cosetExponents0 117 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0118 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 233) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 233)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 118)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 118) = g32p_row28_cosetExponents0 118 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0119 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 237) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 237)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 119)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 119) = g32p_row28_cosetExponents0 119 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0120 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 250) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 250)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 120)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 120) = g32p_row28_cosetExponents0 120 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0121 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 253) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 253)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 121)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 121) = g32p_row28_cosetExponents0 121 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0122 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 255) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 255)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 122)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 122) = g32p_row28_cosetExponents0 122 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0123 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 275) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 275)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 123)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 123) = g32p_row28_cosetExponents0 123 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0124 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 281) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 281)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 124)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 124) = g32p_row28_cosetExponents0 124 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0125 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 283) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 283)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 125)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 125) = g32p_row28_cosetExponents0 125 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0126 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 284) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 284)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 126)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 126) = g32p_row28_cosetExponents0 126 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_0_0127 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 286) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 286)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 127)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 127) = g32p_row28_cosetExponents0 127 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock0_0007 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 0) (g32p_row28_cosetLengths0 (g32p_finBlockIndex 128 7 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 7 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots0 (g32p_finBlockIndex 128 7 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 7 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies0 (g32p_finBlockIndex 128 7 r)) = g32p_row28_cosetExponents0 (g32p_finBlockIndex 128 7 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_0_0112
  · exact g32p_row28_cosetMonodromy_0_0113
  · exact g32p_row28_cosetMonodromy_0_0114
  · exact g32p_row28_cosetMonodromy_0_0115
  · exact g32p_row28_cosetMonodromy_0_0116
  · exact g32p_row28_cosetMonodromy_0_0117
  · exact g32p_row28_cosetMonodromy_0_0118
  · exact g32p_row28_cosetMonodromy_0_0119
  · exact g32p_row28_cosetMonodromy_0_0120
  · exact g32p_row28_cosetMonodromy_0_0121
  · exact g32p_row28_cosetMonodromy_0_0122
  · exact g32p_row28_cosetMonodromy_0_0123
  · exact g32p_row28_cosetMonodromy_0_0124
  · exact g32p_row28_cosetMonodromy_0_0125
  · exact g32p_row28_cosetMonodromy_0_0126
  · exact g32p_row28_cosetMonodromy_0_0127


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_1_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 0)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 0)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 0) = g32p_row28_cosetExponents1 0 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 1)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 1)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 1) = g32p_row28_cosetExponents1 1 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 2)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 2)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 2) = g32p_row28_cosetExponents1 2 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 3)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 3)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 3) = g32p_row28_cosetExponents1 3 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 4)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 4)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 4) = g32p_row28_cosetExponents1 4 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 5)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 5)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 5) = g32p_row28_cosetExponents1 5 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 7)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 6)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 6) = g32p_row28_cosetExponents1 6 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 8)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 7)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 7) = g32p_row28_cosetExponents1 7 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 9)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 8)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 8) = g32p_row28_cosetExponents1 8 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 10)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 9)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 9) = g32p_row28_cosetExponents1 9 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 11)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 10)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 10) = g32p_row28_cosetExponents1 10 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 12)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 11)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 11) = g32p_row28_cosetExponents1 11 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 13)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 12)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 12) = g32p_row28_cosetExponents1 12 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 14)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 13)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 13) = g32p_row28_cosetExponents1 13 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 16)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 14)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 14) = g32p_row28_cosetExponents1 14 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 17)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 15)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 15) = g32p_row28_cosetExponents1 15 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock1_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 1) (g32p_row28_cosetLengths1 (g32p_finBlockIndex 128 0 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 (g32p_finBlockIndex 128 0 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 (g32p_finBlockIndex 128 0 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 (g32p_finBlockIndex 128 0 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 (g32p_finBlockIndex 128 0 r)) = g32p_row28_cosetExponents1 (g32p_finBlockIndex 128 0 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_1_0000
  · exact g32p_row28_cosetMonodromy_1_0001
  · exact g32p_row28_cosetMonodromy_1_0002
  · exact g32p_row28_cosetMonodromy_1_0003
  · exact g32p_row28_cosetMonodromy_1_0004
  · exact g32p_row28_cosetMonodromy_1_0005
  · exact g32p_row28_cosetMonodromy_1_0006
  · exact g32p_row28_cosetMonodromy_1_0007
  · exact g32p_row28_cosetMonodromy_1_0008
  · exact g32p_row28_cosetMonodromy_1_0009
  · exact g32p_row28_cosetMonodromy_1_0010
  · exact g32p_row28_cosetMonodromy_1_0011
  · exact g32p_row28_cosetMonodromy_1_0012
  · exact g32p_row28_cosetMonodromy_1_0013
  · exact g32p_row28_cosetMonodromy_1_0014
  · exact g32p_row28_cosetMonodromy_1_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_1_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 18)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 16)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 16) = g32p_row28_cosetExponents1 16 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 21)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 17)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 17) = g32p_row28_cosetExponents1 17 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 23)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 18)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 18) = g32p_row28_cosetExponents1 18 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 24)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 19)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 19) = g32p_row28_cosetExponents1 19 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 25)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 20)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 20) = g32p_row28_cosetExponents1 20 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 28)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 21)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 21) = g32p_row28_cosetExponents1 21 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 29)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 22)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 22) = g32p_row28_cosetExponents1 22 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 30)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 23)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 23) = g32p_row28_cosetExponents1 23 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 31)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 24)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 24) = g32p_row28_cosetExponents1 24 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 32)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 25)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 25) = g32p_row28_cosetExponents1 25 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 33)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 26)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 26) = g32p_row28_cosetExponents1 26 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 36)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 27)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 27) = g32p_row28_cosetExponents1 27 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 37)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 28)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 28) = g32p_row28_cosetExponents1 28 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 39)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 29)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 29) = g32p_row28_cosetExponents1 29 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 40)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 30)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 30) = g32p_row28_cosetExponents1 30 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 41)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 31)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 31) = g32p_row28_cosetExponents1 31 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock1_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 1) (g32p_row28_cosetLengths1 (g32p_finBlockIndex 128 1 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 (g32p_finBlockIndex 128 1 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 (g32p_finBlockIndex 128 1 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 (g32p_finBlockIndex 128 1 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 (g32p_finBlockIndex 128 1 r)) = g32p_row28_cosetExponents1 (g32p_finBlockIndex 128 1 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_1_0016
  · exact g32p_row28_cosetMonodromy_1_0017
  · exact g32p_row28_cosetMonodromy_1_0018
  · exact g32p_row28_cosetMonodromy_1_0019
  · exact g32p_row28_cosetMonodromy_1_0020
  · exact g32p_row28_cosetMonodromy_1_0021
  · exact g32p_row28_cosetMonodromy_1_0022
  · exact g32p_row28_cosetMonodromy_1_0023
  · exact g32p_row28_cosetMonodromy_1_0024
  · exact g32p_row28_cosetMonodromy_1_0025
  · exact g32p_row28_cosetMonodromy_1_0026
  · exact g32p_row28_cosetMonodromy_1_0027
  · exact g32p_row28_cosetMonodromy_1_0028
  · exact g32p_row28_cosetMonodromy_1_0029
  · exact g32p_row28_cosetMonodromy_1_0030
  · exact g32p_row28_cosetMonodromy_1_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row28_cosetMonodromy_1_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 44)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 32)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 32) = g32p_row28_cosetExponents1 32 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 45)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 33)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 33) = g32p_row28_cosetExponents1 33 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 48)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 34)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 34) = g32p_row28_cosetExponents1 34 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 49)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 35)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 35) = g32p_row28_cosetExponents1 35 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 55)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 36)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 36) = g32p_row28_cosetExponents1 36 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 56)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 37)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 37) = g32p_row28_cosetExponents1 37 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 58)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 38)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 38) = g32p_row28_cosetExponents1 38 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 59)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 39)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 39) = g32p_row28_cosetExponents1 39 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 61)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 40)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 40) = g32p_row28_cosetExponents1 40 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 63)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 41)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 41) = g32p_row28_cosetExponents1 41 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 64)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 42)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 42) = g32p_row28_cosetExponents1 42 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 66)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 43)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 43) = g32p_row28_cosetExponents1 43 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 68)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 44)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 44) = g32p_row28_cosetExponents1 44 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 69)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 45)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 45) = g32p_row28_cosetExponents1 45 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)))) (g32p_row28_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 72)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 46)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 46) = g32p_row28_cosetExponents1 46 := by
  decide +kernel

theorem g32p_row28_cosetMonodromy_1_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row28_cosetBranchMatrices 1) (HurwitzPrymRex_mone)) (g32p_row28_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives 74)
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 47)) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 47) = g32p_row28_cosetExponents1 47 := by
  decide +kernel

theorem g32p_row28_cosetMonodromyBlock1_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row28_cosetBranchMatrices 1) (g32p_row28_cosetLengths1 (g32p_finBlockIndex 128 2 r)))
      (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 (g32p_finBlockIndex 128 2 r))) =
      HurwitzPrymRex_mmul (g32p_row28_cosetRepresentatives (g32p_row28_cosetRoots1 (g32p_finBlockIndex 128 2 r)))
        (g32p_row09_groupNodes (g32p_row28_cosetMonodromies1 (g32p_finBlockIndex 128 2 r))) ∧
    g32p_row28_characterValues (g32p_row28_cosetMonodromies1 (g32p_finBlockIndex 128 2 r)) = g32p_row28_cosetExponents1 (g32p_finBlockIndex 128 2 r) := by
  fin_cases r
  · exact g32p_row28_cosetMonodromy_1_0032
  · exact g32p_row28_cosetMonodromy_1_0033
  · exact g32p_row28_cosetMonodromy_1_0034
  · exact g32p_row28_cosetMonodromy_1_0035
  · exact g32p_row28_cosetMonodromy_1_0036
  · exact g32p_row28_cosetMonodromy_1_0037
  · exact g32p_row28_cosetMonodromy_1_0038
  · exact g32p_row28_cosetMonodromy_1_0039
  · exact g32p_row28_cosetMonodromy_1_0040
  · exact g32p_row28_cosetMonodromy_1_0041
  · exact g32p_row28_cosetMonodromy_1_0042
  · exact g32p_row28_cosetMonodromy_1_0043
  · exact g32p_row28_cosetMonodromy_1_0044
  · exact g32p_row28_cosetMonodromy_1_0045
  · exact g32p_row28_cosetMonodromy_1_0046
  · exact g32p_row28_cosetMonodromy_1_0047


end HodgeLean.Foundations.Program

end
