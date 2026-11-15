import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0959

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0256 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 256) = g32p_row40_cosetRepresentatives 256 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 256) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 256))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 256)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 256) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 256))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 256)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0257 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 257) = g32p_row40_cosetRepresentatives 257 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 257))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 257)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 257))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 257)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0258 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 258) = g32p_row40_cosetRepresentatives 258 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 258) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 258))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 258)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 258) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 258))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 258)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0259 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 259) = g32p_row40_cosetRepresentatives 259 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 259) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 259))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 259)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 259) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 259))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 259)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0260 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 260) = g32p_row40_cosetRepresentatives 260 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 260) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 260))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 260)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 260) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 260))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 260)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0261 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 261) = g32p_row40_cosetRepresentatives 261 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 261) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 261))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 261)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 261) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 261))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 261)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0262 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 262) = g32p_row40_cosetRepresentatives 262 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 262) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 262))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 262)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 262) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 262))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 262)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0263 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 263) = g32p_row40_cosetRepresentatives 263 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 263) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 263))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 263)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 263) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 263))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 263)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0264 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 264) = g32p_row40_cosetRepresentatives 264 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 264) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 264))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 264)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 264) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 264))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 264)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0265 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 265) = g32p_row40_cosetRepresentatives 265 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 265) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 265))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 265)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 265) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 265))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 265)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0266 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 266) = g32p_row40_cosetRepresentatives 266 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 266) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 266))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 266)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 266) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 266))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 266)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0267 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 267) = g32p_row40_cosetRepresentatives 267 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 267) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 267))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 267)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 267) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 267))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 267)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0268 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 268) = g32p_row40_cosetRepresentatives 268 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 268))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 268)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 268))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 268)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0269 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 269) = g32p_row40_cosetRepresentatives 269 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 269) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 269))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 269)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 269) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 269))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 269)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0270 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 270) = g32p_row40_cosetRepresentatives 270 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 270) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 270))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 270)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 270) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 270))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 270)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0271 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 271) = g32p_row40_cosetRepresentatives 271 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 271) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 271))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 271)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 271) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 271))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 271)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0016 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 16 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 16 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0256
  · exact g32p_row40_cosetWord_0257
  · exact g32p_row40_cosetWord_0258
  · exact g32p_row40_cosetWord_0259
  · exact g32p_row40_cosetWord_0260
  · exact g32p_row40_cosetWord_0261
  · exact g32p_row40_cosetWord_0262
  · exact g32p_row40_cosetWord_0263
  · exact g32p_row40_cosetWord_0264
  · exact g32p_row40_cosetWord_0265
  · exact g32p_row40_cosetWord_0266
  · exact g32p_row40_cosetWord_0267
  · exact g32p_row40_cosetWord_0268
  · exact g32p_row40_cosetWord_0269
  · exact g32p_row40_cosetWord_0270
  · exact g32p_row40_cosetWord_0271

theorem g32p_row40_cosetGeneratorBlock_0016 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 16 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 16 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 16 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0256 s
  · exact g32p_row40_cosetGeneratorStep_0257 s
  · exact g32p_row40_cosetGeneratorStep_0258 s
  · exact g32p_row40_cosetGeneratorStep_0259 s
  · exact g32p_row40_cosetGeneratorStep_0260 s
  · exact g32p_row40_cosetGeneratorStep_0261 s
  · exact g32p_row40_cosetGeneratorStep_0262 s
  · exact g32p_row40_cosetGeneratorStep_0263 s
  · exact g32p_row40_cosetGeneratorStep_0264 s
  · exact g32p_row40_cosetGeneratorStep_0265 s
  · exact g32p_row40_cosetGeneratorStep_0266 s
  · exact g32p_row40_cosetGeneratorStep_0267 s
  · exact g32p_row40_cosetGeneratorStep_0268 s
  · exact g32p_row40_cosetGeneratorStep_0269 s
  · exact g32p_row40_cosetGeneratorStep_0270 s
  · exact g32p_row40_cosetGeneratorStep_0271 s

theorem g32p_row40_cosetBranchBlock_0016 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 16 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 16 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 16 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0256 s
  · exact g32p_row40_cosetBranchStep_0257 s
  · exact g32p_row40_cosetBranchStep_0258 s
  · exact g32p_row40_cosetBranchStep_0259 s
  · exact g32p_row40_cosetBranchStep_0260 s
  · exact g32p_row40_cosetBranchStep_0261 s
  · exact g32p_row40_cosetBranchStep_0262 s
  · exact g32p_row40_cosetBranchStep_0263 s
  · exact g32p_row40_cosetBranchStep_0264 s
  · exact g32p_row40_cosetBranchStep_0265 s
  · exact g32p_row40_cosetBranchStep_0266 s
  · exact g32p_row40_cosetBranchStep_0267 s
  · exact g32p_row40_cosetBranchStep_0268 s
  · exact g32p_row40_cosetBranchStep_0269 s
  · exact g32p_row40_cosetBranchStep_0270 s
  · exact g32p_row40_cosetBranchStep_0271 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0272 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 272) = g32p_row40_cosetRepresentatives 272 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 272) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 272))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 272)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 272) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 272))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 272)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0273 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 273) = g32p_row40_cosetRepresentatives 273 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 273) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 273))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 273)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 273) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 273))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 273)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0274 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 274) = g32p_row40_cosetRepresentatives 274 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 274) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 274))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 274)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 274) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 274))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 274)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0275 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 275) = g32p_row40_cosetRepresentatives 275 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 275) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 275))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 275)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 275) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 275))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 275)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0276 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 276) = g32p_row40_cosetRepresentatives 276 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 276) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 276))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 276)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 276) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 276))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 276)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0277 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 277) = g32p_row40_cosetRepresentatives 277 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 277) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 277))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 277)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 277) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 277))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 277)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0278 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 278) = g32p_row40_cosetRepresentatives 278 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 278) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 278))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 278)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 278) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 278))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 278)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0279 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 279) = g32p_row40_cosetRepresentatives 279 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 279) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 279))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 279)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 279) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 279))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 279)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0280 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 280) = g32p_row40_cosetRepresentatives 280 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 280) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 280))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 280)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 280) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 280))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 280)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0281 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 281) = g32p_row40_cosetRepresentatives 281 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 281) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 281))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 281)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 281) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 281))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 281)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0282 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 282) = g32p_row40_cosetRepresentatives 282 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 282) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 282))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 282)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 282) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 282))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 282)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0283 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 283) = g32p_row40_cosetRepresentatives 283 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 283) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 283))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 283)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 283) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 283))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 283)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0284 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 284) = g32p_row40_cosetRepresentatives 284 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 284) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 284))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 284)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 284) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 284))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 284)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0285 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 285) = g32p_row40_cosetRepresentatives 285 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 285) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 285))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 285)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 285) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 285))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 285)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0286 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 286) = g32p_row40_cosetRepresentatives 286 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 286) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 286))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 286)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 286) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 286))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 286)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0287 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 287) = g32p_row40_cosetRepresentatives 287 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 287) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 287))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 287)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 287) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 287))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 287)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0017 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 17 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 17 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0272
  · exact g32p_row40_cosetWord_0273
  · exact g32p_row40_cosetWord_0274
  · exact g32p_row40_cosetWord_0275
  · exact g32p_row40_cosetWord_0276
  · exact g32p_row40_cosetWord_0277
  · exact g32p_row40_cosetWord_0278
  · exact g32p_row40_cosetWord_0279
  · exact g32p_row40_cosetWord_0280
  · exact g32p_row40_cosetWord_0281
  · exact g32p_row40_cosetWord_0282
  · exact g32p_row40_cosetWord_0283
  · exact g32p_row40_cosetWord_0284
  · exact g32p_row40_cosetWord_0285
  · exact g32p_row40_cosetWord_0286
  · exact g32p_row40_cosetWord_0287

theorem g32p_row40_cosetGeneratorBlock_0017 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 17 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 17 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 17 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0272 s
  · exact g32p_row40_cosetGeneratorStep_0273 s
  · exact g32p_row40_cosetGeneratorStep_0274 s
  · exact g32p_row40_cosetGeneratorStep_0275 s
  · exact g32p_row40_cosetGeneratorStep_0276 s
  · exact g32p_row40_cosetGeneratorStep_0277 s
  · exact g32p_row40_cosetGeneratorStep_0278 s
  · exact g32p_row40_cosetGeneratorStep_0279 s
  · exact g32p_row40_cosetGeneratorStep_0280 s
  · exact g32p_row40_cosetGeneratorStep_0281 s
  · exact g32p_row40_cosetGeneratorStep_0282 s
  · exact g32p_row40_cosetGeneratorStep_0283 s
  · exact g32p_row40_cosetGeneratorStep_0284 s
  · exact g32p_row40_cosetGeneratorStep_0285 s
  · exact g32p_row40_cosetGeneratorStep_0286 s
  · exact g32p_row40_cosetGeneratorStep_0287 s

theorem g32p_row40_cosetBranchBlock_0017 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 17 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 17 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 17 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0272 s
  · exact g32p_row40_cosetBranchStep_0273 s
  · exact g32p_row40_cosetBranchStep_0274 s
  · exact g32p_row40_cosetBranchStep_0275 s
  · exact g32p_row40_cosetBranchStep_0276 s
  · exact g32p_row40_cosetBranchStep_0277 s
  · exact g32p_row40_cosetBranchStep_0278 s
  · exact g32p_row40_cosetBranchStep_0279 s
  · exact g32p_row40_cosetBranchStep_0280 s
  · exact g32p_row40_cosetBranchStep_0281 s
  · exact g32p_row40_cosetBranchStep_0282 s
  · exact g32p_row40_cosetBranchStep_0283 s
  · exact g32p_row40_cosetBranchStep_0284 s
  · exact g32p_row40_cosetBranchStep_0285 s
  · exact g32p_row40_cosetBranchStep_0286 s
  · exact g32p_row40_cosetBranchStep_0287 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0288 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 288) = g32p_row40_cosetRepresentatives 288 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 288) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 288))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 288)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 288) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 288))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 288)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0289 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 289) = g32p_row40_cosetRepresentatives 289 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 289) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 289))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 289)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 289) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 289))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 289)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0290 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 290) = g32p_row40_cosetRepresentatives 290 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 290) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 290))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 290)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 290) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 290))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 290)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0291 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 291) = g32p_row40_cosetRepresentatives 291 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 291) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 291))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 291)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 291) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 291))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 291)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0292 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 292) = g32p_row40_cosetRepresentatives 292 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 292) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 292))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 292)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 292) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 292))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 292)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0293 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 293) = g32p_row40_cosetRepresentatives 293 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 293) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 293))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 293)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 293) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 293))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 293)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0294 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 294) = g32p_row40_cosetRepresentatives 294 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 294) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 294))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 294)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 294) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 294))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 294)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0295 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 295) = g32p_row40_cosetRepresentatives 295 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 295) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 295))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 295)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 295) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 295))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 295)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0296 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 296) = g32p_row40_cosetRepresentatives 296 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 296) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 296))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 296)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 296) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 296))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 296)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0297 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 297) = g32p_row40_cosetRepresentatives 297 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 297) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 297))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 297)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 297) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 297))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 297)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0298 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 298) = g32p_row40_cosetRepresentatives 298 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 298) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 298))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 298)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 298) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 298))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 298)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0299 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 299) = g32p_row40_cosetRepresentatives 299 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 299) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 299))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 299)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 299) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 299))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 299)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0300 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 300) = g32p_row40_cosetRepresentatives 300 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 300) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 300))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 300)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 300) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 300))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 300)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0301 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 301) = g32p_row40_cosetRepresentatives 301 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 301) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 301))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 301)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 301) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 301))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 301)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0302 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 302) = g32p_row40_cosetRepresentatives 302 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 302) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 302))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 302)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 302) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 302))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 302)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0303 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 303) = g32p_row40_cosetRepresentatives 303 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 303) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 303))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 303)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 303) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 303))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 303)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0018 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 18 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 18 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0288
  · exact g32p_row40_cosetWord_0289
  · exact g32p_row40_cosetWord_0290
  · exact g32p_row40_cosetWord_0291
  · exact g32p_row40_cosetWord_0292
  · exact g32p_row40_cosetWord_0293
  · exact g32p_row40_cosetWord_0294
  · exact g32p_row40_cosetWord_0295
  · exact g32p_row40_cosetWord_0296
  · exact g32p_row40_cosetWord_0297
  · exact g32p_row40_cosetWord_0298
  · exact g32p_row40_cosetWord_0299
  · exact g32p_row40_cosetWord_0300
  · exact g32p_row40_cosetWord_0301
  · exact g32p_row40_cosetWord_0302
  · exact g32p_row40_cosetWord_0303

theorem g32p_row40_cosetGeneratorBlock_0018 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 18 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 18 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 18 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0288 s
  · exact g32p_row40_cosetGeneratorStep_0289 s
  · exact g32p_row40_cosetGeneratorStep_0290 s
  · exact g32p_row40_cosetGeneratorStep_0291 s
  · exact g32p_row40_cosetGeneratorStep_0292 s
  · exact g32p_row40_cosetGeneratorStep_0293 s
  · exact g32p_row40_cosetGeneratorStep_0294 s
  · exact g32p_row40_cosetGeneratorStep_0295 s
  · exact g32p_row40_cosetGeneratorStep_0296 s
  · exact g32p_row40_cosetGeneratorStep_0297 s
  · exact g32p_row40_cosetGeneratorStep_0298 s
  · exact g32p_row40_cosetGeneratorStep_0299 s
  · exact g32p_row40_cosetGeneratorStep_0300 s
  · exact g32p_row40_cosetGeneratorStep_0301 s
  · exact g32p_row40_cosetGeneratorStep_0302 s
  · exact g32p_row40_cosetGeneratorStep_0303 s

theorem g32p_row40_cosetBranchBlock_0018 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 18 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 18 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 18 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0288 s
  · exact g32p_row40_cosetBranchStep_0289 s
  · exact g32p_row40_cosetBranchStep_0290 s
  · exact g32p_row40_cosetBranchStep_0291 s
  · exact g32p_row40_cosetBranchStep_0292 s
  · exact g32p_row40_cosetBranchStep_0293 s
  · exact g32p_row40_cosetBranchStep_0294 s
  · exact g32p_row40_cosetBranchStep_0295 s
  · exact g32p_row40_cosetBranchStep_0296 s
  · exact g32p_row40_cosetBranchStep_0297 s
  · exact g32p_row40_cosetBranchStep_0298 s
  · exact g32p_row40_cosetBranchStep_0299 s
  · exact g32p_row40_cosetBranchStep_0300 s
  · exact g32p_row40_cosetBranchStep_0301 s
  · exact g32p_row40_cosetBranchStep_0302 s
  · exact g32p_row40_cosetBranchStep_0303 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0304 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 304) = g32p_row40_cosetRepresentatives 304 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 304) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 304))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 304)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 304) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 304))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 304)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0305 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 305) = g32p_row40_cosetRepresentatives 305 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 305) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 305))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 305)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 305) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 305))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 305)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0306 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 306) = g32p_row40_cosetRepresentatives 306 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 306) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 306))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 306)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 306) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 306))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 306)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0307 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 307) = g32p_row40_cosetRepresentatives 307 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 307) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 307))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 307)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 307) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 307))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 307)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0308 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 308) = g32p_row40_cosetRepresentatives 308 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 308) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 308))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 308)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 308) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 308))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 308)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0309 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 309) = g32p_row40_cosetRepresentatives 309 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 309) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 309))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 309)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 309) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 309))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 309)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0310 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 310) = g32p_row40_cosetRepresentatives 310 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 310) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 310))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 310)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 310) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 310))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 310)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0311 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 311) = g32p_row40_cosetRepresentatives 311 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 311) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 311))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 311)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 311) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 311))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 311)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0312 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 312) = g32p_row40_cosetRepresentatives 312 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 312) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 312))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 312)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 312) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 312))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 312)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0313 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 313) = g32p_row40_cosetRepresentatives 313 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 313) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 313))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 313)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 313) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 313))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 313)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0314 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 314) = g32p_row40_cosetRepresentatives 314 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 314) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 314))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 314)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 314) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 314))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 314)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0315 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 315) = g32p_row40_cosetRepresentatives 315 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 315) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 315))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 315)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 315) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 315))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 315)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0316 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 316) = g32p_row40_cosetRepresentatives 316 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 316) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 316))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 316)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 316) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 316))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 316)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0317 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 317) = g32p_row40_cosetRepresentatives 317 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 317) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 317))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 317)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 317) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 317))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 317)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0318 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 318) = g32p_row40_cosetRepresentatives 318 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 318) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 318))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 318)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 318) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 318))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 318)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0319 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 319) = g32p_row40_cosetRepresentatives 319 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 319) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 319))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 319)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 319) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 319))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 319)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0019 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 19 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 19 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0304
  · exact g32p_row40_cosetWord_0305
  · exact g32p_row40_cosetWord_0306
  · exact g32p_row40_cosetWord_0307
  · exact g32p_row40_cosetWord_0308
  · exact g32p_row40_cosetWord_0309
  · exact g32p_row40_cosetWord_0310
  · exact g32p_row40_cosetWord_0311
  · exact g32p_row40_cosetWord_0312
  · exact g32p_row40_cosetWord_0313
  · exact g32p_row40_cosetWord_0314
  · exact g32p_row40_cosetWord_0315
  · exact g32p_row40_cosetWord_0316
  · exact g32p_row40_cosetWord_0317
  · exact g32p_row40_cosetWord_0318
  · exact g32p_row40_cosetWord_0319

theorem g32p_row40_cosetGeneratorBlock_0019 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 19 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 19 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 19 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0304 s
  · exact g32p_row40_cosetGeneratorStep_0305 s
  · exact g32p_row40_cosetGeneratorStep_0306 s
  · exact g32p_row40_cosetGeneratorStep_0307 s
  · exact g32p_row40_cosetGeneratorStep_0308 s
  · exact g32p_row40_cosetGeneratorStep_0309 s
  · exact g32p_row40_cosetGeneratorStep_0310 s
  · exact g32p_row40_cosetGeneratorStep_0311 s
  · exact g32p_row40_cosetGeneratorStep_0312 s
  · exact g32p_row40_cosetGeneratorStep_0313 s
  · exact g32p_row40_cosetGeneratorStep_0314 s
  · exact g32p_row40_cosetGeneratorStep_0315 s
  · exact g32p_row40_cosetGeneratorStep_0316 s
  · exact g32p_row40_cosetGeneratorStep_0317 s
  · exact g32p_row40_cosetGeneratorStep_0318 s
  · exact g32p_row40_cosetGeneratorStep_0319 s

theorem g32p_row40_cosetBranchBlock_0019 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 19 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 19 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 19 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0304 s
  · exact g32p_row40_cosetBranchStep_0305 s
  · exact g32p_row40_cosetBranchStep_0306 s
  · exact g32p_row40_cosetBranchStep_0307 s
  · exact g32p_row40_cosetBranchStep_0308 s
  · exact g32p_row40_cosetBranchStep_0309 s
  · exact g32p_row40_cosetBranchStep_0310 s
  · exact g32p_row40_cosetBranchStep_0311 s
  · exact g32p_row40_cosetBranchStep_0312 s
  · exact g32p_row40_cosetBranchStep_0313 s
  · exact g32p_row40_cosetBranchStep_0314 s
  · exact g32p_row40_cosetBranchStep_0315 s
  · exact g32p_row40_cosetBranchStep_0316 s
  · exact g32p_row40_cosetBranchStep_0317 s
  · exact g32p_row40_cosetBranchStep_0318 s
  · exact g32p_row40_cosetBranchStep_0319 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0320 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 320) = g32p_row40_cosetRepresentatives 320 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 320) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 320))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 320)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 320) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 320))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 320)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0321 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 321) = g32p_row40_cosetRepresentatives 321 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 321) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 321))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 321)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 321) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 321))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 321)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0322 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 322) = g32p_row40_cosetRepresentatives 322 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 322) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 322))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 322)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 322) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 322))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 322)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0323 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 323) = g32p_row40_cosetRepresentatives 323 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 323) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 323))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 323)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 323) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 323))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 323)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0324 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 324) = g32p_row40_cosetRepresentatives 324 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 324) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 324))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 324)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 324) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 324))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 324)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0325 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 325) = g32p_row40_cosetRepresentatives 325 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 325) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 325))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 325)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 325) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 325))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 325)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0326 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 326) = g32p_row40_cosetRepresentatives 326 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 326) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 326))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 326)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 326) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 326))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 326)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0327 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 327) = g32p_row40_cosetRepresentatives 327 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 327) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 327))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 327)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 327) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 327))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 327)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0328 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 328) = g32p_row40_cosetRepresentatives 328 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0328 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 328) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 328))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 328)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0328 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 328) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 328))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 328)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0329 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 329) = g32p_row40_cosetRepresentatives 329 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0329 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 329) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 329))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 329)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0329 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 329) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 329))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 329)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0330 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 330) = g32p_row40_cosetRepresentatives 330 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0330 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 330) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 330))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 330)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0330 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 330) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 330))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 330)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0331 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 331) = g32p_row40_cosetRepresentatives 331 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0331 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 331) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 331))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 331)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0331 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 331) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 331))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 331)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0332 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 332) = g32p_row40_cosetRepresentatives 332 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0332 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 332) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 332))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 332)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0332 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 332) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 332))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 332)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0333 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 333) = g32p_row40_cosetRepresentatives 333 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0333 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 333) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 333))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 333)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0333 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 333) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 333))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 333)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0334 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 334) = g32p_row40_cosetRepresentatives 334 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0334 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 334) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 334))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 334)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0334 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 334) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 334))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 334)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0335 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 335) = g32p_row40_cosetRepresentatives 335 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0335 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 335) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 335))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 335)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0335 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 335) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 335))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 335)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0020 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 20 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 20 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0320
  · exact g32p_row40_cosetWord_0321
  · exact g32p_row40_cosetWord_0322
  · exact g32p_row40_cosetWord_0323
  · exact g32p_row40_cosetWord_0324
  · exact g32p_row40_cosetWord_0325
  · exact g32p_row40_cosetWord_0326
  · exact g32p_row40_cosetWord_0327
  · exact g32p_row40_cosetWord_0328
  · exact g32p_row40_cosetWord_0329
  · exact g32p_row40_cosetWord_0330
  · exact g32p_row40_cosetWord_0331
  · exact g32p_row40_cosetWord_0332
  · exact g32p_row40_cosetWord_0333
  · exact g32p_row40_cosetWord_0334
  · exact g32p_row40_cosetWord_0335

theorem g32p_row40_cosetGeneratorBlock_0020 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 20 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 20 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 20 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0320 s
  · exact g32p_row40_cosetGeneratorStep_0321 s
  · exact g32p_row40_cosetGeneratorStep_0322 s
  · exact g32p_row40_cosetGeneratorStep_0323 s
  · exact g32p_row40_cosetGeneratorStep_0324 s
  · exact g32p_row40_cosetGeneratorStep_0325 s
  · exact g32p_row40_cosetGeneratorStep_0326 s
  · exact g32p_row40_cosetGeneratorStep_0327 s
  · exact g32p_row40_cosetGeneratorStep_0328 s
  · exact g32p_row40_cosetGeneratorStep_0329 s
  · exact g32p_row40_cosetGeneratorStep_0330 s
  · exact g32p_row40_cosetGeneratorStep_0331 s
  · exact g32p_row40_cosetGeneratorStep_0332 s
  · exact g32p_row40_cosetGeneratorStep_0333 s
  · exact g32p_row40_cosetGeneratorStep_0334 s
  · exact g32p_row40_cosetGeneratorStep_0335 s

theorem g32p_row40_cosetBranchBlock_0020 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 20 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 20 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 20 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0320 s
  · exact g32p_row40_cosetBranchStep_0321 s
  · exact g32p_row40_cosetBranchStep_0322 s
  · exact g32p_row40_cosetBranchStep_0323 s
  · exact g32p_row40_cosetBranchStep_0324 s
  · exact g32p_row40_cosetBranchStep_0325 s
  · exact g32p_row40_cosetBranchStep_0326 s
  · exact g32p_row40_cosetBranchStep_0327 s
  · exact g32p_row40_cosetBranchStep_0328 s
  · exact g32p_row40_cosetBranchStep_0329 s
  · exact g32p_row40_cosetBranchStep_0330 s
  · exact g32p_row40_cosetBranchStep_0331 s
  · exact g32p_row40_cosetBranchStep_0332 s
  · exact g32p_row40_cosetBranchStep_0333 s
  · exact g32p_row40_cosetBranchStep_0334 s
  · exact g32p_row40_cosetBranchStep_0335 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0336 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 336) = g32p_row40_cosetRepresentatives 336 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0336 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 336) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 336))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 336)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0336 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 336) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 336))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 336)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0337 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 337) = g32p_row40_cosetRepresentatives 337 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0337 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 337) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 337))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 337)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0337 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 337) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 337))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 337)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0338 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 338) = g32p_row40_cosetRepresentatives 338 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0338 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 338) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 338))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 338)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0338 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 338) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 338))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 338)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0339 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 339) = g32p_row40_cosetRepresentatives 339 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0339 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 339) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 339))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 339)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0339 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 339) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 339))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 339)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0340 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 340) = g32p_row40_cosetRepresentatives 340 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0340 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 340) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 340))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 340)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0340 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 340) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 340))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 340)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0341 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 341) = g32p_row40_cosetRepresentatives 341 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0341 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 341) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 341))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 341)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0341 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 341) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 341))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 341)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0342 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 342) = g32p_row40_cosetRepresentatives 342 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0342 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 342) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 342))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 342)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0342 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 342) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 342))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 342)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0343 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 343) = g32p_row40_cosetRepresentatives 343 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0343 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 343) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 343))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 343)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0343 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 343) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 343))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 343)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0344 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 344) = g32p_row40_cosetRepresentatives 344 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0344 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 344) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 344))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 344)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0344 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 344) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 344))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 344)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0345 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 345) = g32p_row40_cosetRepresentatives 345 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0345 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 345) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 345))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 345)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0345 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 345) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 345))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 345)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0346 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 346) = g32p_row40_cosetRepresentatives 346 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0346 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 346) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 346))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 346)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0346 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 346) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 346))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 346)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0347 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 347) = g32p_row40_cosetRepresentatives 347 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0347 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 347) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 347))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 347)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0347 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 347) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 347))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 347)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0348 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 348) = g32p_row40_cosetRepresentatives 348 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0348 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 348) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 348))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 348)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0348 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 348) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 348))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 348)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0349 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 349) = g32p_row40_cosetRepresentatives 349 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0349 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 349) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 349))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 349)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0349 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 349) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 349))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 349)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0350 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 350) = g32p_row40_cosetRepresentatives 350 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0350 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 350) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 350))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 350)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0350 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 350) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 350))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 350)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0351 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 351) = g32p_row40_cosetRepresentatives 351 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0351 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 351) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 351))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 351)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0351 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 351) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 351))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 351)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0021 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 21 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 21 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0336
  · exact g32p_row40_cosetWord_0337
  · exact g32p_row40_cosetWord_0338
  · exact g32p_row40_cosetWord_0339
  · exact g32p_row40_cosetWord_0340
  · exact g32p_row40_cosetWord_0341
  · exact g32p_row40_cosetWord_0342
  · exact g32p_row40_cosetWord_0343
  · exact g32p_row40_cosetWord_0344
  · exact g32p_row40_cosetWord_0345
  · exact g32p_row40_cosetWord_0346
  · exact g32p_row40_cosetWord_0347
  · exact g32p_row40_cosetWord_0348
  · exact g32p_row40_cosetWord_0349
  · exact g32p_row40_cosetWord_0350
  · exact g32p_row40_cosetWord_0351

theorem g32p_row40_cosetGeneratorBlock_0021 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 21 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 21 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 21 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0336 s
  · exact g32p_row40_cosetGeneratorStep_0337 s
  · exact g32p_row40_cosetGeneratorStep_0338 s
  · exact g32p_row40_cosetGeneratorStep_0339 s
  · exact g32p_row40_cosetGeneratorStep_0340 s
  · exact g32p_row40_cosetGeneratorStep_0341 s
  · exact g32p_row40_cosetGeneratorStep_0342 s
  · exact g32p_row40_cosetGeneratorStep_0343 s
  · exact g32p_row40_cosetGeneratorStep_0344 s
  · exact g32p_row40_cosetGeneratorStep_0345 s
  · exact g32p_row40_cosetGeneratorStep_0346 s
  · exact g32p_row40_cosetGeneratorStep_0347 s
  · exact g32p_row40_cosetGeneratorStep_0348 s
  · exact g32p_row40_cosetGeneratorStep_0349 s
  · exact g32p_row40_cosetGeneratorStep_0350 s
  · exact g32p_row40_cosetGeneratorStep_0351 s

theorem g32p_row40_cosetBranchBlock_0021 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 21 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 21 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 21 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0336 s
  · exact g32p_row40_cosetBranchStep_0337 s
  · exact g32p_row40_cosetBranchStep_0338 s
  · exact g32p_row40_cosetBranchStep_0339 s
  · exact g32p_row40_cosetBranchStep_0340 s
  · exact g32p_row40_cosetBranchStep_0341 s
  · exact g32p_row40_cosetBranchStep_0342 s
  · exact g32p_row40_cosetBranchStep_0343 s
  · exact g32p_row40_cosetBranchStep_0344 s
  · exact g32p_row40_cosetBranchStep_0345 s
  · exact g32p_row40_cosetBranchStep_0346 s
  · exact g32p_row40_cosetBranchStep_0347 s
  · exact g32p_row40_cosetBranchStep_0348 s
  · exact g32p_row40_cosetBranchStep_0349 s
  · exact g32p_row40_cosetBranchStep_0350 s
  · exact g32p_row40_cosetBranchStep_0351 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0352 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 352) = g32p_row40_cosetRepresentatives 352 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0352 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 352) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 352))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 352)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0352 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 352) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 352))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 352)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0353 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 353) = g32p_row40_cosetRepresentatives 353 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0353 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 353) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 353))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 353)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0353 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 353) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 353))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 353)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0354 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 354) = g32p_row40_cosetRepresentatives 354 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0354 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 354) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 354))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 354)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0354 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 354) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 354))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 354)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0355 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 355) = g32p_row40_cosetRepresentatives 355 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0355 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 355) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 355))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 355)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0355 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 355) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 355))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 355)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0356 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 356) = g32p_row40_cosetRepresentatives 356 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0356 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 356) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 356))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 356)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0356 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 356) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 356))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 356)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0357 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 357) = g32p_row40_cosetRepresentatives 357 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0357 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 357) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 357))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 357)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0357 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 357) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 357))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 357)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0358 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 358) = g32p_row40_cosetRepresentatives 358 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0358 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 358) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 358))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 358)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0358 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 358) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 358))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 358)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0359 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 359) = g32p_row40_cosetRepresentatives 359 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0359 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 359) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 359))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 359)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0359 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 359) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 359))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 359)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0360 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 360) = g32p_row40_cosetRepresentatives 360 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0360 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 360) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 360))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 360)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0360 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 360) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 360))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 360)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0361 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 361) = g32p_row40_cosetRepresentatives 361 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0361 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 361) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 361))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 361)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0361 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 361) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 361))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 361)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0362 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 362) = g32p_row40_cosetRepresentatives 362 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0362 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 362) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 362))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 362)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0362 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 362) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 362))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 362)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0363 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 363) = g32p_row40_cosetRepresentatives 363 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0363 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 363) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 363))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 363)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0363 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 363) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 363))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 363)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0364 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 364) = g32p_row40_cosetRepresentatives 364 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0364 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 364) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 364))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 364)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0364 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 364) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 364))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 364)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0365 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 365) = g32p_row40_cosetRepresentatives 365 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0365 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 365) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 365))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 365)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0365 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 365) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 365))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 365)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0366 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 366) = g32p_row40_cosetRepresentatives 366 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0366 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 366) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 366))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 366)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0366 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 366) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 366))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 366)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0367 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 367) = g32p_row40_cosetRepresentatives 367 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0367 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 367) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 367))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 367)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0367 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 367) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 367))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 367)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0022 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 22 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 22 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0352
  · exact g32p_row40_cosetWord_0353
  · exact g32p_row40_cosetWord_0354
  · exact g32p_row40_cosetWord_0355
  · exact g32p_row40_cosetWord_0356
  · exact g32p_row40_cosetWord_0357
  · exact g32p_row40_cosetWord_0358
  · exact g32p_row40_cosetWord_0359
  · exact g32p_row40_cosetWord_0360
  · exact g32p_row40_cosetWord_0361
  · exact g32p_row40_cosetWord_0362
  · exact g32p_row40_cosetWord_0363
  · exact g32p_row40_cosetWord_0364
  · exact g32p_row40_cosetWord_0365
  · exact g32p_row40_cosetWord_0366
  · exact g32p_row40_cosetWord_0367

theorem g32p_row40_cosetGeneratorBlock_0022 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 22 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 22 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 22 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0352 s
  · exact g32p_row40_cosetGeneratorStep_0353 s
  · exact g32p_row40_cosetGeneratorStep_0354 s
  · exact g32p_row40_cosetGeneratorStep_0355 s
  · exact g32p_row40_cosetGeneratorStep_0356 s
  · exact g32p_row40_cosetGeneratorStep_0357 s
  · exact g32p_row40_cosetGeneratorStep_0358 s
  · exact g32p_row40_cosetGeneratorStep_0359 s
  · exact g32p_row40_cosetGeneratorStep_0360 s
  · exact g32p_row40_cosetGeneratorStep_0361 s
  · exact g32p_row40_cosetGeneratorStep_0362 s
  · exact g32p_row40_cosetGeneratorStep_0363 s
  · exact g32p_row40_cosetGeneratorStep_0364 s
  · exact g32p_row40_cosetGeneratorStep_0365 s
  · exact g32p_row40_cosetGeneratorStep_0366 s
  · exact g32p_row40_cosetGeneratorStep_0367 s

theorem g32p_row40_cosetBranchBlock_0022 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 22 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 22 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 22 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0352 s
  · exact g32p_row40_cosetBranchStep_0353 s
  · exact g32p_row40_cosetBranchStep_0354 s
  · exact g32p_row40_cosetBranchStep_0355 s
  · exact g32p_row40_cosetBranchStep_0356 s
  · exact g32p_row40_cosetBranchStep_0357 s
  · exact g32p_row40_cosetBranchStep_0358 s
  · exact g32p_row40_cosetBranchStep_0359 s
  · exact g32p_row40_cosetBranchStep_0360 s
  · exact g32p_row40_cosetBranchStep_0361 s
  · exact g32p_row40_cosetBranchStep_0362 s
  · exact g32p_row40_cosetBranchStep_0363 s
  · exact g32p_row40_cosetBranchStep_0364 s
  · exact g32p_row40_cosetBranchStep_0365 s
  · exact g32p_row40_cosetBranchStep_0366 s
  · exact g32p_row40_cosetBranchStep_0367 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0368 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 368) = g32p_row40_cosetRepresentatives 368 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0368 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 368) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 368))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 368)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0368 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 368) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 368))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 368)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0369 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 369) = g32p_row40_cosetRepresentatives 369 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0369 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 369) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 369))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 369)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0369 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 369) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 369))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 369)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0370 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 370) = g32p_row40_cosetRepresentatives 370 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0370 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 370) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 370))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 370)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0370 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 370) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 370))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 370)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0371 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 371) = g32p_row40_cosetRepresentatives 371 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0371 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 371) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 371))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 371)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0371 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 371) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 371))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 371)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0372 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 372) = g32p_row40_cosetRepresentatives 372 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0372 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 372) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 372))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 372)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0372 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 372) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 372))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 372)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0373 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 373) = g32p_row40_cosetRepresentatives 373 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0373 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 373) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 373))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 373)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0373 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 373) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 373))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 373)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0374 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 374) = g32p_row40_cosetRepresentatives 374 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0374 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 374) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 374))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 374)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0374 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 374) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 374))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 374)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0375 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 375) = g32p_row40_cosetRepresentatives 375 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0375 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 375) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 375))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 375)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0375 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 375) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 375))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 375)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0376 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 376) = g32p_row40_cosetRepresentatives 376 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0376 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 376) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 376))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 376)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0376 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 376) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 376))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 376)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0377 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 377) = g32p_row40_cosetRepresentatives 377 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0377 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 377) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 377))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 377)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0377 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 377) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 377))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 377)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0378 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 378) = g32p_row40_cosetRepresentatives 378 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0378 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 378) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 378))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 378)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0378 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 378) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 378))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 378)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0379 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 379) = g32p_row40_cosetRepresentatives 379 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0379 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 379) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 379))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 379)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0379 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 379) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 379))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 379)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0380 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 380) = g32p_row40_cosetRepresentatives 380 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0380 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 380) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 380))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 380)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0380 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 380) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 380))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 380)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0381 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 381) = g32p_row40_cosetRepresentatives 381 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0381 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 381) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 381))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 381)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0381 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 381) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 381))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 381)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0382 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 382) = g32p_row40_cosetRepresentatives 382 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0382 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 382) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 382))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 382)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0382 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 382) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 382))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 382)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0383 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 383) = g32p_row40_cosetRepresentatives 383 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0383 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 383) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 383))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 383)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0383 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 383) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 383))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 383)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0023 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 23 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 23 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0368
  · exact g32p_row40_cosetWord_0369
  · exact g32p_row40_cosetWord_0370
  · exact g32p_row40_cosetWord_0371
  · exact g32p_row40_cosetWord_0372
  · exact g32p_row40_cosetWord_0373
  · exact g32p_row40_cosetWord_0374
  · exact g32p_row40_cosetWord_0375
  · exact g32p_row40_cosetWord_0376
  · exact g32p_row40_cosetWord_0377
  · exact g32p_row40_cosetWord_0378
  · exact g32p_row40_cosetWord_0379
  · exact g32p_row40_cosetWord_0380
  · exact g32p_row40_cosetWord_0381
  · exact g32p_row40_cosetWord_0382
  · exact g32p_row40_cosetWord_0383

theorem g32p_row40_cosetGeneratorBlock_0023 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 23 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 23 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 23 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0368 s
  · exact g32p_row40_cosetGeneratorStep_0369 s
  · exact g32p_row40_cosetGeneratorStep_0370 s
  · exact g32p_row40_cosetGeneratorStep_0371 s
  · exact g32p_row40_cosetGeneratorStep_0372 s
  · exact g32p_row40_cosetGeneratorStep_0373 s
  · exact g32p_row40_cosetGeneratorStep_0374 s
  · exact g32p_row40_cosetGeneratorStep_0375 s
  · exact g32p_row40_cosetGeneratorStep_0376 s
  · exact g32p_row40_cosetGeneratorStep_0377 s
  · exact g32p_row40_cosetGeneratorStep_0378 s
  · exact g32p_row40_cosetGeneratorStep_0379 s
  · exact g32p_row40_cosetGeneratorStep_0380 s
  · exact g32p_row40_cosetGeneratorStep_0381 s
  · exact g32p_row40_cosetGeneratorStep_0382 s
  · exact g32p_row40_cosetGeneratorStep_0383 s

theorem g32p_row40_cosetBranchBlock_0023 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 23 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 23 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 23 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0368 s
  · exact g32p_row40_cosetBranchStep_0369 s
  · exact g32p_row40_cosetBranchStep_0370 s
  · exact g32p_row40_cosetBranchStep_0371 s
  · exact g32p_row40_cosetBranchStep_0372 s
  · exact g32p_row40_cosetBranchStep_0373 s
  · exact g32p_row40_cosetBranchStep_0374 s
  · exact g32p_row40_cosetBranchStep_0375 s
  · exact g32p_row40_cosetBranchStep_0376 s
  · exact g32p_row40_cosetBranchStep_0377 s
  · exact g32p_row40_cosetBranchStep_0378 s
  · exact g32p_row40_cosetBranchStep_0379 s
  · exact g32p_row40_cosetBranchStep_0380 s
  · exact g32p_row40_cosetBranchStep_0381 s
  · exact g32p_row40_cosetBranchStep_0382 s
  · exact g32p_row40_cosetBranchStep_0383 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0384 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 384) = g32p_row40_cosetRepresentatives 384 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0384 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 384) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 384))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 384)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0384 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 384) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 384))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 384)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0385 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 385) = g32p_row40_cosetRepresentatives 385 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0385 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 385) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 385))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 385)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0385 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 385) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 385))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 385)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0386 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 386) = g32p_row40_cosetRepresentatives 386 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0386 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 386) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 386))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 386)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0386 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 386) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 386))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 386)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0387 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 387) = g32p_row40_cosetRepresentatives 387 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0387 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 387) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 387))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 387)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0387 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 387) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 387))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 387)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0388 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 388) = g32p_row40_cosetRepresentatives 388 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0388 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 388) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 388))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 388)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0388 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 388) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 388))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 388)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0389 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 389) = g32p_row40_cosetRepresentatives 389 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0389 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 389) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 389))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 389)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0389 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 389) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 389))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 389)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0390 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 390) = g32p_row40_cosetRepresentatives 390 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0390 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 390) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 390))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 390)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0390 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 390) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 390))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 390)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0391 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 391) = g32p_row40_cosetRepresentatives 391 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0391 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 391) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 391))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 391)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0391 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 391) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 391))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 391)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0392 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 392) = g32p_row40_cosetRepresentatives 392 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0392 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 392) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 392))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 392)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0392 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 392) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 392))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 392)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0393 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 393) = g32p_row40_cosetRepresentatives 393 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0393 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 393) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 393))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 393)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0393 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 393) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 393))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 393)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0394 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 394) = g32p_row40_cosetRepresentatives 394 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0394 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 394) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 394))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 394)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0394 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 394) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 394))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 394)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0395 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 395) = g32p_row40_cosetRepresentatives 395 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0395 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 395) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 395))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 395)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0395 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 395) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 395))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 395)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0396 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 396) = g32p_row40_cosetRepresentatives 396 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0396 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 396) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 396))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 396)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0396 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 396) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 396))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 396)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0397 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 397) = g32p_row40_cosetRepresentatives 397 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0397 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 397) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 397))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 397)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0397 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 397) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 397))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 397)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0398 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 398) = g32p_row40_cosetRepresentatives 398 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0398 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 398) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 398))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 398)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0398 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 398) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 398))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 398)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0399 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 399) = g32p_row40_cosetRepresentatives 399 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0399 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 399) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 399))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 399)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0399 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 399) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 399))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 399)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0024 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 24 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 24 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0384
  · exact g32p_row40_cosetWord_0385
  · exact g32p_row40_cosetWord_0386
  · exact g32p_row40_cosetWord_0387
  · exact g32p_row40_cosetWord_0388
  · exact g32p_row40_cosetWord_0389
  · exact g32p_row40_cosetWord_0390
  · exact g32p_row40_cosetWord_0391
  · exact g32p_row40_cosetWord_0392
  · exact g32p_row40_cosetWord_0393
  · exact g32p_row40_cosetWord_0394
  · exact g32p_row40_cosetWord_0395
  · exact g32p_row40_cosetWord_0396
  · exact g32p_row40_cosetWord_0397
  · exact g32p_row40_cosetWord_0398
  · exact g32p_row40_cosetWord_0399

theorem g32p_row40_cosetGeneratorBlock_0024 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 24 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 24 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 24 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0384 s
  · exact g32p_row40_cosetGeneratorStep_0385 s
  · exact g32p_row40_cosetGeneratorStep_0386 s
  · exact g32p_row40_cosetGeneratorStep_0387 s
  · exact g32p_row40_cosetGeneratorStep_0388 s
  · exact g32p_row40_cosetGeneratorStep_0389 s
  · exact g32p_row40_cosetGeneratorStep_0390 s
  · exact g32p_row40_cosetGeneratorStep_0391 s
  · exact g32p_row40_cosetGeneratorStep_0392 s
  · exact g32p_row40_cosetGeneratorStep_0393 s
  · exact g32p_row40_cosetGeneratorStep_0394 s
  · exact g32p_row40_cosetGeneratorStep_0395 s
  · exact g32p_row40_cosetGeneratorStep_0396 s
  · exact g32p_row40_cosetGeneratorStep_0397 s
  · exact g32p_row40_cosetGeneratorStep_0398 s
  · exact g32p_row40_cosetGeneratorStep_0399 s

theorem g32p_row40_cosetBranchBlock_0024 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 24 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 24 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 24 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0384 s
  · exact g32p_row40_cosetBranchStep_0385 s
  · exact g32p_row40_cosetBranchStep_0386 s
  · exact g32p_row40_cosetBranchStep_0387 s
  · exact g32p_row40_cosetBranchStep_0388 s
  · exact g32p_row40_cosetBranchStep_0389 s
  · exact g32p_row40_cosetBranchStep_0390 s
  · exact g32p_row40_cosetBranchStep_0391 s
  · exact g32p_row40_cosetBranchStep_0392 s
  · exact g32p_row40_cosetBranchStep_0393 s
  · exact g32p_row40_cosetBranchStep_0394 s
  · exact g32p_row40_cosetBranchStep_0395 s
  · exact g32p_row40_cosetBranchStep_0396 s
  · exact g32p_row40_cosetBranchStep_0397 s
  · exact g32p_row40_cosetBranchStep_0398 s
  · exact g32p_row40_cosetBranchStep_0399 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0400 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 400) = g32p_row40_cosetRepresentatives 400 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0400 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 400) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 400))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 400)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0400 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 400) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 400))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 400)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0401 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 401) = g32p_row40_cosetRepresentatives 401 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0401 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 401) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 401))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 401)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0401 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 401) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 401))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 401)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0402 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 402) = g32p_row40_cosetRepresentatives 402 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0402 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 402) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 402))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 402)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0402 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 402) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 402))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 402)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0403 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 403) = g32p_row40_cosetRepresentatives 403 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0403 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 403) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 403))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 403)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0403 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 403) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 403))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 403)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0404 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 404) = g32p_row40_cosetRepresentatives 404 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0404 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 404) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 404))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 404)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0404 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 404) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 404))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 404)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0405 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 405) = g32p_row40_cosetRepresentatives 405 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0405 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 405) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 405))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 405)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0405 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 405) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 405))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 405)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0406 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 406) = g32p_row40_cosetRepresentatives 406 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0406 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 406) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 406))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 406)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0406 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 406) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 406))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 406)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0407 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 407) = g32p_row40_cosetRepresentatives 407 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0407 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 407) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 407))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 407)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0407 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 407) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 407))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 407)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0408 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 408) = g32p_row40_cosetRepresentatives 408 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0408 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 408) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 408))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 408)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0408 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 408) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 408))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 408)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0409 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 409) = g32p_row40_cosetRepresentatives 409 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0409 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 409) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 409))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 409)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0409 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 409) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 409))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 409)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0410 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 410) = g32p_row40_cosetRepresentatives 410 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0410 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 410) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 410))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 410)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0410 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 410) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 410))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 410)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0411 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 411) = g32p_row40_cosetRepresentatives 411 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0411 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 411) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 411))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 411)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0411 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 411) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 411))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 411)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0412 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 412) = g32p_row40_cosetRepresentatives 412 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0412 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 412) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 412))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 412)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0412 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 412) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 412))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 412)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0413 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 413) = g32p_row40_cosetRepresentatives 413 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0413 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 413) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 413))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 413)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0413 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 413) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 413))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 413)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0414 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 414) = g32p_row40_cosetRepresentatives 414 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0414 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 414) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 414))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 414)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0414 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 414) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 414))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 414)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0415 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 415) = g32p_row40_cosetRepresentatives 415 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0415 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 415) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 415))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 415)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0415 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 415) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 415))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 415)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0025 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 25 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 25 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0400
  · exact g32p_row40_cosetWord_0401
  · exact g32p_row40_cosetWord_0402
  · exact g32p_row40_cosetWord_0403
  · exact g32p_row40_cosetWord_0404
  · exact g32p_row40_cosetWord_0405
  · exact g32p_row40_cosetWord_0406
  · exact g32p_row40_cosetWord_0407
  · exact g32p_row40_cosetWord_0408
  · exact g32p_row40_cosetWord_0409
  · exact g32p_row40_cosetWord_0410
  · exact g32p_row40_cosetWord_0411
  · exact g32p_row40_cosetWord_0412
  · exact g32p_row40_cosetWord_0413
  · exact g32p_row40_cosetWord_0414
  · exact g32p_row40_cosetWord_0415

theorem g32p_row40_cosetGeneratorBlock_0025 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 25 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 25 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 25 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0400 s
  · exact g32p_row40_cosetGeneratorStep_0401 s
  · exact g32p_row40_cosetGeneratorStep_0402 s
  · exact g32p_row40_cosetGeneratorStep_0403 s
  · exact g32p_row40_cosetGeneratorStep_0404 s
  · exact g32p_row40_cosetGeneratorStep_0405 s
  · exact g32p_row40_cosetGeneratorStep_0406 s
  · exact g32p_row40_cosetGeneratorStep_0407 s
  · exact g32p_row40_cosetGeneratorStep_0408 s
  · exact g32p_row40_cosetGeneratorStep_0409 s
  · exact g32p_row40_cosetGeneratorStep_0410 s
  · exact g32p_row40_cosetGeneratorStep_0411 s
  · exact g32p_row40_cosetGeneratorStep_0412 s
  · exact g32p_row40_cosetGeneratorStep_0413 s
  · exact g32p_row40_cosetGeneratorStep_0414 s
  · exact g32p_row40_cosetGeneratorStep_0415 s

theorem g32p_row40_cosetBranchBlock_0025 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 25 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 25 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 25 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0400 s
  · exact g32p_row40_cosetBranchStep_0401 s
  · exact g32p_row40_cosetBranchStep_0402 s
  · exact g32p_row40_cosetBranchStep_0403 s
  · exact g32p_row40_cosetBranchStep_0404 s
  · exact g32p_row40_cosetBranchStep_0405 s
  · exact g32p_row40_cosetBranchStep_0406 s
  · exact g32p_row40_cosetBranchStep_0407 s
  · exact g32p_row40_cosetBranchStep_0408 s
  · exact g32p_row40_cosetBranchStep_0409 s
  · exact g32p_row40_cosetBranchStep_0410 s
  · exact g32p_row40_cosetBranchStep_0411 s
  · exact g32p_row40_cosetBranchStep_0412 s
  · exact g32p_row40_cosetBranchStep_0413 s
  · exact g32p_row40_cosetBranchStep_0414 s
  · exact g32p_row40_cosetBranchStep_0415 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0416 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 416) = g32p_row40_cosetRepresentatives 416 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0416 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 416) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 416))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 416)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0416 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 416) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 416))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 416)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0417 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 417) = g32p_row40_cosetRepresentatives 417 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0417 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 417) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 417))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 417)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0417 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 417) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 417))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 417)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0418 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 418) = g32p_row40_cosetRepresentatives 418 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0418 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 418) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 418))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 418)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0418 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 418) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 418))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 418)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0419 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 419) = g32p_row40_cosetRepresentatives 419 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0419 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 419) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 419))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 419)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0419 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 419) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 419))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 419)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0420 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 420) = g32p_row40_cosetRepresentatives 420 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0420 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 420) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 420))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 420)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0420 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 420) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 420))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 420)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0421 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 421) = g32p_row40_cosetRepresentatives 421 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0421 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 421) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 421))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 421)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0421 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 421) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 421))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 421)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0422 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 422) = g32p_row40_cosetRepresentatives 422 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0422 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 422) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 422))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 422)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0422 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 422) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 422))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 422)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0423 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 423) = g32p_row40_cosetRepresentatives 423 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0423 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 423) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 423))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 423)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0423 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 423) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 423))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 423)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0424 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 424) = g32p_row40_cosetRepresentatives 424 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0424 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 424) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 424))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 424)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0424 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 424) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 424))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 424)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0425 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 425) = g32p_row40_cosetRepresentatives 425 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0425 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 425) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 425))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 425)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0425 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 425) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 425))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 425)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0426 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 426) = g32p_row40_cosetRepresentatives 426 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0426 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 426) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 426))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 426)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0426 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 426) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 426))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 426)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0427 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 427) = g32p_row40_cosetRepresentatives 427 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0427 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 427) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 427))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 427)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0427 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 427) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 427))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 427)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0428 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 428) = g32p_row40_cosetRepresentatives 428 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0428 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 428) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 428))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 428)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0428 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 428) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 428))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 428)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0429 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 429) = g32p_row40_cosetRepresentatives 429 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0429 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 429) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 429))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 429)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0429 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 429) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 429))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 429)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0430 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 430) = g32p_row40_cosetRepresentatives 430 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0430 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 430) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 430))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 430)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0430 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 430) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 430))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 430)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0431 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 431) = g32p_row40_cosetRepresentatives 431 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0431 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 431) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 431))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 431)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0431 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 431) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 431))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 431)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0026 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 26 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 26 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0416
  · exact g32p_row40_cosetWord_0417
  · exact g32p_row40_cosetWord_0418
  · exact g32p_row40_cosetWord_0419
  · exact g32p_row40_cosetWord_0420
  · exact g32p_row40_cosetWord_0421
  · exact g32p_row40_cosetWord_0422
  · exact g32p_row40_cosetWord_0423
  · exact g32p_row40_cosetWord_0424
  · exact g32p_row40_cosetWord_0425
  · exact g32p_row40_cosetWord_0426
  · exact g32p_row40_cosetWord_0427
  · exact g32p_row40_cosetWord_0428
  · exact g32p_row40_cosetWord_0429
  · exact g32p_row40_cosetWord_0430
  · exact g32p_row40_cosetWord_0431

theorem g32p_row40_cosetGeneratorBlock_0026 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 26 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 26 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 26 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0416 s
  · exact g32p_row40_cosetGeneratorStep_0417 s
  · exact g32p_row40_cosetGeneratorStep_0418 s
  · exact g32p_row40_cosetGeneratorStep_0419 s
  · exact g32p_row40_cosetGeneratorStep_0420 s
  · exact g32p_row40_cosetGeneratorStep_0421 s
  · exact g32p_row40_cosetGeneratorStep_0422 s
  · exact g32p_row40_cosetGeneratorStep_0423 s
  · exact g32p_row40_cosetGeneratorStep_0424 s
  · exact g32p_row40_cosetGeneratorStep_0425 s
  · exact g32p_row40_cosetGeneratorStep_0426 s
  · exact g32p_row40_cosetGeneratorStep_0427 s
  · exact g32p_row40_cosetGeneratorStep_0428 s
  · exact g32p_row40_cosetGeneratorStep_0429 s
  · exact g32p_row40_cosetGeneratorStep_0430 s
  · exact g32p_row40_cosetGeneratorStep_0431 s

theorem g32p_row40_cosetBranchBlock_0026 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 26 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 26 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 26 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0416 s
  · exact g32p_row40_cosetBranchStep_0417 s
  · exact g32p_row40_cosetBranchStep_0418 s
  · exact g32p_row40_cosetBranchStep_0419 s
  · exact g32p_row40_cosetBranchStep_0420 s
  · exact g32p_row40_cosetBranchStep_0421 s
  · exact g32p_row40_cosetBranchStep_0422 s
  · exact g32p_row40_cosetBranchStep_0423 s
  · exact g32p_row40_cosetBranchStep_0424 s
  · exact g32p_row40_cosetBranchStep_0425 s
  · exact g32p_row40_cosetBranchStep_0426 s
  · exact g32p_row40_cosetBranchStep_0427 s
  · exact g32p_row40_cosetBranchStep_0428 s
  · exact g32p_row40_cosetBranchStep_0429 s
  · exact g32p_row40_cosetBranchStep_0430 s
  · exact g32p_row40_cosetBranchStep_0431 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0432 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 432) = g32p_row40_cosetRepresentatives 432 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0432 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 432) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 432))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 432)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0432 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 432) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 432))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 432)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0433 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 433) = g32p_row40_cosetRepresentatives 433 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0433 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 433) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 433))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 433)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0433 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 433) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 433))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 433)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0434 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 434) = g32p_row40_cosetRepresentatives 434 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0434 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 434) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 434))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 434)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0434 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 434) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 434))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 434)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0435 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 435) = g32p_row40_cosetRepresentatives 435 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0435 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 435) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 435))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 435)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0435 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 435) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 435))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 435)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0436 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 436) = g32p_row40_cosetRepresentatives 436 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0436 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 436) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 436))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 436)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0436 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 436) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 436))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 436)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0437 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 437) = g32p_row40_cosetRepresentatives 437 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0437 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 437) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 437))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 437)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0437 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 437) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 437))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 437)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0438 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 438) = g32p_row40_cosetRepresentatives 438 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0438 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 438) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 438))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 438)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0438 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 438) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 438))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 438)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0439 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 439) = g32p_row40_cosetRepresentatives 439 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0439 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 439) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 439))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 439)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0439 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 439) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 439))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 439)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0440 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 440) = g32p_row40_cosetRepresentatives 440 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0440 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 440) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 440))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 440)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0440 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 440) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 440))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 440)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0441 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 441) = g32p_row40_cosetRepresentatives 441 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0441 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 441) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 441))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 441)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0441 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 441) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 441))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 441)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0442 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 442) = g32p_row40_cosetRepresentatives 442 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0442 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 442) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 442))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 442)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0442 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 442) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 442))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 442)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0443 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 443) = g32p_row40_cosetRepresentatives 443 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0443 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 443) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 443))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 443)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0443 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 443) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 443))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 443)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0444 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 444) = g32p_row40_cosetRepresentatives 444 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0444 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 444) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 444))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 444)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0444 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 444) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 444))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 444)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0445 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 445) = g32p_row40_cosetRepresentatives 445 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0445 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 445) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 445))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 445)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0445 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 445) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 445))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 445)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0446 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 446) = g32p_row40_cosetRepresentatives 446 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0446 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 446) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 446))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 446)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0446 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 446) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 446))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 446)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0447 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 447) = g32p_row40_cosetRepresentatives 447 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0447 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 447) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 447))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 447)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0447 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 447) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 447))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 447)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0027 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 27 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 27 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0432
  · exact g32p_row40_cosetWord_0433
  · exact g32p_row40_cosetWord_0434
  · exact g32p_row40_cosetWord_0435
  · exact g32p_row40_cosetWord_0436
  · exact g32p_row40_cosetWord_0437
  · exact g32p_row40_cosetWord_0438
  · exact g32p_row40_cosetWord_0439
  · exact g32p_row40_cosetWord_0440
  · exact g32p_row40_cosetWord_0441
  · exact g32p_row40_cosetWord_0442
  · exact g32p_row40_cosetWord_0443
  · exact g32p_row40_cosetWord_0444
  · exact g32p_row40_cosetWord_0445
  · exact g32p_row40_cosetWord_0446
  · exact g32p_row40_cosetWord_0447

theorem g32p_row40_cosetGeneratorBlock_0027 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 27 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 27 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 27 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0432 s
  · exact g32p_row40_cosetGeneratorStep_0433 s
  · exact g32p_row40_cosetGeneratorStep_0434 s
  · exact g32p_row40_cosetGeneratorStep_0435 s
  · exact g32p_row40_cosetGeneratorStep_0436 s
  · exact g32p_row40_cosetGeneratorStep_0437 s
  · exact g32p_row40_cosetGeneratorStep_0438 s
  · exact g32p_row40_cosetGeneratorStep_0439 s
  · exact g32p_row40_cosetGeneratorStep_0440 s
  · exact g32p_row40_cosetGeneratorStep_0441 s
  · exact g32p_row40_cosetGeneratorStep_0442 s
  · exact g32p_row40_cosetGeneratorStep_0443 s
  · exact g32p_row40_cosetGeneratorStep_0444 s
  · exact g32p_row40_cosetGeneratorStep_0445 s
  · exact g32p_row40_cosetGeneratorStep_0446 s
  · exact g32p_row40_cosetGeneratorStep_0447 s

theorem g32p_row40_cosetBranchBlock_0027 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 27 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 27 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 27 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0432 s
  · exact g32p_row40_cosetBranchStep_0433 s
  · exact g32p_row40_cosetBranchStep_0434 s
  · exact g32p_row40_cosetBranchStep_0435 s
  · exact g32p_row40_cosetBranchStep_0436 s
  · exact g32p_row40_cosetBranchStep_0437 s
  · exact g32p_row40_cosetBranchStep_0438 s
  · exact g32p_row40_cosetBranchStep_0439 s
  · exact g32p_row40_cosetBranchStep_0440 s
  · exact g32p_row40_cosetBranchStep_0441 s
  · exact g32p_row40_cosetBranchStep_0442 s
  · exact g32p_row40_cosetBranchStep_0443 s
  · exact g32p_row40_cosetBranchStep_0444 s
  · exact g32p_row40_cosetBranchStep_0445 s
  · exact g32p_row40_cosetBranchStep_0446 s
  · exact g32p_row40_cosetBranchStep_0447 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0448 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 448) = g32p_row40_cosetRepresentatives 448 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0448 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 448) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 448))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 448)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0448 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 448) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 448))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 448)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0449 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 449) = g32p_row40_cosetRepresentatives 449 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0449 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 449) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 449))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 449)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0449 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 449) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 449))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 449)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0450 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 450) = g32p_row40_cosetRepresentatives 450 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0450 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 450) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 450))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 450)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0450 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 450) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 450))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 450)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0451 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 451) = g32p_row40_cosetRepresentatives 451 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0451 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 451) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 451))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 451)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0451 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 451) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 451))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 451)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0452 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 452) = g32p_row40_cosetRepresentatives 452 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0452 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 452) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 452))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 452)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0452 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 452) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 452))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 452)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0453 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 453) = g32p_row40_cosetRepresentatives 453 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0453 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 453) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 453))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 453)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0453 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 453) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 453))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 453)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0454 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 454) = g32p_row40_cosetRepresentatives 454 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0454 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 454) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 454))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 454)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0454 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 454) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 454))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 454)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0455 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 455) = g32p_row40_cosetRepresentatives 455 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0455 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 455) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 455))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 455)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0455 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 455) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 455))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 455)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0456 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 456) = g32p_row40_cosetRepresentatives 456 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0456 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 456) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 456))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 456)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0456 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 456) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 456))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 456)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0457 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 457) = g32p_row40_cosetRepresentatives 457 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0457 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 457) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 457))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 457)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0457 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 457) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 457))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 457)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0458 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 458) = g32p_row40_cosetRepresentatives 458 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0458 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 458) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 458))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 458)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0458 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 458) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 458))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 458)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0459 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 459) = g32p_row40_cosetRepresentatives 459 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0459 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 459) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 459))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 459)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0459 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 459) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 459))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 459)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0460 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 460) = g32p_row40_cosetRepresentatives 460 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0460 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 460) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 460))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 460)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0460 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 460) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 460))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 460)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0461 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 461) = g32p_row40_cosetRepresentatives 461 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0461 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 461) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 461))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 461)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0461 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 461) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 461))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 461)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0462 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 462) = g32p_row40_cosetRepresentatives 462 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0462 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 462) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 462))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 462)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0462 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 462) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 462))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 462)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0463 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 463) = g32p_row40_cosetRepresentatives 463 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0463 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 463) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 463))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 463)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0463 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 463) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 463))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 463)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0028 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 28 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 28 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0448
  · exact g32p_row40_cosetWord_0449
  · exact g32p_row40_cosetWord_0450
  · exact g32p_row40_cosetWord_0451
  · exact g32p_row40_cosetWord_0452
  · exact g32p_row40_cosetWord_0453
  · exact g32p_row40_cosetWord_0454
  · exact g32p_row40_cosetWord_0455
  · exact g32p_row40_cosetWord_0456
  · exact g32p_row40_cosetWord_0457
  · exact g32p_row40_cosetWord_0458
  · exact g32p_row40_cosetWord_0459
  · exact g32p_row40_cosetWord_0460
  · exact g32p_row40_cosetWord_0461
  · exact g32p_row40_cosetWord_0462
  · exact g32p_row40_cosetWord_0463

theorem g32p_row40_cosetGeneratorBlock_0028 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 28 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 28 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 28 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0448 s
  · exact g32p_row40_cosetGeneratorStep_0449 s
  · exact g32p_row40_cosetGeneratorStep_0450 s
  · exact g32p_row40_cosetGeneratorStep_0451 s
  · exact g32p_row40_cosetGeneratorStep_0452 s
  · exact g32p_row40_cosetGeneratorStep_0453 s
  · exact g32p_row40_cosetGeneratorStep_0454 s
  · exact g32p_row40_cosetGeneratorStep_0455 s
  · exact g32p_row40_cosetGeneratorStep_0456 s
  · exact g32p_row40_cosetGeneratorStep_0457 s
  · exact g32p_row40_cosetGeneratorStep_0458 s
  · exact g32p_row40_cosetGeneratorStep_0459 s
  · exact g32p_row40_cosetGeneratorStep_0460 s
  · exact g32p_row40_cosetGeneratorStep_0461 s
  · exact g32p_row40_cosetGeneratorStep_0462 s
  · exact g32p_row40_cosetGeneratorStep_0463 s

theorem g32p_row40_cosetBranchBlock_0028 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 28 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 28 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 28 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0448 s
  · exact g32p_row40_cosetBranchStep_0449 s
  · exact g32p_row40_cosetBranchStep_0450 s
  · exact g32p_row40_cosetBranchStep_0451 s
  · exact g32p_row40_cosetBranchStep_0452 s
  · exact g32p_row40_cosetBranchStep_0453 s
  · exact g32p_row40_cosetBranchStep_0454 s
  · exact g32p_row40_cosetBranchStep_0455 s
  · exact g32p_row40_cosetBranchStep_0456 s
  · exact g32p_row40_cosetBranchStep_0457 s
  · exact g32p_row40_cosetBranchStep_0458 s
  · exact g32p_row40_cosetBranchStep_0459 s
  · exact g32p_row40_cosetBranchStep_0460 s
  · exact g32p_row40_cosetBranchStep_0461 s
  · exact g32p_row40_cosetBranchStep_0462 s
  · exact g32p_row40_cosetBranchStep_0463 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0464 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 464) = g32p_row40_cosetRepresentatives 464 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0464 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 464) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 464))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 464)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0464 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 464) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 464))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 464)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0465 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 465) = g32p_row40_cosetRepresentatives 465 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0465 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 465) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 465))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 465)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0465 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 465) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 465))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 465)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0466 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 466) = g32p_row40_cosetRepresentatives 466 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0466 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 466) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 466))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 466)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0466 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 466) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 466))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 466)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0467 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 467) = g32p_row40_cosetRepresentatives 467 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0467 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 467) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 467))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 467)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0467 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 467) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 467))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 467)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0468 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 468) = g32p_row40_cosetRepresentatives 468 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0468 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 468) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 468))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 468)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0468 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 468) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 468))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 468)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0469 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 469) = g32p_row40_cosetRepresentatives 469 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0469 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 469) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 469))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 469)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0469 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 469) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 469))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 469)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0470 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 470) = g32p_row40_cosetRepresentatives 470 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0470 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 470) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 470))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 470)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0470 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 470) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 470))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 470)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0471 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 471) = g32p_row40_cosetRepresentatives 471 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0471 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 471) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 471))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 471)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0471 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 471) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 471))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 471)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0472 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 472) = g32p_row40_cosetRepresentatives 472 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0472 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 472) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 472))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 472)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0472 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 472) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 472))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 472)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0473 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 473) = g32p_row40_cosetRepresentatives 473 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0473 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 473) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 473))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 473)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0473 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 473) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 473))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 473)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0474 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 474) = g32p_row40_cosetRepresentatives 474 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0474 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 474) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 474))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 474)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0474 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 474) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 474))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 474)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0475 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 475) = g32p_row40_cosetRepresentatives 475 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0475 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 475) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 475))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 475)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0475 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 475) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 475))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 475)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0476 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 476) = g32p_row40_cosetRepresentatives 476 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0476 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 476) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 476))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 476)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0476 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 476) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 476))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 476)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0477 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 477) = g32p_row40_cosetRepresentatives 477 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0477 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 477) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 477))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 477)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0477 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 477) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 477))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 477)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0478 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 478) = g32p_row40_cosetRepresentatives 478 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0478 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 478) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 478))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 478)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0478 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 478) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 478))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 478)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0479 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 479) = g32p_row40_cosetRepresentatives 479 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0479 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 479) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 479))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 479)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0479 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 479) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 479))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 479)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0029 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 29 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 29 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0464
  · exact g32p_row40_cosetWord_0465
  · exact g32p_row40_cosetWord_0466
  · exact g32p_row40_cosetWord_0467
  · exact g32p_row40_cosetWord_0468
  · exact g32p_row40_cosetWord_0469
  · exact g32p_row40_cosetWord_0470
  · exact g32p_row40_cosetWord_0471
  · exact g32p_row40_cosetWord_0472
  · exact g32p_row40_cosetWord_0473
  · exact g32p_row40_cosetWord_0474
  · exact g32p_row40_cosetWord_0475
  · exact g32p_row40_cosetWord_0476
  · exact g32p_row40_cosetWord_0477
  · exact g32p_row40_cosetWord_0478
  · exact g32p_row40_cosetWord_0479

theorem g32p_row40_cosetGeneratorBlock_0029 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 29 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 29 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 29 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0464 s
  · exact g32p_row40_cosetGeneratorStep_0465 s
  · exact g32p_row40_cosetGeneratorStep_0466 s
  · exact g32p_row40_cosetGeneratorStep_0467 s
  · exact g32p_row40_cosetGeneratorStep_0468 s
  · exact g32p_row40_cosetGeneratorStep_0469 s
  · exact g32p_row40_cosetGeneratorStep_0470 s
  · exact g32p_row40_cosetGeneratorStep_0471 s
  · exact g32p_row40_cosetGeneratorStep_0472 s
  · exact g32p_row40_cosetGeneratorStep_0473 s
  · exact g32p_row40_cosetGeneratorStep_0474 s
  · exact g32p_row40_cosetGeneratorStep_0475 s
  · exact g32p_row40_cosetGeneratorStep_0476 s
  · exact g32p_row40_cosetGeneratorStep_0477 s
  · exact g32p_row40_cosetGeneratorStep_0478 s
  · exact g32p_row40_cosetGeneratorStep_0479 s

theorem g32p_row40_cosetBranchBlock_0029 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 29 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 29 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 29 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0464 s
  · exact g32p_row40_cosetBranchStep_0465 s
  · exact g32p_row40_cosetBranchStep_0466 s
  · exact g32p_row40_cosetBranchStep_0467 s
  · exact g32p_row40_cosetBranchStep_0468 s
  · exact g32p_row40_cosetBranchStep_0469 s
  · exact g32p_row40_cosetBranchStep_0470 s
  · exact g32p_row40_cosetBranchStep_0471 s
  · exact g32p_row40_cosetBranchStep_0472 s
  · exact g32p_row40_cosetBranchStep_0473 s
  · exact g32p_row40_cosetBranchStep_0474 s
  · exact g32p_row40_cosetBranchStep_0475 s
  · exact g32p_row40_cosetBranchStep_0476 s
  · exact g32p_row40_cosetBranchStep_0477 s
  · exact g32p_row40_cosetBranchStep_0478 s
  · exact g32p_row40_cosetBranchStep_0479 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0480 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 480) = g32p_row40_cosetRepresentatives 480 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0480 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 480) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 480))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 480)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0480 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 480) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 480))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 480)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0481 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 481) = g32p_row40_cosetRepresentatives 481 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0481 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 481) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 481))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 481)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0481 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 481) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 481))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 481)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0482 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 482) = g32p_row40_cosetRepresentatives 482 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0482 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 482) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 482))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 482)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0482 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 482) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 482))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 482)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0483 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 483) = g32p_row40_cosetRepresentatives 483 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0483 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 483) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 483))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 483)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0483 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 483) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 483))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 483)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0484 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 484) = g32p_row40_cosetRepresentatives 484 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0484 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 484) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 484))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 484)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0484 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 484) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 484))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 484)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0485 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 485) = g32p_row40_cosetRepresentatives 485 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0485 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 485) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 485))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 485)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0485 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 485) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 485))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 485)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0486 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 486) = g32p_row40_cosetRepresentatives 486 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0486 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 486) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 486))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 486)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0486 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 486) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 486))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 486)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0487 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 487) = g32p_row40_cosetRepresentatives 487 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0487 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 487) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 487))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 487)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0487 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 487) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 487))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 487)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0488 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 488) = g32p_row40_cosetRepresentatives 488 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0488 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 488) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 488))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 488)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0488 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 488) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 488))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 488)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0489 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 489) = g32p_row40_cosetRepresentatives 489 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0489 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 489) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 489))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 489)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0489 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 489) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 489))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 489)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0490 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 490) = g32p_row40_cosetRepresentatives 490 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0490 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 490) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 490))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 490)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0490 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 490) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 490))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 490)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0491 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 491) = g32p_row40_cosetRepresentatives 491 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0491 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 491) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 491))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 491)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0491 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 491) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 491))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 491)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0492 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 492) = g32p_row40_cosetRepresentatives 492 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0492 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 492) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 492))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 492)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0492 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 492) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 492))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 492)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0493 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 493) = g32p_row40_cosetRepresentatives 493 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0493 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 493) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 493))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 493)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0493 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 493) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 493))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 493)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0494 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 494) = g32p_row40_cosetRepresentatives 494 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0494 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 494) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 494))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 494)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0494 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 494) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 494))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 494)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0495 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 495) = g32p_row40_cosetRepresentatives 495 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0495 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 495) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 495))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 495)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0495 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 495) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 495))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 495)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0030 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 30 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 30 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0480
  · exact g32p_row40_cosetWord_0481
  · exact g32p_row40_cosetWord_0482
  · exact g32p_row40_cosetWord_0483
  · exact g32p_row40_cosetWord_0484
  · exact g32p_row40_cosetWord_0485
  · exact g32p_row40_cosetWord_0486
  · exact g32p_row40_cosetWord_0487
  · exact g32p_row40_cosetWord_0488
  · exact g32p_row40_cosetWord_0489
  · exact g32p_row40_cosetWord_0490
  · exact g32p_row40_cosetWord_0491
  · exact g32p_row40_cosetWord_0492
  · exact g32p_row40_cosetWord_0493
  · exact g32p_row40_cosetWord_0494
  · exact g32p_row40_cosetWord_0495

theorem g32p_row40_cosetGeneratorBlock_0030 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 30 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 30 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 30 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0480 s
  · exact g32p_row40_cosetGeneratorStep_0481 s
  · exact g32p_row40_cosetGeneratorStep_0482 s
  · exact g32p_row40_cosetGeneratorStep_0483 s
  · exact g32p_row40_cosetGeneratorStep_0484 s
  · exact g32p_row40_cosetGeneratorStep_0485 s
  · exact g32p_row40_cosetGeneratorStep_0486 s
  · exact g32p_row40_cosetGeneratorStep_0487 s
  · exact g32p_row40_cosetGeneratorStep_0488 s
  · exact g32p_row40_cosetGeneratorStep_0489 s
  · exact g32p_row40_cosetGeneratorStep_0490 s
  · exact g32p_row40_cosetGeneratorStep_0491 s
  · exact g32p_row40_cosetGeneratorStep_0492 s
  · exact g32p_row40_cosetGeneratorStep_0493 s
  · exact g32p_row40_cosetGeneratorStep_0494 s
  · exact g32p_row40_cosetGeneratorStep_0495 s

theorem g32p_row40_cosetBranchBlock_0030 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 30 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 30 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 30 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0480 s
  · exact g32p_row40_cosetBranchStep_0481 s
  · exact g32p_row40_cosetBranchStep_0482 s
  · exact g32p_row40_cosetBranchStep_0483 s
  · exact g32p_row40_cosetBranchStep_0484 s
  · exact g32p_row40_cosetBranchStep_0485 s
  · exact g32p_row40_cosetBranchStep_0486 s
  · exact g32p_row40_cosetBranchStep_0487 s
  · exact g32p_row40_cosetBranchStep_0488 s
  · exact g32p_row40_cosetBranchStep_0489 s
  · exact g32p_row40_cosetBranchStep_0490 s
  · exact g32p_row40_cosetBranchStep_0491 s
  · exact g32p_row40_cosetBranchStep_0492 s
  · exact g32p_row40_cosetBranchStep_0493 s
  · exact g32p_row40_cosetBranchStep_0494 s
  · exact g32p_row40_cosetBranchStep_0495 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row40_cosetWord_0496 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 496) = g32p_row40_cosetRepresentatives 496 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0496 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 496) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 496))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 496)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0496 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 496) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 496))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 496)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0497 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 497) = g32p_row40_cosetRepresentatives 497 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0497 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 497) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 497))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 497)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0497 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 497) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 497))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 497)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0498 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 498) = g32p_row40_cosetRepresentatives 498 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0498 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 498) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 498))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 498)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0498 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 498) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 498))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 498)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0499 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 499) = g32p_row40_cosetRepresentatives 499 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0499 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 499) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 499))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 499)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0499 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 499) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 499))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 499)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0500 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 500) = g32p_row40_cosetRepresentatives 500 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0500 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 500) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 500))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 500)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0500 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 500) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 500))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 500)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0501 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 501) = g32p_row40_cosetRepresentatives 501 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0501 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 501) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 501))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 501)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0501 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 501) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 501))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 501)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0502 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 502) = g32p_row40_cosetRepresentatives 502 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0502 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 502) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 502))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 502)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0502 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 502) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 502))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 502)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0503 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 503) = g32p_row40_cosetRepresentatives 503 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0503 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 503) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 503))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 503)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0503 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 503) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 503))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 503)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0504 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 504) = g32p_row40_cosetRepresentatives 504 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0504 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 504) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 504))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 504)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0504 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 504) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 504))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 504)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0505 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 505) = g32p_row40_cosetRepresentatives 505 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0505 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 505) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 505))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 505)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0505 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 505) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 505))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 505)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0506 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 506) = g32p_row40_cosetRepresentatives 506 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0506 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 506) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 506))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 506)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0506 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 506) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 506))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 506)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0507 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 507) = g32p_row40_cosetRepresentatives 507 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0507 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 507) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 507))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 507)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0507 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 507) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 507))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 507)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0508 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 508) = g32p_row40_cosetRepresentatives 508 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0508 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 508) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 508))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 508)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0508 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 508) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 508))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 508)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0509 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 509) = g32p_row40_cosetRepresentatives 509 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0509 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 509) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 509))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 509)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0509 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 509) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 509))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 509)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0510 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 510) = g32p_row40_cosetRepresentatives 510 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0510 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 510) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 510))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 510)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0510 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 510) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 510))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 510)) := by
  decide +kernel

theorem g32p_row40_cosetWord_0511 :
    g32p_archiveIntegralWord (g32p_row40_cosetWords 511) = g32p_row40_cosetRepresentatives 511 := by
  decide +kernel

theorem g32p_row40_cosetGeneratorStep_0511 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives 511) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s 511))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s 511)) := by
  decide +kernel

theorem g32p_row40_cosetBranchStep_0511 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives 511) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s 511))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s 511)) := by
  decide +kernel

theorem g32p_row40_cosetWordBlock_0031 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row40_cosetWords (g32p_finBlockIndex 1080 31 r)) = g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 31 r) := by
  fin_cases r
  · exact g32p_row40_cosetWord_0496
  · exact g32p_row40_cosetWord_0497
  · exact g32p_row40_cosetWord_0498
  · exact g32p_row40_cosetWord_0499
  · exact g32p_row40_cosetWord_0500
  · exact g32p_row40_cosetWord_0501
  · exact g32p_row40_cosetWord_0502
  · exact g32p_row40_cosetWord_0503
  · exact g32p_row40_cosetWord_0504
  · exact g32p_row40_cosetWord_0505
  · exact g32p_row40_cosetWord_0506
  · exact g32p_row40_cosetWord_0507
  · exact g32p_row40_cosetWord_0508
  · exact g32p_row40_cosetWord_0509
  · exact g32p_row40_cosetWord_0510
  · exact g32p_row40_cosetWord_0511

theorem g32p_row40_cosetGeneratorBlock_0031 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 31 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetGeneratorNext s (g32p_finBlockIndex 1080 31 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetGeneratorFactor s (g32p_finBlockIndex 1080 31 r))) := by
  fin_cases r
  · exact g32p_row40_cosetGeneratorStep_0496 s
  · exact g32p_row40_cosetGeneratorStep_0497 s
  · exact g32p_row40_cosetGeneratorStep_0498 s
  · exact g32p_row40_cosetGeneratorStep_0499 s
  · exact g32p_row40_cosetGeneratorStep_0500 s
  · exact g32p_row40_cosetGeneratorStep_0501 s
  · exact g32p_row40_cosetGeneratorStep_0502 s
  · exact g32p_row40_cosetGeneratorStep_0503 s
  · exact g32p_row40_cosetGeneratorStep_0504 s
  · exact g32p_row40_cosetGeneratorStep_0505 s
  · exact g32p_row40_cosetGeneratorStep_0506 s
  · exact g32p_row40_cosetGeneratorStep_0507 s
  · exact g32p_row40_cosetGeneratorStep_0508 s
  · exact g32p_row40_cosetGeneratorStep_0509 s
  · exact g32p_row40_cosetGeneratorStep_0510 s
  · exact g32p_row40_cosetGeneratorStep_0511 s

theorem g32p_row40_cosetBranchBlock_0031 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row40_cosetBranchMatrices s) (g32p_row40_cosetRepresentatives (g32p_finBlockIndex 1080 31 r)) =
      HurwitzPrymRex_mmul (g32p_row40_cosetRepresentatives (g32p_row40_cosetBranchNext s (g32p_finBlockIndex 1080 31 r)))
        (g32p_row40_groupNodes (g32p_row40_cosetBranchFactor s (g32p_finBlockIndex 1080 31 r))) := by
  fin_cases r
  · exact g32p_row40_cosetBranchStep_0496 s
  · exact g32p_row40_cosetBranchStep_0497 s
  · exact g32p_row40_cosetBranchStep_0498 s
  · exact g32p_row40_cosetBranchStep_0499 s
  · exact g32p_row40_cosetBranchStep_0500 s
  · exact g32p_row40_cosetBranchStep_0501 s
  · exact g32p_row40_cosetBranchStep_0502 s
  · exact g32p_row40_cosetBranchStep_0503 s
  · exact g32p_row40_cosetBranchStep_0504 s
  · exact g32p_row40_cosetBranchStep_0505 s
  · exact g32p_row40_cosetBranchStep_0506 s
  · exact g32p_row40_cosetBranchStep_0507 s
  · exact g32p_row40_cosetBranchStep_0508 s
  · exact g32p_row40_cosetBranchStep_0509 s
  · exact g32p_row40_cosetBranchStep_0510 s
  · exact g32p_row40_cosetBranchStep_0511 s


end HodgeLean.Foundations.Program

end
