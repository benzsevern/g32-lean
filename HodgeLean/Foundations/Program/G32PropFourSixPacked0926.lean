import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness36CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0925
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow36
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0256 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 256) = g32p_row36_cosetRepresentatives 256 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 256) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 256))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 256)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 256) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 256))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 256)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0257 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 257) = g32p_row36_cosetRepresentatives 257 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 257))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 257)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 257) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 257))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 257)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0258 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 258) = g32p_row36_cosetRepresentatives 258 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 258) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 258))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 258)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 258) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 258))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 258)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0259 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 259) = g32p_row36_cosetRepresentatives 259 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 259) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 259))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 259)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 259) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 259))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 259)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0260 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 260) = g32p_row36_cosetRepresentatives 260 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 260) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 260))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 260)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 260) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 260))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 260)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0261 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 261) = g32p_row36_cosetRepresentatives 261 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 261) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 261))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 261)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 261) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 261))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 261)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0262 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 262) = g32p_row36_cosetRepresentatives 262 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 262) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 262))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 262)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 262) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 262))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 262)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0263 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 263) = g32p_row36_cosetRepresentatives 263 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 263) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 263))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 263)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 263) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 263))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 263)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0264 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 264) = g32p_row36_cosetRepresentatives 264 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 264) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 264))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 264)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 264) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 264))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 264)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0265 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 265) = g32p_row36_cosetRepresentatives 265 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 265) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 265))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 265)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 265) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 265))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 265)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0266 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 266) = g32p_row36_cosetRepresentatives 266 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 266) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 266))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 266)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 266) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 266))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 266)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0267 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 267) = g32p_row36_cosetRepresentatives 267 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 267) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 267))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 267)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 267) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 267))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 267)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0268 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 268) = g32p_row36_cosetRepresentatives 268 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 268))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 268)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 268) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 268))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 268)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0269 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 269) = g32p_row36_cosetRepresentatives 269 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 269) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 269))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 269)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 269) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 269))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 269)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0270 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 270) = g32p_row36_cosetRepresentatives 270 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 270) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 270))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 270)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 270) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 270))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 270)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0271 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 271) = g32p_row36_cosetRepresentatives 271 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 271) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 271))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 271)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 271) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 271))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 271)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0016 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 16 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 16 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0256
  · exact g32p_row36_cosetWord_0257
  · exact g32p_row36_cosetWord_0258
  · exact g32p_row36_cosetWord_0259
  · exact g32p_row36_cosetWord_0260
  · exact g32p_row36_cosetWord_0261
  · exact g32p_row36_cosetWord_0262
  · exact g32p_row36_cosetWord_0263
  · exact g32p_row36_cosetWord_0264
  · exact g32p_row36_cosetWord_0265
  · exact g32p_row36_cosetWord_0266
  · exact g32p_row36_cosetWord_0267
  · exact g32p_row36_cosetWord_0268
  · exact g32p_row36_cosetWord_0269
  · exact g32p_row36_cosetWord_0270
  · exact g32p_row36_cosetWord_0271

theorem g32p_row36_cosetGeneratorBlock_0016 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 16 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 16 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 16 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0256 s
  · exact g32p_row36_cosetGeneratorStep_0257 s
  · exact g32p_row36_cosetGeneratorStep_0258 s
  · exact g32p_row36_cosetGeneratorStep_0259 s
  · exact g32p_row36_cosetGeneratorStep_0260 s
  · exact g32p_row36_cosetGeneratorStep_0261 s
  · exact g32p_row36_cosetGeneratorStep_0262 s
  · exact g32p_row36_cosetGeneratorStep_0263 s
  · exact g32p_row36_cosetGeneratorStep_0264 s
  · exact g32p_row36_cosetGeneratorStep_0265 s
  · exact g32p_row36_cosetGeneratorStep_0266 s
  · exact g32p_row36_cosetGeneratorStep_0267 s
  · exact g32p_row36_cosetGeneratorStep_0268 s
  · exact g32p_row36_cosetGeneratorStep_0269 s
  · exact g32p_row36_cosetGeneratorStep_0270 s
  · exact g32p_row36_cosetGeneratorStep_0271 s

theorem g32p_row36_cosetBranchBlock_0016 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 16 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 16 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 16 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0256 s
  · exact g32p_row36_cosetBranchStep_0257 s
  · exact g32p_row36_cosetBranchStep_0258 s
  · exact g32p_row36_cosetBranchStep_0259 s
  · exact g32p_row36_cosetBranchStep_0260 s
  · exact g32p_row36_cosetBranchStep_0261 s
  · exact g32p_row36_cosetBranchStep_0262 s
  · exact g32p_row36_cosetBranchStep_0263 s
  · exact g32p_row36_cosetBranchStep_0264 s
  · exact g32p_row36_cosetBranchStep_0265 s
  · exact g32p_row36_cosetBranchStep_0266 s
  · exact g32p_row36_cosetBranchStep_0267 s
  · exact g32p_row36_cosetBranchStep_0268 s
  · exact g32p_row36_cosetBranchStep_0269 s
  · exact g32p_row36_cosetBranchStep_0270 s
  · exact g32p_row36_cosetBranchStep_0271 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0272 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 272) = g32p_row36_cosetRepresentatives 272 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 272) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 272))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 272)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 272) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 272))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 272)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0273 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 273) = g32p_row36_cosetRepresentatives 273 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 273) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 273))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 273)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 273) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 273))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 273)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0274 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 274) = g32p_row36_cosetRepresentatives 274 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 274) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 274))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 274)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 274) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 274))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 274)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0275 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 275) = g32p_row36_cosetRepresentatives 275 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 275) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 275))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 275)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 275) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 275))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 275)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0276 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 276) = g32p_row36_cosetRepresentatives 276 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 276) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 276))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 276)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 276) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 276))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 276)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0277 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 277) = g32p_row36_cosetRepresentatives 277 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 277) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 277))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 277)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 277) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 277))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 277)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0278 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 278) = g32p_row36_cosetRepresentatives 278 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 278) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 278))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 278)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 278) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 278))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 278)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0279 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 279) = g32p_row36_cosetRepresentatives 279 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 279) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 279))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 279)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 279) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 279))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 279)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0280 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 280) = g32p_row36_cosetRepresentatives 280 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 280) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 280))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 280)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 280) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 280))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 280)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0281 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 281) = g32p_row36_cosetRepresentatives 281 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 281) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 281))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 281)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 281) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 281))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 281)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0282 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 282) = g32p_row36_cosetRepresentatives 282 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 282) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 282))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 282)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 282) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 282))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 282)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0283 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 283) = g32p_row36_cosetRepresentatives 283 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 283) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 283))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 283)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 283) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 283))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 283)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0284 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 284) = g32p_row36_cosetRepresentatives 284 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 284) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 284))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 284)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 284) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 284))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 284)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0285 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 285) = g32p_row36_cosetRepresentatives 285 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 285) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 285))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 285)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 285) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 285))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 285)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0286 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 286) = g32p_row36_cosetRepresentatives 286 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 286) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 286))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 286)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 286) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 286))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 286)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0287 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 287) = g32p_row36_cosetRepresentatives 287 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 287) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 287))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 287)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 287) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 287))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 287)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0017 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 17 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 17 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0272
  · exact g32p_row36_cosetWord_0273
  · exact g32p_row36_cosetWord_0274
  · exact g32p_row36_cosetWord_0275
  · exact g32p_row36_cosetWord_0276
  · exact g32p_row36_cosetWord_0277
  · exact g32p_row36_cosetWord_0278
  · exact g32p_row36_cosetWord_0279
  · exact g32p_row36_cosetWord_0280
  · exact g32p_row36_cosetWord_0281
  · exact g32p_row36_cosetWord_0282
  · exact g32p_row36_cosetWord_0283
  · exact g32p_row36_cosetWord_0284
  · exact g32p_row36_cosetWord_0285
  · exact g32p_row36_cosetWord_0286
  · exact g32p_row36_cosetWord_0287

theorem g32p_row36_cosetGeneratorBlock_0017 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 17 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 17 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 17 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0272 s
  · exact g32p_row36_cosetGeneratorStep_0273 s
  · exact g32p_row36_cosetGeneratorStep_0274 s
  · exact g32p_row36_cosetGeneratorStep_0275 s
  · exact g32p_row36_cosetGeneratorStep_0276 s
  · exact g32p_row36_cosetGeneratorStep_0277 s
  · exact g32p_row36_cosetGeneratorStep_0278 s
  · exact g32p_row36_cosetGeneratorStep_0279 s
  · exact g32p_row36_cosetGeneratorStep_0280 s
  · exact g32p_row36_cosetGeneratorStep_0281 s
  · exact g32p_row36_cosetGeneratorStep_0282 s
  · exact g32p_row36_cosetGeneratorStep_0283 s
  · exact g32p_row36_cosetGeneratorStep_0284 s
  · exact g32p_row36_cosetGeneratorStep_0285 s
  · exact g32p_row36_cosetGeneratorStep_0286 s
  · exact g32p_row36_cosetGeneratorStep_0287 s

theorem g32p_row36_cosetBranchBlock_0017 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 17 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 17 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 17 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0272 s
  · exact g32p_row36_cosetBranchStep_0273 s
  · exact g32p_row36_cosetBranchStep_0274 s
  · exact g32p_row36_cosetBranchStep_0275 s
  · exact g32p_row36_cosetBranchStep_0276 s
  · exact g32p_row36_cosetBranchStep_0277 s
  · exact g32p_row36_cosetBranchStep_0278 s
  · exact g32p_row36_cosetBranchStep_0279 s
  · exact g32p_row36_cosetBranchStep_0280 s
  · exact g32p_row36_cosetBranchStep_0281 s
  · exact g32p_row36_cosetBranchStep_0282 s
  · exact g32p_row36_cosetBranchStep_0283 s
  · exact g32p_row36_cosetBranchStep_0284 s
  · exact g32p_row36_cosetBranchStep_0285 s
  · exact g32p_row36_cosetBranchStep_0286 s
  · exact g32p_row36_cosetBranchStep_0287 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0288 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 288) = g32p_row36_cosetRepresentatives 288 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 288) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 288))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 288)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 288) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 288))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 288)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0289 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 289) = g32p_row36_cosetRepresentatives 289 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 289) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 289))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 289)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 289) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 289))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 289)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0290 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 290) = g32p_row36_cosetRepresentatives 290 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 290) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 290))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 290)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 290) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 290))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 290)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0291 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 291) = g32p_row36_cosetRepresentatives 291 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 291) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 291))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 291)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 291) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 291))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 291)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0292 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 292) = g32p_row36_cosetRepresentatives 292 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 292) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 292))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 292)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 292) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 292))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 292)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0293 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 293) = g32p_row36_cosetRepresentatives 293 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 293) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 293))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 293)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 293) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 293))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 293)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0294 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 294) = g32p_row36_cosetRepresentatives 294 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 294) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 294))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 294)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 294) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 294))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 294)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0295 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 295) = g32p_row36_cosetRepresentatives 295 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 295) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 295))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 295)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 295) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 295))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 295)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0296 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 296) = g32p_row36_cosetRepresentatives 296 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 296) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 296))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 296)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 296) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 296))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 296)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0297 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 297) = g32p_row36_cosetRepresentatives 297 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 297) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 297))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 297)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 297) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 297))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 297)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0298 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 298) = g32p_row36_cosetRepresentatives 298 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 298) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 298))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 298)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 298) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 298))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 298)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0299 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 299) = g32p_row36_cosetRepresentatives 299 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 299) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 299))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 299)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 299) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 299))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 299)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0300 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 300) = g32p_row36_cosetRepresentatives 300 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 300) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 300))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 300)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 300) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 300))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 300)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0301 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 301) = g32p_row36_cosetRepresentatives 301 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 301) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 301))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 301)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 301) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 301))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 301)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0302 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 302) = g32p_row36_cosetRepresentatives 302 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 302) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 302))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 302)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 302) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 302))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 302)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0303 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 303) = g32p_row36_cosetRepresentatives 303 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 303) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 303))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 303)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 303) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 303))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 303)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0018 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 18 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 18 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0288
  · exact g32p_row36_cosetWord_0289
  · exact g32p_row36_cosetWord_0290
  · exact g32p_row36_cosetWord_0291
  · exact g32p_row36_cosetWord_0292
  · exact g32p_row36_cosetWord_0293
  · exact g32p_row36_cosetWord_0294
  · exact g32p_row36_cosetWord_0295
  · exact g32p_row36_cosetWord_0296
  · exact g32p_row36_cosetWord_0297
  · exact g32p_row36_cosetWord_0298
  · exact g32p_row36_cosetWord_0299
  · exact g32p_row36_cosetWord_0300
  · exact g32p_row36_cosetWord_0301
  · exact g32p_row36_cosetWord_0302
  · exact g32p_row36_cosetWord_0303

theorem g32p_row36_cosetGeneratorBlock_0018 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 18 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 18 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 18 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0288 s
  · exact g32p_row36_cosetGeneratorStep_0289 s
  · exact g32p_row36_cosetGeneratorStep_0290 s
  · exact g32p_row36_cosetGeneratorStep_0291 s
  · exact g32p_row36_cosetGeneratorStep_0292 s
  · exact g32p_row36_cosetGeneratorStep_0293 s
  · exact g32p_row36_cosetGeneratorStep_0294 s
  · exact g32p_row36_cosetGeneratorStep_0295 s
  · exact g32p_row36_cosetGeneratorStep_0296 s
  · exact g32p_row36_cosetGeneratorStep_0297 s
  · exact g32p_row36_cosetGeneratorStep_0298 s
  · exact g32p_row36_cosetGeneratorStep_0299 s
  · exact g32p_row36_cosetGeneratorStep_0300 s
  · exact g32p_row36_cosetGeneratorStep_0301 s
  · exact g32p_row36_cosetGeneratorStep_0302 s
  · exact g32p_row36_cosetGeneratorStep_0303 s

theorem g32p_row36_cosetBranchBlock_0018 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 18 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 18 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 18 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0288 s
  · exact g32p_row36_cosetBranchStep_0289 s
  · exact g32p_row36_cosetBranchStep_0290 s
  · exact g32p_row36_cosetBranchStep_0291 s
  · exact g32p_row36_cosetBranchStep_0292 s
  · exact g32p_row36_cosetBranchStep_0293 s
  · exact g32p_row36_cosetBranchStep_0294 s
  · exact g32p_row36_cosetBranchStep_0295 s
  · exact g32p_row36_cosetBranchStep_0296 s
  · exact g32p_row36_cosetBranchStep_0297 s
  · exact g32p_row36_cosetBranchStep_0298 s
  · exact g32p_row36_cosetBranchStep_0299 s
  · exact g32p_row36_cosetBranchStep_0300 s
  · exact g32p_row36_cosetBranchStep_0301 s
  · exact g32p_row36_cosetBranchStep_0302 s
  · exact g32p_row36_cosetBranchStep_0303 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0304 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 304) = g32p_row36_cosetRepresentatives 304 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 304) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 304))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 304)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 304) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 304))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 304)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0305 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 305) = g32p_row36_cosetRepresentatives 305 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 305) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 305))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 305)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 305) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 305))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 305)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0306 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 306) = g32p_row36_cosetRepresentatives 306 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 306) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 306))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 306)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 306) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 306))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 306)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0307 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 307) = g32p_row36_cosetRepresentatives 307 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 307) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 307))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 307)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 307) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 307))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 307)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0308 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 308) = g32p_row36_cosetRepresentatives 308 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 308) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 308))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 308)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 308) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 308))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 308)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0309 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 309) = g32p_row36_cosetRepresentatives 309 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 309) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 309))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 309)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 309) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 309))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 309)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0310 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 310) = g32p_row36_cosetRepresentatives 310 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 310) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 310))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 310)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 310) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 310))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 310)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0311 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 311) = g32p_row36_cosetRepresentatives 311 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 311) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 311))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 311)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 311) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 311))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 311)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0312 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 312) = g32p_row36_cosetRepresentatives 312 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 312) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 312))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 312)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 312) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 312))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 312)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0313 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 313) = g32p_row36_cosetRepresentatives 313 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 313) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 313))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 313)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 313) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 313))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 313)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0314 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 314) = g32p_row36_cosetRepresentatives 314 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 314) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 314))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 314)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 314) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 314))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 314)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0315 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 315) = g32p_row36_cosetRepresentatives 315 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 315) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 315))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 315)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 315) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 315))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 315)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0316 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 316) = g32p_row36_cosetRepresentatives 316 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 316) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 316))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 316)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 316) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 316))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 316)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0317 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 317) = g32p_row36_cosetRepresentatives 317 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 317) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 317))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 317)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 317) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 317))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 317)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0318 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 318) = g32p_row36_cosetRepresentatives 318 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 318) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 318))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 318)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 318) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 318))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 318)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0319 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 319) = g32p_row36_cosetRepresentatives 319 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 319) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 319))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 319)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 319) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 319))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 319)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0019 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 19 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 19 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0304
  · exact g32p_row36_cosetWord_0305
  · exact g32p_row36_cosetWord_0306
  · exact g32p_row36_cosetWord_0307
  · exact g32p_row36_cosetWord_0308
  · exact g32p_row36_cosetWord_0309
  · exact g32p_row36_cosetWord_0310
  · exact g32p_row36_cosetWord_0311
  · exact g32p_row36_cosetWord_0312
  · exact g32p_row36_cosetWord_0313
  · exact g32p_row36_cosetWord_0314
  · exact g32p_row36_cosetWord_0315
  · exact g32p_row36_cosetWord_0316
  · exact g32p_row36_cosetWord_0317
  · exact g32p_row36_cosetWord_0318
  · exact g32p_row36_cosetWord_0319

theorem g32p_row36_cosetGeneratorBlock_0019 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 19 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 19 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 19 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0304 s
  · exact g32p_row36_cosetGeneratorStep_0305 s
  · exact g32p_row36_cosetGeneratorStep_0306 s
  · exact g32p_row36_cosetGeneratorStep_0307 s
  · exact g32p_row36_cosetGeneratorStep_0308 s
  · exact g32p_row36_cosetGeneratorStep_0309 s
  · exact g32p_row36_cosetGeneratorStep_0310 s
  · exact g32p_row36_cosetGeneratorStep_0311 s
  · exact g32p_row36_cosetGeneratorStep_0312 s
  · exact g32p_row36_cosetGeneratorStep_0313 s
  · exact g32p_row36_cosetGeneratorStep_0314 s
  · exact g32p_row36_cosetGeneratorStep_0315 s
  · exact g32p_row36_cosetGeneratorStep_0316 s
  · exact g32p_row36_cosetGeneratorStep_0317 s
  · exact g32p_row36_cosetGeneratorStep_0318 s
  · exact g32p_row36_cosetGeneratorStep_0319 s

theorem g32p_row36_cosetBranchBlock_0019 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 19 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 19 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 19 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0304 s
  · exact g32p_row36_cosetBranchStep_0305 s
  · exact g32p_row36_cosetBranchStep_0306 s
  · exact g32p_row36_cosetBranchStep_0307 s
  · exact g32p_row36_cosetBranchStep_0308 s
  · exact g32p_row36_cosetBranchStep_0309 s
  · exact g32p_row36_cosetBranchStep_0310 s
  · exact g32p_row36_cosetBranchStep_0311 s
  · exact g32p_row36_cosetBranchStep_0312 s
  · exact g32p_row36_cosetBranchStep_0313 s
  · exact g32p_row36_cosetBranchStep_0314 s
  · exact g32p_row36_cosetBranchStep_0315 s
  · exact g32p_row36_cosetBranchStep_0316 s
  · exact g32p_row36_cosetBranchStep_0317 s
  · exact g32p_row36_cosetBranchStep_0318 s
  · exact g32p_row36_cosetBranchStep_0319 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0320 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 320) = g32p_row36_cosetRepresentatives 320 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 320) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 320))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 320)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 320) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 320))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 320)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0321 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 321) = g32p_row36_cosetRepresentatives 321 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 321) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 321))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 321)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 321) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 321))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 321)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0322 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 322) = g32p_row36_cosetRepresentatives 322 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 322) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 322))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 322)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 322) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 322))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 322)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0323 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 323) = g32p_row36_cosetRepresentatives 323 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 323) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 323))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 323)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 323) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 323))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 323)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0324 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 324) = g32p_row36_cosetRepresentatives 324 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 324) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 324))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 324)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 324) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 324))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 324)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0325 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 325) = g32p_row36_cosetRepresentatives 325 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 325) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 325))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 325)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 325) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 325))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 325)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0326 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 326) = g32p_row36_cosetRepresentatives 326 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 326) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 326))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 326)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 326) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 326))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 326)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0327 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 327) = g32p_row36_cosetRepresentatives 327 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 327) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 327))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 327)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 327) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 327))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 327)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0328 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 328) = g32p_row36_cosetRepresentatives 328 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0328 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 328) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 328))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 328)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0328 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 328) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 328))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 328)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0329 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 329) = g32p_row36_cosetRepresentatives 329 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0329 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 329) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 329))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 329)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0329 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 329) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 329))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 329)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0330 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 330) = g32p_row36_cosetRepresentatives 330 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0330 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 330) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 330))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 330)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0330 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 330) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 330))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 330)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0331 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 331) = g32p_row36_cosetRepresentatives 331 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0331 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 331) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 331))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 331)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0331 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 331) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 331))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 331)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0332 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 332) = g32p_row36_cosetRepresentatives 332 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0332 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 332) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 332))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 332)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0332 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 332) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 332))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 332)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0333 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 333) = g32p_row36_cosetRepresentatives 333 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0333 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 333) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 333))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 333)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0333 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 333) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 333))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 333)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0334 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 334) = g32p_row36_cosetRepresentatives 334 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0334 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 334) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 334))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 334)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0334 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 334) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 334))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 334)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0335 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 335) = g32p_row36_cosetRepresentatives 335 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0335 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 335) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 335))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 335)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0335 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 335) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 335))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 335)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0020 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 20 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 20 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0320
  · exact g32p_row36_cosetWord_0321
  · exact g32p_row36_cosetWord_0322
  · exact g32p_row36_cosetWord_0323
  · exact g32p_row36_cosetWord_0324
  · exact g32p_row36_cosetWord_0325
  · exact g32p_row36_cosetWord_0326
  · exact g32p_row36_cosetWord_0327
  · exact g32p_row36_cosetWord_0328
  · exact g32p_row36_cosetWord_0329
  · exact g32p_row36_cosetWord_0330
  · exact g32p_row36_cosetWord_0331
  · exact g32p_row36_cosetWord_0332
  · exact g32p_row36_cosetWord_0333
  · exact g32p_row36_cosetWord_0334
  · exact g32p_row36_cosetWord_0335

theorem g32p_row36_cosetGeneratorBlock_0020 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 20 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 20 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 20 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0320 s
  · exact g32p_row36_cosetGeneratorStep_0321 s
  · exact g32p_row36_cosetGeneratorStep_0322 s
  · exact g32p_row36_cosetGeneratorStep_0323 s
  · exact g32p_row36_cosetGeneratorStep_0324 s
  · exact g32p_row36_cosetGeneratorStep_0325 s
  · exact g32p_row36_cosetGeneratorStep_0326 s
  · exact g32p_row36_cosetGeneratorStep_0327 s
  · exact g32p_row36_cosetGeneratorStep_0328 s
  · exact g32p_row36_cosetGeneratorStep_0329 s
  · exact g32p_row36_cosetGeneratorStep_0330 s
  · exact g32p_row36_cosetGeneratorStep_0331 s
  · exact g32p_row36_cosetGeneratorStep_0332 s
  · exact g32p_row36_cosetGeneratorStep_0333 s
  · exact g32p_row36_cosetGeneratorStep_0334 s
  · exact g32p_row36_cosetGeneratorStep_0335 s

theorem g32p_row36_cosetBranchBlock_0020 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 20 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 20 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 20 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0320 s
  · exact g32p_row36_cosetBranchStep_0321 s
  · exact g32p_row36_cosetBranchStep_0322 s
  · exact g32p_row36_cosetBranchStep_0323 s
  · exact g32p_row36_cosetBranchStep_0324 s
  · exact g32p_row36_cosetBranchStep_0325 s
  · exact g32p_row36_cosetBranchStep_0326 s
  · exact g32p_row36_cosetBranchStep_0327 s
  · exact g32p_row36_cosetBranchStep_0328 s
  · exact g32p_row36_cosetBranchStep_0329 s
  · exact g32p_row36_cosetBranchStep_0330 s
  · exact g32p_row36_cosetBranchStep_0331 s
  · exact g32p_row36_cosetBranchStep_0332 s
  · exact g32p_row36_cosetBranchStep_0333 s
  · exact g32p_row36_cosetBranchStep_0334 s
  · exact g32p_row36_cosetBranchStep_0335 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0336 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 336) = g32p_row36_cosetRepresentatives 336 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0336 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 336) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 336))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 336)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0336 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 336) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 336))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 336)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0337 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 337) = g32p_row36_cosetRepresentatives 337 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0337 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 337) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 337))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 337)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0337 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 337) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 337))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 337)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0338 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 338) = g32p_row36_cosetRepresentatives 338 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0338 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 338) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 338))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 338)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0338 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 338) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 338))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 338)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0339 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 339) = g32p_row36_cosetRepresentatives 339 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0339 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 339) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 339))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 339)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0339 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 339) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 339))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 339)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0340 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 340) = g32p_row36_cosetRepresentatives 340 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0340 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 340) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 340))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 340)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0340 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 340) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 340))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 340)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0341 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 341) = g32p_row36_cosetRepresentatives 341 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0341 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 341) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 341))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 341)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0341 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 341) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 341))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 341)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0342 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 342) = g32p_row36_cosetRepresentatives 342 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0342 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 342) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 342))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 342)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0342 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 342) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 342))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 342)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0343 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 343) = g32p_row36_cosetRepresentatives 343 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0343 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 343) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 343))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 343)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0343 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 343) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 343))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 343)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0344 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 344) = g32p_row36_cosetRepresentatives 344 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0344 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 344) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 344))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 344)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0344 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 344) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 344))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 344)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0345 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 345) = g32p_row36_cosetRepresentatives 345 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0345 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 345) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 345))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 345)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0345 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 345) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 345))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 345)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0346 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 346) = g32p_row36_cosetRepresentatives 346 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0346 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 346) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 346))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 346)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0346 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 346) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 346))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 346)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0347 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 347) = g32p_row36_cosetRepresentatives 347 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0347 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 347) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 347))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 347)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0347 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 347) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 347))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 347)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0348 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 348) = g32p_row36_cosetRepresentatives 348 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0348 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 348) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 348))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 348)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0348 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 348) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 348))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 348)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0349 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 349) = g32p_row36_cosetRepresentatives 349 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0349 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 349) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 349))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 349)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0349 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 349) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 349))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 349)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0350 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 350) = g32p_row36_cosetRepresentatives 350 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0350 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 350) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 350))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 350)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0350 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 350) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 350))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 350)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0351 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 351) = g32p_row36_cosetRepresentatives 351 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0351 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 351) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 351))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 351)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0351 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 351) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 351))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 351)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0021 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 21 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 21 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0336
  · exact g32p_row36_cosetWord_0337
  · exact g32p_row36_cosetWord_0338
  · exact g32p_row36_cosetWord_0339
  · exact g32p_row36_cosetWord_0340
  · exact g32p_row36_cosetWord_0341
  · exact g32p_row36_cosetWord_0342
  · exact g32p_row36_cosetWord_0343
  · exact g32p_row36_cosetWord_0344
  · exact g32p_row36_cosetWord_0345
  · exact g32p_row36_cosetWord_0346
  · exact g32p_row36_cosetWord_0347
  · exact g32p_row36_cosetWord_0348
  · exact g32p_row36_cosetWord_0349
  · exact g32p_row36_cosetWord_0350
  · exact g32p_row36_cosetWord_0351

theorem g32p_row36_cosetGeneratorBlock_0021 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 21 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 21 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 21 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0336 s
  · exact g32p_row36_cosetGeneratorStep_0337 s
  · exact g32p_row36_cosetGeneratorStep_0338 s
  · exact g32p_row36_cosetGeneratorStep_0339 s
  · exact g32p_row36_cosetGeneratorStep_0340 s
  · exact g32p_row36_cosetGeneratorStep_0341 s
  · exact g32p_row36_cosetGeneratorStep_0342 s
  · exact g32p_row36_cosetGeneratorStep_0343 s
  · exact g32p_row36_cosetGeneratorStep_0344 s
  · exact g32p_row36_cosetGeneratorStep_0345 s
  · exact g32p_row36_cosetGeneratorStep_0346 s
  · exact g32p_row36_cosetGeneratorStep_0347 s
  · exact g32p_row36_cosetGeneratorStep_0348 s
  · exact g32p_row36_cosetGeneratorStep_0349 s
  · exact g32p_row36_cosetGeneratorStep_0350 s
  · exact g32p_row36_cosetGeneratorStep_0351 s

theorem g32p_row36_cosetBranchBlock_0021 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 21 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 21 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 21 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0336 s
  · exact g32p_row36_cosetBranchStep_0337 s
  · exact g32p_row36_cosetBranchStep_0338 s
  · exact g32p_row36_cosetBranchStep_0339 s
  · exact g32p_row36_cosetBranchStep_0340 s
  · exact g32p_row36_cosetBranchStep_0341 s
  · exact g32p_row36_cosetBranchStep_0342 s
  · exact g32p_row36_cosetBranchStep_0343 s
  · exact g32p_row36_cosetBranchStep_0344 s
  · exact g32p_row36_cosetBranchStep_0345 s
  · exact g32p_row36_cosetBranchStep_0346 s
  · exact g32p_row36_cosetBranchStep_0347 s
  · exact g32p_row36_cosetBranchStep_0348 s
  · exact g32p_row36_cosetBranchStep_0349 s
  · exact g32p_row36_cosetBranchStep_0350 s
  · exact g32p_row36_cosetBranchStep_0351 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0352 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 352) = g32p_row36_cosetRepresentatives 352 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0352 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 352) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 352))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 352)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0352 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 352) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 352))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 352)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0353 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 353) = g32p_row36_cosetRepresentatives 353 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0353 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 353) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 353))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 353)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0353 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 353) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 353))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 353)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0354 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 354) = g32p_row36_cosetRepresentatives 354 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0354 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 354) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 354))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 354)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0354 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 354) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 354))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 354)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0355 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 355) = g32p_row36_cosetRepresentatives 355 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0355 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 355) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 355))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 355)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0355 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 355) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 355))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 355)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0356 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 356) = g32p_row36_cosetRepresentatives 356 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0356 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 356) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 356))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 356)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0356 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 356) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 356))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 356)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0357 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 357) = g32p_row36_cosetRepresentatives 357 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0357 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 357) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 357))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 357)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0357 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 357) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 357))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 357)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0358 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 358) = g32p_row36_cosetRepresentatives 358 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0358 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 358) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 358))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 358)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0358 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 358) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 358))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 358)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0359 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 359) = g32p_row36_cosetRepresentatives 359 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0359 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 359) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 359))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 359)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0359 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 359) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 359))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 359)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0360 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 360) = g32p_row36_cosetRepresentatives 360 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0360 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 360) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 360))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 360)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0360 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 360) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 360))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 360)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0361 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 361) = g32p_row36_cosetRepresentatives 361 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0361 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 361) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 361))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 361)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0361 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 361) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 361))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 361)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0362 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 362) = g32p_row36_cosetRepresentatives 362 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0362 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 362) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 362))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 362)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0362 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 362) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 362))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 362)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0363 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 363) = g32p_row36_cosetRepresentatives 363 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0363 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 363) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 363))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 363)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0363 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 363) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 363))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 363)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0364 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 364) = g32p_row36_cosetRepresentatives 364 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0364 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 364) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 364))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 364)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0364 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 364) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 364))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 364)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0365 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 365) = g32p_row36_cosetRepresentatives 365 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0365 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 365) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 365))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 365)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0365 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 365) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 365))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 365)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0366 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 366) = g32p_row36_cosetRepresentatives 366 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0366 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 366) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 366))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 366)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0366 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 366) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 366))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 366)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0367 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 367) = g32p_row36_cosetRepresentatives 367 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0367 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 367) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 367))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 367)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0367 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 367) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 367))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 367)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0022 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 22 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 22 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0352
  · exact g32p_row36_cosetWord_0353
  · exact g32p_row36_cosetWord_0354
  · exact g32p_row36_cosetWord_0355
  · exact g32p_row36_cosetWord_0356
  · exact g32p_row36_cosetWord_0357
  · exact g32p_row36_cosetWord_0358
  · exact g32p_row36_cosetWord_0359
  · exact g32p_row36_cosetWord_0360
  · exact g32p_row36_cosetWord_0361
  · exact g32p_row36_cosetWord_0362
  · exact g32p_row36_cosetWord_0363
  · exact g32p_row36_cosetWord_0364
  · exact g32p_row36_cosetWord_0365
  · exact g32p_row36_cosetWord_0366
  · exact g32p_row36_cosetWord_0367

theorem g32p_row36_cosetGeneratorBlock_0022 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 22 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 22 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 22 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0352 s
  · exact g32p_row36_cosetGeneratorStep_0353 s
  · exact g32p_row36_cosetGeneratorStep_0354 s
  · exact g32p_row36_cosetGeneratorStep_0355 s
  · exact g32p_row36_cosetGeneratorStep_0356 s
  · exact g32p_row36_cosetGeneratorStep_0357 s
  · exact g32p_row36_cosetGeneratorStep_0358 s
  · exact g32p_row36_cosetGeneratorStep_0359 s
  · exact g32p_row36_cosetGeneratorStep_0360 s
  · exact g32p_row36_cosetGeneratorStep_0361 s
  · exact g32p_row36_cosetGeneratorStep_0362 s
  · exact g32p_row36_cosetGeneratorStep_0363 s
  · exact g32p_row36_cosetGeneratorStep_0364 s
  · exact g32p_row36_cosetGeneratorStep_0365 s
  · exact g32p_row36_cosetGeneratorStep_0366 s
  · exact g32p_row36_cosetGeneratorStep_0367 s

theorem g32p_row36_cosetBranchBlock_0022 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 22 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 22 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 22 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0352 s
  · exact g32p_row36_cosetBranchStep_0353 s
  · exact g32p_row36_cosetBranchStep_0354 s
  · exact g32p_row36_cosetBranchStep_0355 s
  · exact g32p_row36_cosetBranchStep_0356 s
  · exact g32p_row36_cosetBranchStep_0357 s
  · exact g32p_row36_cosetBranchStep_0358 s
  · exact g32p_row36_cosetBranchStep_0359 s
  · exact g32p_row36_cosetBranchStep_0360 s
  · exact g32p_row36_cosetBranchStep_0361 s
  · exact g32p_row36_cosetBranchStep_0362 s
  · exact g32p_row36_cosetBranchStep_0363 s
  · exact g32p_row36_cosetBranchStep_0364 s
  · exact g32p_row36_cosetBranchStep_0365 s
  · exact g32p_row36_cosetBranchStep_0366 s
  · exact g32p_row36_cosetBranchStep_0367 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0368 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 368) = g32p_row36_cosetRepresentatives 368 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0368 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 368) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 368))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 368)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0368 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 368) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 368))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 368)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0369 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 369) = g32p_row36_cosetRepresentatives 369 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0369 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 369) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 369))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 369)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0369 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 369) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 369))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 369)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0370 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 370) = g32p_row36_cosetRepresentatives 370 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0370 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 370) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 370))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 370)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0370 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 370) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 370))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 370)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0371 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 371) = g32p_row36_cosetRepresentatives 371 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0371 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 371) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 371))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 371)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0371 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 371) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 371))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 371)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0372 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 372) = g32p_row36_cosetRepresentatives 372 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0372 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 372) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 372))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 372)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0372 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 372) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 372))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 372)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0373 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 373) = g32p_row36_cosetRepresentatives 373 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0373 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 373) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 373))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 373)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0373 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 373) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 373))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 373)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0374 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 374) = g32p_row36_cosetRepresentatives 374 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0374 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 374) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 374))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 374)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0374 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 374) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 374))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 374)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0375 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 375) = g32p_row36_cosetRepresentatives 375 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0375 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 375) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 375))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 375)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0375 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 375) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 375))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 375)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0376 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 376) = g32p_row36_cosetRepresentatives 376 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0376 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 376) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 376))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 376)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0376 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 376) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 376))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 376)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0377 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 377) = g32p_row36_cosetRepresentatives 377 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0377 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 377) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 377))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 377)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0377 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 377) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 377))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 377)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0378 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 378) = g32p_row36_cosetRepresentatives 378 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0378 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 378) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 378))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 378)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0378 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 378) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 378))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 378)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0379 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 379) = g32p_row36_cosetRepresentatives 379 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0379 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 379) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 379))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 379)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0379 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 379) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 379))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 379)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0380 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 380) = g32p_row36_cosetRepresentatives 380 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0380 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 380) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 380))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 380)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0380 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 380) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 380))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 380)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0381 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 381) = g32p_row36_cosetRepresentatives 381 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0381 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 381) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 381))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 381)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0381 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 381) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 381))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 381)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0382 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 382) = g32p_row36_cosetRepresentatives 382 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0382 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 382) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 382))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 382)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0382 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 382) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 382))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 382)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0383 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 383) = g32p_row36_cosetRepresentatives 383 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0383 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 383) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 383))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 383)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0383 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 383) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 383))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 383)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0023 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 23 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 23 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0368
  · exact g32p_row36_cosetWord_0369
  · exact g32p_row36_cosetWord_0370
  · exact g32p_row36_cosetWord_0371
  · exact g32p_row36_cosetWord_0372
  · exact g32p_row36_cosetWord_0373
  · exact g32p_row36_cosetWord_0374
  · exact g32p_row36_cosetWord_0375
  · exact g32p_row36_cosetWord_0376
  · exact g32p_row36_cosetWord_0377
  · exact g32p_row36_cosetWord_0378
  · exact g32p_row36_cosetWord_0379
  · exact g32p_row36_cosetWord_0380
  · exact g32p_row36_cosetWord_0381
  · exact g32p_row36_cosetWord_0382
  · exact g32p_row36_cosetWord_0383

theorem g32p_row36_cosetGeneratorBlock_0023 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 23 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 23 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 23 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0368 s
  · exact g32p_row36_cosetGeneratorStep_0369 s
  · exact g32p_row36_cosetGeneratorStep_0370 s
  · exact g32p_row36_cosetGeneratorStep_0371 s
  · exact g32p_row36_cosetGeneratorStep_0372 s
  · exact g32p_row36_cosetGeneratorStep_0373 s
  · exact g32p_row36_cosetGeneratorStep_0374 s
  · exact g32p_row36_cosetGeneratorStep_0375 s
  · exact g32p_row36_cosetGeneratorStep_0376 s
  · exact g32p_row36_cosetGeneratorStep_0377 s
  · exact g32p_row36_cosetGeneratorStep_0378 s
  · exact g32p_row36_cosetGeneratorStep_0379 s
  · exact g32p_row36_cosetGeneratorStep_0380 s
  · exact g32p_row36_cosetGeneratorStep_0381 s
  · exact g32p_row36_cosetGeneratorStep_0382 s
  · exact g32p_row36_cosetGeneratorStep_0383 s

theorem g32p_row36_cosetBranchBlock_0023 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 23 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 23 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 23 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0368 s
  · exact g32p_row36_cosetBranchStep_0369 s
  · exact g32p_row36_cosetBranchStep_0370 s
  · exact g32p_row36_cosetBranchStep_0371 s
  · exact g32p_row36_cosetBranchStep_0372 s
  · exact g32p_row36_cosetBranchStep_0373 s
  · exact g32p_row36_cosetBranchStep_0374 s
  · exact g32p_row36_cosetBranchStep_0375 s
  · exact g32p_row36_cosetBranchStep_0376 s
  · exact g32p_row36_cosetBranchStep_0377 s
  · exact g32p_row36_cosetBranchStep_0378 s
  · exact g32p_row36_cosetBranchStep_0379 s
  · exact g32p_row36_cosetBranchStep_0380 s
  · exact g32p_row36_cosetBranchStep_0381 s
  · exact g32p_row36_cosetBranchStep_0382 s
  · exact g32p_row36_cosetBranchStep_0383 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0384 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 384) = g32p_row36_cosetRepresentatives 384 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0384 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 384) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 384))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 384)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0384 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 384) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 384))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 384)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0385 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 385) = g32p_row36_cosetRepresentatives 385 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0385 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 385) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 385))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 385)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0385 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 385) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 385))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 385)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0386 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 386) = g32p_row36_cosetRepresentatives 386 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0386 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 386) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 386))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 386)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0386 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 386) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 386))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 386)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0387 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 387) = g32p_row36_cosetRepresentatives 387 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0387 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 387) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 387))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 387)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0387 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 387) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 387))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 387)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0388 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 388) = g32p_row36_cosetRepresentatives 388 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0388 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 388) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 388))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 388)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0388 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 388) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 388))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 388)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0389 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 389) = g32p_row36_cosetRepresentatives 389 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0389 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 389) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 389))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 389)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0389 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 389) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 389))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 389)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0390 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 390) = g32p_row36_cosetRepresentatives 390 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0390 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 390) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 390))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 390)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0390 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 390) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 390))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 390)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0391 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 391) = g32p_row36_cosetRepresentatives 391 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0391 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 391) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 391))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 391)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0391 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 391) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 391))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 391)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0392 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 392) = g32p_row36_cosetRepresentatives 392 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0392 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 392) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 392))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 392)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0392 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 392) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 392))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 392)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0393 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 393) = g32p_row36_cosetRepresentatives 393 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0393 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 393) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 393))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 393)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0393 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 393) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 393))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 393)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0394 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 394) = g32p_row36_cosetRepresentatives 394 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0394 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 394) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 394))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 394)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0394 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 394) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 394))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 394)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0395 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 395) = g32p_row36_cosetRepresentatives 395 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0395 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 395) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 395))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 395)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0395 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 395) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 395))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 395)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0396 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 396) = g32p_row36_cosetRepresentatives 396 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0396 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 396) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 396))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 396)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0396 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 396) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 396))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 396)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0397 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 397) = g32p_row36_cosetRepresentatives 397 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0397 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 397) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 397))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 397)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0397 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 397) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 397))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 397)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0398 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 398) = g32p_row36_cosetRepresentatives 398 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0398 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 398) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 398))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 398)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0398 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 398) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 398))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 398)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0399 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 399) = g32p_row36_cosetRepresentatives 399 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0399 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 399) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 399))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 399)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0399 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 399) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 399))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 399)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0024 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 24 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 24 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0384
  · exact g32p_row36_cosetWord_0385
  · exact g32p_row36_cosetWord_0386
  · exact g32p_row36_cosetWord_0387
  · exact g32p_row36_cosetWord_0388
  · exact g32p_row36_cosetWord_0389
  · exact g32p_row36_cosetWord_0390
  · exact g32p_row36_cosetWord_0391
  · exact g32p_row36_cosetWord_0392
  · exact g32p_row36_cosetWord_0393
  · exact g32p_row36_cosetWord_0394
  · exact g32p_row36_cosetWord_0395
  · exact g32p_row36_cosetWord_0396
  · exact g32p_row36_cosetWord_0397
  · exact g32p_row36_cosetWord_0398
  · exact g32p_row36_cosetWord_0399

theorem g32p_row36_cosetGeneratorBlock_0024 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 24 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 24 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 24 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0384 s
  · exact g32p_row36_cosetGeneratorStep_0385 s
  · exact g32p_row36_cosetGeneratorStep_0386 s
  · exact g32p_row36_cosetGeneratorStep_0387 s
  · exact g32p_row36_cosetGeneratorStep_0388 s
  · exact g32p_row36_cosetGeneratorStep_0389 s
  · exact g32p_row36_cosetGeneratorStep_0390 s
  · exact g32p_row36_cosetGeneratorStep_0391 s
  · exact g32p_row36_cosetGeneratorStep_0392 s
  · exact g32p_row36_cosetGeneratorStep_0393 s
  · exact g32p_row36_cosetGeneratorStep_0394 s
  · exact g32p_row36_cosetGeneratorStep_0395 s
  · exact g32p_row36_cosetGeneratorStep_0396 s
  · exact g32p_row36_cosetGeneratorStep_0397 s
  · exact g32p_row36_cosetGeneratorStep_0398 s
  · exact g32p_row36_cosetGeneratorStep_0399 s

theorem g32p_row36_cosetBranchBlock_0024 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 24 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 24 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 24 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0384 s
  · exact g32p_row36_cosetBranchStep_0385 s
  · exact g32p_row36_cosetBranchStep_0386 s
  · exact g32p_row36_cosetBranchStep_0387 s
  · exact g32p_row36_cosetBranchStep_0388 s
  · exact g32p_row36_cosetBranchStep_0389 s
  · exact g32p_row36_cosetBranchStep_0390 s
  · exact g32p_row36_cosetBranchStep_0391 s
  · exact g32p_row36_cosetBranchStep_0392 s
  · exact g32p_row36_cosetBranchStep_0393 s
  · exact g32p_row36_cosetBranchStep_0394 s
  · exact g32p_row36_cosetBranchStep_0395 s
  · exact g32p_row36_cosetBranchStep_0396 s
  · exact g32p_row36_cosetBranchStep_0397 s
  · exact g32p_row36_cosetBranchStep_0398 s
  · exact g32p_row36_cosetBranchStep_0399 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetWord_0400 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 400) = g32p_row36_cosetRepresentatives 400 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0400 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 400) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 400))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 400)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0400 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 400) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 400))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 400)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0401 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 401) = g32p_row36_cosetRepresentatives 401 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0401 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 401) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 401))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 401)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0401 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 401) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 401))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 401)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0402 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 402) = g32p_row36_cosetRepresentatives 402 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0402 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 402) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 402))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 402)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0402 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 402) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 402))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 402)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0403 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 403) = g32p_row36_cosetRepresentatives 403 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0403 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 403) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 403))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 403)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0403 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 403) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 403))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 403)) := by
  decide +kernel

theorem g32p_row36_cosetWord_0404 :
    g32p_archiveIntegralWord (g32p_row36_cosetWords 404) = g32p_row36_cosetRepresentatives 404 := by
  decide +kernel

theorem g32p_row36_cosetGeneratorStep_0404 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives 404) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s 404))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s 404)) := by
  decide +kernel

theorem g32p_row36_cosetBranchStep_0404 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives 404) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s 404))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s 404)) := by
  decide +kernel

theorem g32p_row36_cosetWordBlock_0025 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords (g32p_finBlockIndex 405 25 r)) = g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 25 r) := by
  fin_cases r
  · exact g32p_row36_cosetWord_0400
  · exact g32p_row36_cosetWord_0401
  · exact g32p_row36_cosetWord_0402
  · exact g32p_row36_cosetWord_0403
  · exact g32p_row36_cosetWord_0404
  · exact g32p_row36_cosetWord_0000
  · exact g32p_row36_cosetWord_0001
  · exact g32p_row36_cosetWord_0002
  · exact g32p_row36_cosetWord_0003
  · exact g32p_row36_cosetWord_0004
  · exact g32p_row36_cosetWord_0005
  · exact g32p_row36_cosetWord_0006
  · exact g32p_row36_cosetWord_0007
  · exact g32p_row36_cosetWord_0008
  · exact g32p_row36_cosetWord_0009
  · exact g32p_row36_cosetWord_0010

theorem g32p_row36_cosetGeneratorBlock_0025 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 25 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s (g32p_finBlockIndex 405 25 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s (g32p_finBlockIndex 405 25 r))) := by
  fin_cases r
  · exact g32p_row36_cosetGeneratorStep_0400 s
  · exact g32p_row36_cosetGeneratorStep_0401 s
  · exact g32p_row36_cosetGeneratorStep_0402 s
  · exact g32p_row36_cosetGeneratorStep_0403 s
  · exact g32p_row36_cosetGeneratorStep_0404 s
  · exact g32p_row36_cosetGeneratorStep_0000 s
  · exact g32p_row36_cosetGeneratorStep_0001 s
  · exact g32p_row36_cosetGeneratorStep_0002 s
  · exact g32p_row36_cosetGeneratorStep_0003 s
  · exact g32p_row36_cosetGeneratorStep_0004 s
  · exact g32p_row36_cosetGeneratorStep_0005 s
  · exact g32p_row36_cosetGeneratorStep_0006 s
  · exact g32p_row36_cosetGeneratorStep_0007 s
  · exact g32p_row36_cosetGeneratorStep_0008 s
  · exact g32p_row36_cosetGeneratorStep_0009 s
  · exact g32p_row36_cosetGeneratorStep_0010 s

theorem g32p_row36_cosetBranchBlock_0025 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices s) (g32p_row36_cosetRepresentatives (g32p_finBlockIndex 405 25 r)) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetBranchNext s (g32p_finBlockIndex 405 25 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetBranchFactor s (g32p_finBlockIndex 405 25 r))) := by
  fin_cases r
  · exact g32p_row36_cosetBranchStep_0400 s
  · exact g32p_row36_cosetBranchStep_0401 s
  · exact g32p_row36_cosetBranchStep_0402 s
  · exact g32p_row36_cosetBranchStep_0403 s
  · exact g32p_row36_cosetBranchStep_0404 s
  · exact g32p_row36_cosetBranchStep_0000 s
  · exact g32p_row36_cosetBranchStep_0001 s
  · exact g32p_row36_cosetBranchStep_0002 s
  · exact g32p_row36_cosetBranchStep_0003 s
  · exact g32p_row36_cosetBranchStep_0004 s
  · exact g32p_row36_cosetBranchStep_0005 s
  · exact g32p_row36_cosetBranchStep_0006 s
  · exact g32p_row36_cosetBranchStep_0007 s
  · exact g32p_row36_cosetBranchStep_0008 s
  · exact g32p_row36_cosetBranchStep_0009 s
  · exact g32p_row36_cosetBranchStep_0010 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row36_cosetWord (i : Fin 405) :
    g32p_archiveIntegralWord (g32p_row36_cosetWords i) = g32p_row36_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row36_cosetWordBlock_0000
  · exact g32p_row36_cosetWordBlock_0001
  · exact g32p_row36_cosetWordBlock_0002
  · exact g32p_row36_cosetWordBlock_0003
  · exact g32p_row36_cosetWordBlock_0004
  · exact g32p_row36_cosetWordBlock_0005
  · exact g32p_row36_cosetWordBlock_0006
  · exact g32p_row36_cosetWordBlock_0007
  · exact g32p_row36_cosetWordBlock_0008
  · exact g32p_row36_cosetWordBlock_0009
  · exact g32p_row36_cosetWordBlock_0010
  · exact g32p_row36_cosetWordBlock_0011
  · exact g32p_row36_cosetWordBlock_0012
  · exact g32p_row36_cosetWordBlock_0013
  · exact g32p_row36_cosetWordBlock_0014
  · exact g32p_row36_cosetWordBlock_0015
  · exact g32p_row36_cosetWordBlock_0016
  · exact g32p_row36_cosetWordBlock_0017
  · exact g32p_row36_cosetWordBlock_0018
  · exact g32p_row36_cosetWordBlock_0019
  · exact g32p_row36_cosetWordBlock_0020
  · exact g32p_row36_cosetWordBlock_0021
  · exact g32p_row36_cosetWordBlock_0022
  · exact g32p_row36_cosetWordBlock_0023
  · exact g32p_row36_cosetWordBlock_0024
  · exact g32p_row36_cosetWordBlock_0025


def g32p_row36_cosetActualRepresentatives (i : Fin 405) : g32p_G := g32p_archiveWord (g32p_row36_cosetWords i)

theorem g32p_row36_cosetActualRepresentatives_map (i : Fin 405) :
    b4b_toMatrix (g32p_row36_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row36_cosetRepresentatives i)) := by
  rw [g32p_row36_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row36_cosetWord]

theorem g32p_row36_cosetGeneratorStep (s : Fin 4) (i : Fin 405) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row36_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetGeneratorNext s i))
        (g32p_row36_groupNodes (g32p_row36_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row36_cosetGeneratorBlock_0000 s
  · exact g32p_row36_cosetGeneratorBlock_0001 s
  · exact g32p_row36_cosetGeneratorBlock_0002 s
  · exact g32p_row36_cosetGeneratorBlock_0003 s
  · exact g32p_row36_cosetGeneratorBlock_0004 s
  · exact g32p_row36_cosetGeneratorBlock_0005 s
  · exact g32p_row36_cosetGeneratorBlock_0006 s
  · exact g32p_row36_cosetGeneratorBlock_0007 s
  · exact g32p_row36_cosetGeneratorBlock_0008 s
  · exact g32p_row36_cosetGeneratorBlock_0009 s
  · exact g32p_row36_cosetGeneratorBlock_0010 s
  · exact g32p_row36_cosetGeneratorBlock_0011 s
  · exact g32p_row36_cosetGeneratorBlock_0012 s
  · exact g32p_row36_cosetGeneratorBlock_0013 s
  · exact g32p_row36_cosetGeneratorBlock_0014 s
  · exact g32p_row36_cosetGeneratorBlock_0015 s
  · exact g32p_row36_cosetGeneratorBlock_0016 s
  · exact g32p_row36_cosetGeneratorBlock_0017 s
  · exact g32p_row36_cosetGeneratorBlock_0018 s
  · exact g32p_row36_cosetGeneratorBlock_0019 s
  · exact g32p_row36_cosetGeneratorBlock_0020 s
  · exact g32p_row36_cosetGeneratorBlock_0021 s
  · exact g32p_row36_cosetGeneratorBlock_0022 s
  · exact g32p_row36_cosetGeneratorBlock_0023 s
  · exact g32p_row36_cosetGeneratorBlock_0024 s
  · exact g32p_row36_cosetGeneratorBlock_0025 s


theorem g32p_row36_cosetActualStep (s : Fin 4) (i : Fin 405) :
    g32p_word (g32p_archiveWords s) * g32p_row36_cosetActualRepresentatives i =
      g32p_row36_cosetActualRepresentatives (g32p_row36_cosetGeneratorNext s i) *
        (g32p_row36_groupEquiv (g32p_row36_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row36_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row36_cosetActualRepresentatives (g32p_row36_cosetGeneratorNext s i) *
      (g32p_row36_groupEquiv (g32p_row36_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row36_cosetActualRepresentatives_map,
    g32p_row36_cosetActualRepresentatives_map, g32p_row36_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row36_cosetGeneratorStep]

theorem g32p_row36_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row36_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row36_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row36_cosetGeneratorNext
      (fun s i => g32p_row36_groupEquiv (g32p_row36_cosetGeneratorFactor s i))
    exact g32p_row36_cosetActualStep
  · rw [g32p_row36_finiteSupplier_order]
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

theorem g32p_row36_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 0)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 0)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 0) = g32p_row36_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 1)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 1)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 1) = g32p_row36_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 2)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 2)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 2) = g32p_row36_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 3)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 3)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 3) = g32p_row36_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 4)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 4)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 4) = g32p_row36_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 5)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 5)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 5) = g32p_row36_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 6)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 6)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 6) = g32p_row36_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 7)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 7)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 7) = g32p_row36_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 8)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 8)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 8) = g32p_row36_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 9)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 9)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 9) = g32p_row36_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 10)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 10)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 10) = g32p_row36_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 11)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 11)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 11) = g32p_row36_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 12)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 12)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 12) = g32p_row36_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 13)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 13)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 13) = g32p_row36_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 14)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 14)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 14) = g32p_row36_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 15)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 15)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 15) = g32p_row36_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row36_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row36_cosetBranchMatrices 0) (g32p_row36_cosetLengths0 (g32p_finBlockIndex 135 0 r)))
      (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 0 r))) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 0 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 0 r))) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 0 r)) = g32p_row36_cosetExponents0 (g32p_finBlockIndex 135 0 r) := by
  fin_cases r
  · exact g32p_row36_cosetMonodromy_0_0000
  · exact g32p_row36_cosetMonodromy_0_0001
  · exact g32p_row36_cosetMonodromy_0_0002
  · exact g32p_row36_cosetMonodromy_0_0003
  · exact g32p_row36_cosetMonodromy_0_0004
  · exact g32p_row36_cosetMonodromy_0_0005
  · exact g32p_row36_cosetMonodromy_0_0006
  · exact g32p_row36_cosetMonodromy_0_0007
  · exact g32p_row36_cosetMonodromy_0_0008
  · exact g32p_row36_cosetMonodromy_0_0009
  · exact g32p_row36_cosetMonodromy_0_0010
  · exact g32p_row36_cosetMonodromy_0_0011
  · exact g32p_row36_cosetMonodromy_0_0012
  · exact g32p_row36_cosetMonodromy_0_0013
  · exact g32p_row36_cosetMonodromy_0_0014
  · exact g32p_row36_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 16)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 16)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 16) = g32p_row36_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 17)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 17)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 17) = g32p_row36_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 18)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 18)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 18) = g32p_row36_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 19)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 19)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 19) = g32p_row36_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 21)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 20)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 20) = g32p_row36_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 22)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 21)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 21) = g32p_row36_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 23)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 22)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 22) = g32p_row36_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 24)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 23)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 23) = g32p_row36_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 25)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 24)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 24) = g32p_row36_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 26)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 25)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 25) = g32p_row36_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 27)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 26)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 26) = g32p_row36_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 28)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 27)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 27) = g32p_row36_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 29)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 28)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 28) = g32p_row36_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 30)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 29)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 29) = g32p_row36_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 31)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 30)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 30) = g32p_row36_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 32)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 31)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 31) = g32p_row36_cosetExponents0 31 := by
  decide +kernel

theorem g32p_row36_cosetMonodromyBlock0_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row36_cosetBranchMatrices 0) (g32p_row36_cosetLengths0 (g32p_finBlockIndex 135 1 r)))
      (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 1 r))) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 1 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 1 r))) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 1 r)) = g32p_row36_cosetExponents0 (g32p_finBlockIndex 135 1 r) := by
  fin_cases r
  · exact g32p_row36_cosetMonodromy_0_0016
  · exact g32p_row36_cosetMonodromy_0_0017
  · exact g32p_row36_cosetMonodromy_0_0018
  · exact g32p_row36_cosetMonodromy_0_0019
  · exact g32p_row36_cosetMonodromy_0_0020
  · exact g32p_row36_cosetMonodromy_0_0021
  · exact g32p_row36_cosetMonodromy_0_0022
  · exact g32p_row36_cosetMonodromy_0_0023
  · exact g32p_row36_cosetMonodromy_0_0024
  · exact g32p_row36_cosetMonodromy_0_0025
  · exact g32p_row36_cosetMonodromy_0_0026
  · exact g32p_row36_cosetMonodromy_0_0027
  · exact g32p_row36_cosetMonodromy_0_0028
  · exact g32p_row36_cosetMonodromy_0_0029
  · exact g32p_row36_cosetMonodromy_0_0030
  · exact g32p_row36_cosetMonodromy_0_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetMonodromy_0_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 34)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 32)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 32) = g32p_row36_cosetExponents0 32 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 35)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 33)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 33) = g32p_row36_cosetExponents0 33 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 36)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 34)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 34) = g32p_row36_cosetExponents0 34 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 37)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 35)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 35) = g32p_row36_cosetExponents0 35 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 38)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 36)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 36) = g32p_row36_cosetExponents0 36 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 40)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 37)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 37) = g32p_row36_cosetExponents0 37 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 41)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 38)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 38) = g32p_row36_cosetExponents0 38 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 43)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 39)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 39) = g32p_row36_cosetExponents0 39 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 44)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 40)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 40) = g32p_row36_cosetExponents0 40 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 45)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 41)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 41) = g32p_row36_cosetExponents0 41 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 46)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 42)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 42) = g32p_row36_cosetExponents0 42 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 47)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 43)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 43) = g32p_row36_cosetExponents0 43 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 48)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 44)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 44) = g32p_row36_cosetExponents0 44 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 49)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 45)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 45) = g32p_row36_cosetExponents0 45 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 50)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 46)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 46) = g32p_row36_cosetExponents0 46 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 51)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 47)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 47) = g32p_row36_cosetExponents0 47 := by
  decide +kernel

theorem g32p_row36_cosetMonodromyBlock0_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row36_cosetBranchMatrices 0) (g32p_row36_cosetLengths0 (g32p_finBlockIndex 135 2 r)))
      (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 2 r))) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 2 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 2 r))) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 2 r)) = g32p_row36_cosetExponents0 (g32p_finBlockIndex 135 2 r) := by
  fin_cases r
  · exact g32p_row36_cosetMonodromy_0_0032
  · exact g32p_row36_cosetMonodromy_0_0033
  · exact g32p_row36_cosetMonodromy_0_0034
  · exact g32p_row36_cosetMonodromy_0_0035
  · exact g32p_row36_cosetMonodromy_0_0036
  · exact g32p_row36_cosetMonodromy_0_0037
  · exact g32p_row36_cosetMonodromy_0_0038
  · exact g32p_row36_cosetMonodromy_0_0039
  · exact g32p_row36_cosetMonodromy_0_0040
  · exact g32p_row36_cosetMonodromy_0_0041
  · exact g32p_row36_cosetMonodromy_0_0042
  · exact g32p_row36_cosetMonodromy_0_0043
  · exact g32p_row36_cosetMonodromy_0_0044
  · exact g32p_row36_cosetMonodromy_0_0045
  · exact g32p_row36_cosetMonodromy_0_0046
  · exact g32p_row36_cosetMonodromy_0_0047


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetMonodromy_0_0048 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 52)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 48)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 48) = g32p_row36_cosetExponents0 48 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0049 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 54)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 49)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 49) = g32p_row36_cosetExponents0 49 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0050 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 55)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 50)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 50) = g32p_row36_cosetExponents0 50 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0051 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 58)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 51)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 51) = g32p_row36_cosetExponents0 51 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0052 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 61)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 52)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 52) = g32p_row36_cosetExponents0 52 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0053 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 62)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 53)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 53) = g32p_row36_cosetExponents0 53 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0054 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 64)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 54)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 54) = g32p_row36_cosetExponents0 54 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0055 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 65)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 55)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 55) = g32p_row36_cosetExponents0 55 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0056 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 66)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 56)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 56) = g32p_row36_cosetExponents0 56 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0057 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 69)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 57)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 57) = g32p_row36_cosetExponents0 57 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0058 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 70)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 58)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 58) = g32p_row36_cosetExponents0 58 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0059 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 71)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 59)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 59) = g32p_row36_cosetExponents0 59 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0060 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 72)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 60)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 60) = g32p_row36_cosetExponents0 60 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0061 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 73)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 61)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 61) = g32p_row36_cosetExponents0 61 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0062 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 74)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 62)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 62) = g32p_row36_cosetExponents0 62 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0063 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 75)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 63)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 63) = g32p_row36_cosetExponents0 63 := by
  decide +kernel

theorem g32p_row36_cosetMonodromyBlock0_0003 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row36_cosetBranchMatrices 0) (g32p_row36_cosetLengths0 (g32p_finBlockIndex 135 3 r)))
      (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 3 r))) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 3 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 3 r))) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 3 r)) = g32p_row36_cosetExponents0 (g32p_finBlockIndex 135 3 r) := by
  fin_cases r
  · exact g32p_row36_cosetMonodromy_0_0048
  · exact g32p_row36_cosetMonodromy_0_0049
  · exact g32p_row36_cosetMonodromy_0_0050
  · exact g32p_row36_cosetMonodromy_0_0051
  · exact g32p_row36_cosetMonodromy_0_0052
  · exact g32p_row36_cosetMonodromy_0_0053
  · exact g32p_row36_cosetMonodromy_0_0054
  · exact g32p_row36_cosetMonodromy_0_0055
  · exact g32p_row36_cosetMonodromy_0_0056
  · exact g32p_row36_cosetMonodromy_0_0057
  · exact g32p_row36_cosetMonodromy_0_0058
  · exact g32p_row36_cosetMonodromy_0_0059
  · exact g32p_row36_cosetMonodromy_0_0060
  · exact g32p_row36_cosetMonodromy_0_0061
  · exact g32p_row36_cosetMonodromy_0_0062
  · exact g32p_row36_cosetMonodromy_0_0063


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row36_cosetMonodromy_0_0064 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 76)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 64)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 64) = g32p_row36_cosetExponents0 64 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0065 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 77)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 65)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 65) = g32p_row36_cosetExponents0 65 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0066 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 79)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 66)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 66) = g32p_row36_cosetExponents0 66 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0067 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 80)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 67)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 67) = g32p_row36_cosetExponents0 67 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0068 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 81)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 68)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 68) = g32p_row36_cosetExponents0 68 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0069 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 82)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 69)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 69) = g32p_row36_cosetExponents0 69 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0070 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 83) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 83)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 70)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 70) = g32p_row36_cosetExponents0 70 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0071 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 84) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 84)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 71)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 71) = g32p_row36_cosetExponents0 71 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0072 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 88)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 72)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 72) = g32p_row36_cosetExponents0 72 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0073 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 90) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 90)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 73)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 73) = g32p_row36_cosetExponents0 73 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0074 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 91) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 91)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 74)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 74) = g32p_row36_cosetExponents0 74 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0075 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 92) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 92)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 75)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 75) = g32p_row36_cosetExponents0 75 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0076 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 93) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 93)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 76)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 76) = g32p_row36_cosetExponents0 76 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0077 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 97) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 97)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 77)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 77) = g32p_row36_cosetExponents0 77 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0078 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 98) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 98)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 78)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 78) = g32p_row36_cosetExponents0 78 := by
  decide +kernel

theorem g32p_row36_cosetMonodromy_0_0079 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row36_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row36_cosetRepresentatives 99) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives 99)
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 79)) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 79) = g32p_row36_cosetExponents0 79 := by
  decide +kernel

theorem g32p_row36_cosetMonodromyBlock0_0004 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row36_cosetBranchMatrices 0) (g32p_row36_cosetLengths0 (g32p_finBlockIndex 135 4 r)))
      (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 4 r))) =
      HurwitzPrymRex_mmul (g32p_row36_cosetRepresentatives (g32p_row36_cosetRoots0 (g32p_finBlockIndex 135 4 r)))
        (g32p_row36_groupNodes (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 4 r))) ∧
    g32p_row36_characterValues (g32p_row36_cosetMonodromies0 (g32p_finBlockIndex 135 4 r)) = g32p_row36_cosetExponents0 (g32p_finBlockIndex 135 4 r) := by
  fin_cases r
  · exact g32p_row36_cosetMonodromy_0_0064
  · exact g32p_row36_cosetMonodromy_0_0065
  · exact g32p_row36_cosetMonodromy_0_0066
  · exact g32p_row36_cosetMonodromy_0_0067
  · exact g32p_row36_cosetMonodromy_0_0068
  · exact g32p_row36_cosetMonodromy_0_0069
  · exact g32p_row36_cosetMonodromy_0_0070
  · exact g32p_row36_cosetMonodromy_0_0071
  · exact g32p_row36_cosetMonodromy_0_0072
  · exact g32p_row36_cosetMonodromy_0_0073
  · exact g32p_row36_cosetMonodromy_0_0074
  · exact g32p_row36_cosetMonodromy_0_0075
  · exact g32p_row36_cosetMonodromy_0_0076
  · exact g32p_row36_cosetMonodromy_0_0077
  · exact g32p_row36_cosetMonodromy_0_0078
  · exact g32p_row36_cosetMonodromy_0_0079


end HodgeLean.Foundations.Program

end
