import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0835

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1280 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1280) = g32p_row31_cosetRepresentatives 1280 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1280) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1280))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1280)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1280) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1280))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1280)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1281 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1281) = g32p_row31_cosetRepresentatives 1281 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1281) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1281))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1281)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1281) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1281))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1281)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1282 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1282) = g32p_row31_cosetRepresentatives 1282 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1282) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1282))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1282)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1282) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1282))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1282)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1283 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1283) = g32p_row31_cosetRepresentatives 1283 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1283) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1283))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1283)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1283) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1283))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1283)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1284 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1284) = g32p_row31_cosetRepresentatives 1284 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1284) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1284))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1284)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1284) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1284))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1284)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1285 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1285) = g32p_row31_cosetRepresentatives 1285 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1285) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1285))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1285)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1285) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1285))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1285)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1286 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1286) = g32p_row31_cosetRepresentatives 1286 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1286) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1286))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1286)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1286) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1286))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1286)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1287 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1287) = g32p_row31_cosetRepresentatives 1287 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1287) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1287))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1287)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1287) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1287))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1287)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1288 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1288) = g32p_row31_cosetRepresentatives 1288 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1288) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1288))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1288)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1288) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1288))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1288)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1289 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1289) = g32p_row31_cosetRepresentatives 1289 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1289) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1289))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1289)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1289) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1289))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1289)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1290 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1290) = g32p_row31_cosetRepresentatives 1290 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1290) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1290))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1290)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1290) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1290))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1290)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1291 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1291) = g32p_row31_cosetRepresentatives 1291 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1291) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1291))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1291)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1291) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1291))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1291)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1292 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1292) = g32p_row31_cosetRepresentatives 1292 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1292) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1292))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1292)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1292) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1292))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1292)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1293 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1293) = g32p_row31_cosetRepresentatives 1293 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1293) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1293))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1293)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1293) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1293))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1293)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1294 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1294) = g32p_row31_cosetRepresentatives 1294 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1294) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1294))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1294)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1294) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1294))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1294)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1295 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1295) = g32p_row31_cosetRepresentatives 1295 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1295) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1295))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1295)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1295) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1295))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1295)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0080 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 80 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 80 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1280
  · exact g32p_row31_cosetWord_1281
  · exact g32p_row31_cosetWord_1282
  · exact g32p_row31_cosetWord_1283
  · exact g32p_row31_cosetWord_1284
  · exact g32p_row31_cosetWord_1285
  · exact g32p_row31_cosetWord_1286
  · exact g32p_row31_cosetWord_1287
  · exact g32p_row31_cosetWord_1288
  · exact g32p_row31_cosetWord_1289
  · exact g32p_row31_cosetWord_1290
  · exact g32p_row31_cosetWord_1291
  · exact g32p_row31_cosetWord_1292
  · exact g32p_row31_cosetWord_1293
  · exact g32p_row31_cosetWord_1294
  · exact g32p_row31_cosetWord_1295

theorem g32p_row31_cosetGeneratorBlock_0080 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 80 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 80 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 80 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1280 s
  · exact g32p_row31_cosetGeneratorStep_1281 s
  · exact g32p_row31_cosetGeneratorStep_1282 s
  · exact g32p_row31_cosetGeneratorStep_1283 s
  · exact g32p_row31_cosetGeneratorStep_1284 s
  · exact g32p_row31_cosetGeneratorStep_1285 s
  · exact g32p_row31_cosetGeneratorStep_1286 s
  · exact g32p_row31_cosetGeneratorStep_1287 s
  · exact g32p_row31_cosetGeneratorStep_1288 s
  · exact g32p_row31_cosetGeneratorStep_1289 s
  · exact g32p_row31_cosetGeneratorStep_1290 s
  · exact g32p_row31_cosetGeneratorStep_1291 s
  · exact g32p_row31_cosetGeneratorStep_1292 s
  · exact g32p_row31_cosetGeneratorStep_1293 s
  · exact g32p_row31_cosetGeneratorStep_1294 s
  · exact g32p_row31_cosetGeneratorStep_1295 s

theorem g32p_row31_cosetBranchBlock_0080 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 80 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 80 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 80 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1280 s
  · exact g32p_row31_cosetBranchStep_1281 s
  · exact g32p_row31_cosetBranchStep_1282 s
  · exact g32p_row31_cosetBranchStep_1283 s
  · exact g32p_row31_cosetBranchStep_1284 s
  · exact g32p_row31_cosetBranchStep_1285 s
  · exact g32p_row31_cosetBranchStep_1286 s
  · exact g32p_row31_cosetBranchStep_1287 s
  · exact g32p_row31_cosetBranchStep_1288 s
  · exact g32p_row31_cosetBranchStep_1289 s
  · exact g32p_row31_cosetBranchStep_1290 s
  · exact g32p_row31_cosetBranchStep_1291 s
  · exact g32p_row31_cosetBranchStep_1292 s
  · exact g32p_row31_cosetBranchStep_1293 s
  · exact g32p_row31_cosetBranchStep_1294 s
  · exact g32p_row31_cosetBranchStep_1295 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1296 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1296) = g32p_row31_cosetRepresentatives 1296 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1296) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1296))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1296)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1296) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1296))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1296)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1297 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1297) = g32p_row31_cosetRepresentatives 1297 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1297) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1297))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1297)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1297) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1297))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1297)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1298 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1298) = g32p_row31_cosetRepresentatives 1298 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1298) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1298))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1298)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1298) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1298))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1298)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1299 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1299) = g32p_row31_cosetRepresentatives 1299 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1299) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1299))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1299)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1299) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1299))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1299)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1300 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1300) = g32p_row31_cosetRepresentatives 1300 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1300) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1300))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1300)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1300) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1300))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1300)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1301 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1301) = g32p_row31_cosetRepresentatives 1301 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1301) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1301))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1301)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1301) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1301))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1301)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1302 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1302) = g32p_row31_cosetRepresentatives 1302 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1302) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1302))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1302)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1302) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1302))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1302)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1303 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1303) = g32p_row31_cosetRepresentatives 1303 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1303) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1303))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1303)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1303) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1303))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1303)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1304 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1304) = g32p_row31_cosetRepresentatives 1304 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1304) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1304))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1304)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1304) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1304))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1304)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1305 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1305) = g32p_row31_cosetRepresentatives 1305 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1305) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1305))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1305)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1305) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1305))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1305)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1306 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1306) = g32p_row31_cosetRepresentatives 1306 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1306) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1306))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1306)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1306) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1306))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1306)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1307 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1307) = g32p_row31_cosetRepresentatives 1307 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1307) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1307))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1307)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1307) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1307))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1307)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1308 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1308) = g32p_row31_cosetRepresentatives 1308 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1308) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1308))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1308)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1308) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1308))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1308)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1309 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1309) = g32p_row31_cosetRepresentatives 1309 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1309) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1309))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1309)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1309) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1309))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1309)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1310 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1310) = g32p_row31_cosetRepresentatives 1310 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1310) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1310))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1310)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1310) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1310))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1310)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1311 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1311) = g32p_row31_cosetRepresentatives 1311 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1311) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1311))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1311)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1311) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1311))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1311)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0081 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 81 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 81 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1296
  · exact g32p_row31_cosetWord_1297
  · exact g32p_row31_cosetWord_1298
  · exact g32p_row31_cosetWord_1299
  · exact g32p_row31_cosetWord_1300
  · exact g32p_row31_cosetWord_1301
  · exact g32p_row31_cosetWord_1302
  · exact g32p_row31_cosetWord_1303
  · exact g32p_row31_cosetWord_1304
  · exact g32p_row31_cosetWord_1305
  · exact g32p_row31_cosetWord_1306
  · exact g32p_row31_cosetWord_1307
  · exact g32p_row31_cosetWord_1308
  · exact g32p_row31_cosetWord_1309
  · exact g32p_row31_cosetWord_1310
  · exact g32p_row31_cosetWord_1311

theorem g32p_row31_cosetGeneratorBlock_0081 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 81 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 81 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 81 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1296 s
  · exact g32p_row31_cosetGeneratorStep_1297 s
  · exact g32p_row31_cosetGeneratorStep_1298 s
  · exact g32p_row31_cosetGeneratorStep_1299 s
  · exact g32p_row31_cosetGeneratorStep_1300 s
  · exact g32p_row31_cosetGeneratorStep_1301 s
  · exact g32p_row31_cosetGeneratorStep_1302 s
  · exact g32p_row31_cosetGeneratorStep_1303 s
  · exact g32p_row31_cosetGeneratorStep_1304 s
  · exact g32p_row31_cosetGeneratorStep_1305 s
  · exact g32p_row31_cosetGeneratorStep_1306 s
  · exact g32p_row31_cosetGeneratorStep_1307 s
  · exact g32p_row31_cosetGeneratorStep_1308 s
  · exact g32p_row31_cosetGeneratorStep_1309 s
  · exact g32p_row31_cosetGeneratorStep_1310 s
  · exact g32p_row31_cosetGeneratorStep_1311 s

theorem g32p_row31_cosetBranchBlock_0081 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 81 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 81 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 81 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1296 s
  · exact g32p_row31_cosetBranchStep_1297 s
  · exact g32p_row31_cosetBranchStep_1298 s
  · exact g32p_row31_cosetBranchStep_1299 s
  · exact g32p_row31_cosetBranchStep_1300 s
  · exact g32p_row31_cosetBranchStep_1301 s
  · exact g32p_row31_cosetBranchStep_1302 s
  · exact g32p_row31_cosetBranchStep_1303 s
  · exact g32p_row31_cosetBranchStep_1304 s
  · exact g32p_row31_cosetBranchStep_1305 s
  · exact g32p_row31_cosetBranchStep_1306 s
  · exact g32p_row31_cosetBranchStep_1307 s
  · exact g32p_row31_cosetBranchStep_1308 s
  · exact g32p_row31_cosetBranchStep_1309 s
  · exact g32p_row31_cosetBranchStep_1310 s
  · exact g32p_row31_cosetBranchStep_1311 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1312 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1312) = g32p_row31_cosetRepresentatives 1312 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1312) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1312))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1312)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1312) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1312))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1312)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1313 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1313) = g32p_row31_cosetRepresentatives 1313 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1313) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1313))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1313)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1313) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1313))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1313)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1314 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1314) = g32p_row31_cosetRepresentatives 1314 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1314) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1314))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1314)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1314) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1314))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1314)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1315 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1315) = g32p_row31_cosetRepresentatives 1315 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1315) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1315))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1315)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1315) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1315))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1315)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1316 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1316) = g32p_row31_cosetRepresentatives 1316 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1316) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1316))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1316)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1316) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1316))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1316)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1317 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1317) = g32p_row31_cosetRepresentatives 1317 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1317) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1317))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1317)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1317) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1317))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1317)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1318 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1318) = g32p_row31_cosetRepresentatives 1318 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1318) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1318))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1318)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1318) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1318))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1318)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1319 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1319) = g32p_row31_cosetRepresentatives 1319 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1319) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1319))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1319)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1319) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1319))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1319)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1320 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1320) = g32p_row31_cosetRepresentatives 1320 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1320) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1320))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1320)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1320) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1320))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1320)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1321 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1321) = g32p_row31_cosetRepresentatives 1321 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1321) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1321))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1321)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1321) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1321))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1321)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1322 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1322) = g32p_row31_cosetRepresentatives 1322 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1322) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1322))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1322)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1322) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1322))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1322)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1323 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1323) = g32p_row31_cosetRepresentatives 1323 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1323) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1323))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1323)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1323) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1323))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1323)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1324 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1324) = g32p_row31_cosetRepresentatives 1324 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1324) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1324))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1324)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1324) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1324))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1324)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1325 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1325) = g32p_row31_cosetRepresentatives 1325 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1325) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1325))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1325)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1325) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1325))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1325)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1326 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1326) = g32p_row31_cosetRepresentatives 1326 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1326) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1326))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1326)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1326) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1326))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1326)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1327 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1327) = g32p_row31_cosetRepresentatives 1327 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1327) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1327))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1327)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1327) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1327))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1327)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0082 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 82 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 82 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1312
  · exact g32p_row31_cosetWord_1313
  · exact g32p_row31_cosetWord_1314
  · exact g32p_row31_cosetWord_1315
  · exact g32p_row31_cosetWord_1316
  · exact g32p_row31_cosetWord_1317
  · exact g32p_row31_cosetWord_1318
  · exact g32p_row31_cosetWord_1319
  · exact g32p_row31_cosetWord_1320
  · exact g32p_row31_cosetWord_1321
  · exact g32p_row31_cosetWord_1322
  · exact g32p_row31_cosetWord_1323
  · exact g32p_row31_cosetWord_1324
  · exact g32p_row31_cosetWord_1325
  · exact g32p_row31_cosetWord_1326
  · exact g32p_row31_cosetWord_1327

theorem g32p_row31_cosetGeneratorBlock_0082 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 82 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 82 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 82 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1312 s
  · exact g32p_row31_cosetGeneratorStep_1313 s
  · exact g32p_row31_cosetGeneratorStep_1314 s
  · exact g32p_row31_cosetGeneratorStep_1315 s
  · exact g32p_row31_cosetGeneratorStep_1316 s
  · exact g32p_row31_cosetGeneratorStep_1317 s
  · exact g32p_row31_cosetGeneratorStep_1318 s
  · exact g32p_row31_cosetGeneratorStep_1319 s
  · exact g32p_row31_cosetGeneratorStep_1320 s
  · exact g32p_row31_cosetGeneratorStep_1321 s
  · exact g32p_row31_cosetGeneratorStep_1322 s
  · exact g32p_row31_cosetGeneratorStep_1323 s
  · exact g32p_row31_cosetGeneratorStep_1324 s
  · exact g32p_row31_cosetGeneratorStep_1325 s
  · exact g32p_row31_cosetGeneratorStep_1326 s
  · exact g32p_row31_cosetGeneratorStep_1327 s

theorem g32p_row31_cosetBranchBlock_0082 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 82 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 82 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 82 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1312 s
  · exact g32p_row31_cosetBranchStep_1313 s
  · exact g32p_row31_cosetBranchStep_1314 s
  · exact g32p_row31_cosetBranchStep_1315 s
  · exact g32p_row31_cosetBranchStep_1316 s
  · exact g32p_row31_cosetBranchStep_1317 s
  · exact g32p_row31_cosetBranchStep_1318 s
  · exact g32p_row31_cosetBranchStep_1319 s
  · exact g32p_row31_cosetBranchStep_1320 s
  · exact g32p_row31_cosetBranchStep_1321 s
  · exact g32p_row31_cosetBranchStep_1322 s
  · exact g32p_row31_cosetBranchStep_1323 s
  · exact g32p_row31_cosetBranchStep_1324 s
  · exact g32p_row31_cosetBranchStep_1325 s
  · exact g32p_row31_cosetBranchStep_1326 s
  · exact g32p_row31_cosetBranchStep_1327 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1328 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1328) = g32p_row31_cosetRepresentatives 1328 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1328 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1328) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1328))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1328)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1328 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1328) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1328))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1328)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1329 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1329) = g32p_row31_cosetRepresentatives 1329 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1329 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1329) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1329))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1329)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1329 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1329) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1329))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1329)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1330 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1330) = g32p_row31_cosetRepresentatives 1330 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1330 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1330) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1330))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1330)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1330 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1330) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1330))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1330)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1331 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1331) = g32p_row31_cosetRepresentatives 1331 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1331 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1331) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1331))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1331)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1331 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1331) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1331))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1331)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1332 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1332) = g32p_row31_cosetRepresentatives 1332 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1332 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1332) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1332))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1332)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1332 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1332) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1332))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1332)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1333 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1333) = g32p_row31_cosetRepresentatives 1333 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1333 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1333) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1333))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1333)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1333 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1333) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1333))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1333)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1334 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1334) = g32p_row31_cosetRepresentatives 1334 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1334 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1334) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1334))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1334)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1334 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1334) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1334))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1334)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1335 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1335) = g32p_row31_cosetRepresentatives 1335 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1335 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1335) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1335))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1335)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1335 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1335) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1335))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1335)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1336 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1336) = g32p_row31_cosetRepresentatives 1336 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1336 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1336) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1336))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1336)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1336 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1336) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1336))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1336)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1337 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1337) = g32p_row31_cosetRepresentatives 1337 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1337 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1337) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1337))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1337)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1337 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1337) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1337))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1337)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1338 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1338) = g32p_row31_cosetRepresentatives 1338 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1338 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1338) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1338))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1338)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1338 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1338) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1338))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1338)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1339 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1339) = g32p_row31_cosetRepresentatives 1339 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1339 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1339) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1339))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1339)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1339 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1339) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1339))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1339)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1340 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1340) = g32p_row31_cosetRepresentatives 1340 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1340 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1340) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1340))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1340)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1340 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1340) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1340))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1340)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1341 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1341) = g32p_row31_cosetRepresentatives 1341 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1341 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1341) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1341))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1341)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1341 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1341) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1341))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1341)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1342 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1342) = g32p_row31_cosetRepresentatives 1342 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1342 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1342) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1342))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1342)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1342 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1342) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1342))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1342)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1343 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1343) = g32p_row31_cosetRepresentatives 1343 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1343 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1343) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1343))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1343)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1343 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1343) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1343))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1343)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0083 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 83 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 83 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1328
  · exact g32p_row31_cosetWord_1329
  · exact g32p_row31_cosetWord_1330
  · exact g32p_row31_cosetWord_1331
  · exact g32p_row31_cosetWord_1332
  · exact g32p_row31_cosetWord_1333
  · exact g32p_row31_cosetWord_1334
  · exact g32p_row31_cosetWord_1335
  · exact g32p_row31_cosetWord_1336
  · exact g32p_row31_cosetWord_1337
  · exact g32p_row31_cosetWord_1338
  · exact g32p_row31_cosetWord_1339
  · exact g32p_row31_cosetWord_1340
  · exact g32p_row31_cosetWord_1341
  · exact g32p_row31_cosetWord_1342
  · exact g32p_row31_cosetWord_1343

theorem g32p_row31_cosetGeneratorBlock_0083 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 83 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 83 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 83 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1328 s
  · exact g32p_row31_cosetGeneratorStep_1329 s
  · exact g32p_row31_cosetGeneratorStep_1330 s
  · exact g32p_row31_cosetGeneratorStep_1331 s
  · exact g32p_row31_cosetGeneratorStep_1332 s
  · exact g32p_row31_cosetGeneratorStep_1333 s
  · exact g32p_row31_cosetGeneratorStep_1334 s
  · exact g32p_row31_cosetGeneratorStep_1335 s
  · exact g32p_row31_cosetGeneratorStep_1336 s
  · exact g32p_row31_cosetGeneratorStep_1337 s
  · exact g32p_row31_cosetGeneratorStep_1338 s
  · exact g32p_row31_cosetGeneratorStep_1339 s
  · exact g32p_row31_cosetGeneratorStep_1340 s
  · exact g32p_row31_cosetGeneratorStep_1341 s
  · exact g32p_row31_cosetGeneratorStep_1342 s
  · exact g32p_row31_cosetGeneratorStep_1343 s

theorem g32p_row31_cosetBranchBlock_0083 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 83 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 83 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 83 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1328 s
  · exact g32p_row31_cosetBranchStep_1329 s
  · exact g32p_row31_cosetBranchStep_1330 s
  · exact g32p_row31_cosetBranchStep_1331 s
  · exact g32p_row31_cosetBranchStep_1332 s
  · exact g32p_row31_cosetBranchStep_1333 s
  · exact g32p_row31_cosetBranchStep_1334 s
  · exact g32p_row31_cosetBranchStep_1335 s
  · exact g32p_row31_cosetBranchStep_1336 s
  · exact g32p_row31_cosetBranchStep_1337 s
  · exact g32p_row31_cosetBranchStep_1338 s
  · exact g32p_row31_cosetBranchStep_1339 s
  · exact g32p_row31_cosetBranchStep_1340 s
  · exact g32p_row31_cosetBranchStep_1341 s
  · exact g32p_row31_cosetBranchStep_1342 s
  · exact g32p_row31_cosetBranchStep_1343 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1344 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1344) = g32p_row31_cosetRepresentatives 1344 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1344 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1344) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1344))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1344)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1344 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1344) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1344))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1344)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1345 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1345) = g32p_row31_cosetRepresentatives 1345 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1345 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1345) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1345))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1345)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1345 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1345) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1345))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1345)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1346 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1346) = g32p_row31_cosetRepresentatives 1346 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1346 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1346) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1346))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1346)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1346 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1346) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1346))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1346)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1347 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1347) = g32p_row31_cosetRepresentatives 1347 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1347 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1347) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1347))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1347)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1347 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1347) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1347))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1347)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1348 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1348) = g32p_row31_cosetRepresentatives 1348 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1348 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1348) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1348))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1348)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1348 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1348) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1348))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1348)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1349 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1349) = g32p_row31_cosetRepresentatives 1349 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1349 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1349) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1349))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1349)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1349 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1349) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1349))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1349)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1350 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1350) = g32p_row31_cosetRepresentatives 1350 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1350 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1350) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1350))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1350)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1350 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1350) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1350))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1350)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1351 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1351) = g32p_row31_cosetRepresentatives 1351 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1351 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1351) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1351))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1351)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1351 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1351) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1351))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1351)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1352 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1352) = g32p_row31_cosetRepresentatives 1352 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1352 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1352) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1352))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1352)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1352 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1352) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1352))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1352)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1353 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1353) = g32p_row31_cosetRepresentatives 1353 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1353 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1353) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1353))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1353)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1353 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1353) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1353))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1353)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1354 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1354) = g32p_row31_cosetRepresentatives 1354 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1354 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1354) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1354))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1354)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1354 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1354) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1354))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1354)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1355 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1355) = g32p_row31_cosetRepresentatives 1355 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1355 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1355) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1355))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1355)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1355 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1355) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1355))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1355)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1356 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1356) = g32p_row31_cosetRepresentatives 1356 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1356 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1356) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1356))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1356)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1356 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1356) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1356))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1356)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1357 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1357) = g32p_row31_cosetRepresentatives 1357 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1357 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1357) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1357))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1357)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1357 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1357) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1357))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1357)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1358 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1358) = g32p_row31_cosetRepresentatives 1358 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1358 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1358) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1358))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1358)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1358 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1358) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1358))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1358)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1359 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1359) = g32p_row31_cosetRepresentatives 1359 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1359 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1359) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1359))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1359)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1359 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1359) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1359))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1359)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0084 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 84 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 84 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1344
  · exact g32p_row31_cosetWord_1345
  · exact g32p_row31_cosetWord_1346
  · exact g32p_row31_cosetWord_1347
  · exact g32p_row31_cosetWord_1348
  · exact g32p_row31_cosetWord_1349
  · exact g32p_row31_cosetWord_1350
  · exact g32p_row31_cosetWord_1351
  · exact g32p_row31_cosetWord_1352
  · exact g32p_row31_cosetWord_1353
  · exact g32p_row31_cosetWord_1354
  · exact g32p_row31_cosetWord_1355
  · exact g32p_row31_cosetWord_1356
  · exact g32p_row31_cosetWord_1357
  · exact g32p_row31_cosetWord_1358
  · exact g32p_row31_cosetWord_1359

theorem g32p_row31_cosetGeneratorBlock_0084 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 84 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 84 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 84 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1344 s
  · exact g32p_row31_cosetGeneratorStep_1345 s
  · exact g32p_row31_cosetGeneratorStep_1346 s
  · exact g32p_row31_cosetGeneratorStep_1347 s
  · exact g32p_row31_cosetGeneratorStep_1348 s
  · exact g32p_row31_cosetGeneratorStep_1349 s
  · exact g32p_row31_cosetGeneratorStep_1350 s
  · exact g32p_row31_cosetGeneratorStep_1351 s
  · exact g32p_row31_cosetGeneratorStep_1352 s
  · exact g32p_row31_cosetGeneratorStep_1353 s
  · exact g32p_row31_cosetGeneratorStep_1354 s
  · exact g32p_row31_cosetGeneratorStep_1355 s
  · exact g32p_row31_cosetGeneratorStep_1356 s
  · exact g32p_row31_cosetGeneratorStep_1357 s
  · exact g32p_row31_cosetGeneratorStep_1358 s
  · exact g32p_row31_cosetGeneratorStep_1359 s

theorem g32p_row31_cosetBranchBlock_0084 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 84 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 84 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 84 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1344 s
  · exact g32p_row31_cosetBranchStep_1345 s
  · exact g32p_row31_cosetBranchStep_1346 s
  · exact g32p_row31_cosetBranchStep_1347 s
  · exact g32p_row31_cosetBranchStep_1348 s
  · exact g32p_row31_cosetBranchStep_1349 s
  · exact g32p_row31_cosetBranchStep_1350 s
  · exact g32p_row31_cosetBranchStep_1351 s
  · exact g32p_row31_cosetBranchStep_1352 s
  · exact g32p_row31_cosetBranchStep_1353 s
  · exact g32p_row31_cosetBranchStep_1354 s
  · exact g32p_row31_cosetBranchStep_1355 s
  · exact g32p_row31_cosetBranchStep_1356 s
  · exact g32p_row31_cosetBranchStep_1357 s
  · exact g32p_row31_cosetBranchStep_1358 s
  · exact g32p_row31_cosetBranchStep_1359 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1360 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1360) = g32p_row31_cosetRepresentatives 1360 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1360 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1360) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1360))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1360)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1360 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1360) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1360))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1360)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1361 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1361) = g32p_row31_cosetRepresentatives 1361 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1361 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1361) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1361))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1361)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1361 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1361) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1361))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1361)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1362 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1362) = g32p_row31_cosetRepresentatives 1362 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1362 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1362) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1362))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1362)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1362 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1362) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1362))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1362)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1363 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1363) = g32p_row31_cosetRepresentatives 1363 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1363 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1363) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1363))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1363)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1363 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1363) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1363))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1363)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1364 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1364) = g32p_row31_cosetRepresentatives 1364 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1364 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1364) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1364))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1364)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1364 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1364) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1364))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1364)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1365 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1365) = g32p_row31_cosetRepresentatives 1365 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1365 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1365) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1365))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1365)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1365 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1365) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1365))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1365)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1366 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1366) = g32p_row31_cosetRepresentatives 1366 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1366 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1366) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1366))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1366)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1366 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1366) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1366))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1366)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1367 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1367) = g32p_row31_cosetRepresentatives 1367 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1367 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1367) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1367))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1367)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1367 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1367) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1367))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1367)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1368 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1368) = g32p_row31_cosetRepresentatives 1368 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1368 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1368) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1368))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1368)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1368 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1368) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1368))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1368)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1369 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1369) = g32p_row31_cosetRepresentatives 1369 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1369 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1369) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1369))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1369)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1369 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1369) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1369))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1369)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1370 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1370) = g32p_row31_cosetRepresentatives 1370 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1370 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1370) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1370))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1370)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1370 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1370) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1370))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1370)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1371 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1371) = g32p_row31_cosetRepresentatives 1371 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1371 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1371) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1371))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1371)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1371 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1371) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1371))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1371)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1372 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1372) = g32p_row31_cosetRepresentatives 1372 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1372 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1372) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1372))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1372)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1372 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1372) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1372))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1372)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1373 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1373) = g32p_row31_cosetRepresentatives 1373 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1373 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1373) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1373))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1373)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1373 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1373) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1373))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1373)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1374 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1374) = g32p_row31_cosetRepresentatives 1374 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1374 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1374) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1374))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1374)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1374 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1374) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1374))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1374)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1375 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1375) = g32p_row31_cosetRepresentatives 1375 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1375 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1375) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1375))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1375)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1375 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1375) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1375))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1375)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0085 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 85 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 85 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1360
  · exact g32p_row31_cosetWord_1361
  · exact g32p_row31_cosetWord_1362
  · exact g32p_row31_cosetWord_1363
  · exact g32p_row31_cosetWord_1364
  · exact g32p_row31_cosetWord_1365
  · exact g32p_row31_cosetWord_1366
  · exact g32p_row31_cosetWord_1367
  · exact g32p_row31_cosetWord_1368
  · exact g32p_row31_cosetWord_1369
  · exact g32p_row31_cosetWord_1370
  · exact g32p_row31_cosetWord_1371
  · exact g32p_row31_cosetWord_1372
  · exact g32p_row31_cosetWord_1373
  · exact g32p_row31_cosetWord_1374
  · exact g32p_row31_cosetWord_1375

theorem g32p_row31_cosetGeneratorBlock_0085 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 85 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 85 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 85 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1360 s
  · exact g32p_row31_cosetGeneratorStep_1361 s
  · exact g32p_row31_cosetGeneratorStep_1362 s
  · exact g32p_row31_cosetGeneratorStep_1363 s
  · exact g32p_row31_cosetGeneratorStep_1364 s
  · exact g32p_row31_cosetGeneratorStep_1365 s
  · exact g32p_row31_cosetGeneratorStep_1366 s
  · exact g32p_row31_cosetGeneratorStep_1367 s
  · exact g32p_row31_cosetGeneratorStep_1368 s
  · exact g32p_row31_cosetGeneratorStep_1369 s
  · exact g32p_row31_cosetGeneratorStep_1370 s
  · exact g32p_row31_cosetGeneratorStep_1371 s
  · exact g32p_row31_cosetGeneratorStep_1372 s
  · exact g32p_row31_cosetGeneratorStep_1373 s
  · exact g32p_row31_cosetGeneratorStep_1374 s
  · exact g32p_row31_cosetGeneratorStep_1375 s

theorem g32p_row31_cosetBranchBlock_0085 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 85 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 85 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 85 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1360 s
  · exact g32p_row31_cosetBranchStep_1361 s
  · exact g32p_row31_cosetBranchStep_1362 s
  · exact g32p_row31_cosetBranchStep_1363 s
  · exact g32p_row31_cosetBranchStep_1364 s
  · exact g32p_row31_cosetBranchStep_1365 s
  · exact g32p_row31_cosetBranchStep_1366 s
  · exact g32p_row31_cosetBranchStep_1367 s
  · exact g32p_row31_cosetBranchStep_1368 s
  · exact g32p_row31_cosetBranchStep_1369 s
  · exact g32p_row31_cosetBranchStep_1370 s
  · exact g32p_row31_cosetBranchStep_1371 s
  · exact g32p_row31_cosetBranchStep_1372 s
  · exact g32p_row31_cosetBranchStep_1373 s
  · exact g32p_row31_cosetBranchStep_1374 s
  · exact g32p_row31_cosetBranchStep_1375 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1376 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1376) = g32p_row31_cosetRepresentatives 1376 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1376 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1376) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1376))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1376)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1376 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1376) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1376))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1376)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1377 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1377) = g32p_row31_cosetRepresentatives 1377 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1377 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1377) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1377))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1377)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1377 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1377) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1377))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1377)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1378 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1378) = g32p_row31_cosetRepresentatives 1378 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1378 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1378) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1378))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1378)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1378 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1378) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1378))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1378)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1379 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1379) = g32p_row31_cosetRepresentatives 1379 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1379 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1379) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1379))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1379)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1379 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1379) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1379))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1379)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1380 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1380) = g32p_row31_cosetRepresentatives 1380 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1380 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1380) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1380))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1380)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1380 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1380) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1380))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1380)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1381 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1381) = g32p_row31_cosetRepresentatives 1381 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1381 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1381) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1381))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1381)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1381 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1381) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1381))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1381)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1382 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1382) = g32p_row31_cosetRepresentatives 1382 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1382 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1382) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1382))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1382)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1382 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1382) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1382))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1382)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1383 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1383) = g32p_row31_cosetRepresentatives 1383 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1383 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1383) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1383))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1383)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1383 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1383) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1383))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1383)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1384 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1384) = g32p_row31_cosetRepresentatives 1384 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1384 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1384) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1384))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1384)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1384 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1384) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1384))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1384)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1385 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1385) = g32p_row31_cosetRepresentatives 1385 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1385 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1385) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1385))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1385)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1385 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1385) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1385))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1385)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1386 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1386) = g32p_row31_cosetRepresentatives 1386 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1386 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1386) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1386))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1386)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1386 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1386) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1386))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1386)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1387 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1387) = g32p_row31_cosetRepresentatives 1387 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1387 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1387) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1387))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1387)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1387 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1387) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1387))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1387)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1388 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1388) = g32p_row31_cosetRepresentatives 1388 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1388 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1388) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1388))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1388)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1388 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1388) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1388))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1388)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1389 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1389) = g32p_row31_cosetRepresentatives 1389 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1389 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1389) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1389))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1389)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1389 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1389) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1389))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1389)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1390 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1390) = g32p_row31_cosetRepresentatives 1390 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1390 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1390) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1390))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1390)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1390 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1390) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1390))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1390)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1391 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1391) = g32p_row31_cosetRepresentatives 1391 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1391 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1391) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1391))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1391)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1391 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1391) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1391))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1391)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0086 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 86 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 86 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1376
  · exact g32p_row31_cosetWord_1377
  · exact g32p_row31_cosetWord_1378
  · exact g32p_row31_cosetWord_1379
  · exact g32p_row31_cosetWord_1380
  · exact g32p_row31_cosetWord_1381
  · exact g32p_row31_cosetWord_1382
  · exact g32p_row31_cosetWord_1383
  · exact g32p_row31_cosetWord_1384
  · exact g32p_row31_cosetWord_1385
  · exact g32p_row31_cosetWord_1386
  · exact g32p_row31_cosetWord_1387
  · exact g32p_row31_cosetWord_1388
  · exact g32p_row31_cosetWord_1389
  · exact g32p_row31_cosetWord_1390
  · exact g32p_row31_cosetWord_1391

theorem g32p_row31_cosetGeneratorBlock_0086 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 86 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 86 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 86 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1376 s
  · exact g32p_row31_cosetGeneratorStep_1377 s
  · exact g32p_row31_cosetGeneratorStep_1378 s
  · exact g32p_row31_cosetGeneratorStep_1379 s
  · exact g32p_row31_cosetGeneratorStep_1380 s
  · exact g32p_row31_cosetGeneratorStep_1381 s
  · exact g32p_row31_cosetGeneratorStep_1382 s
  · exact g32p_row31_cosetGeneratorStep_1383 s
  · exact g32p_row31_cosetGeneratorStep_1384 s
  · exact g32p_row31_cosetGeneratorStep_1385 s
  · exact g32p_row31_cosetGeneratorStep_1386 s
  · exact g32p_row31_cosetGeneratorStep_1387 s
  · exact g32p_row31_cosetGeneratorStep_1388 s
  · exact g32p_row31_cosetGeneratorStep_1389 s
  · exact g32p_row31_cosetGeneratorStep_1390 s
  · exact g32p_row31_cosetGeneratorStep_1391 s

theorem g32p_row31_cosetBranchBlock_0086 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 86 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 86 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 86 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1376 s
  · exact g32p_row31_cosetBranchStep_1377 s
  · exact g32p_row31_cosetBranchStep_1378 s
  · exact g32p_row31_cosetBranchStep_1379 s
  · exact g32p_row31_cosetBranchStep_1380 s
  · exact g32p_row31_cosetBranchStep_1381 s
  · exact g32p_row31_cosetBranchStep_1382 s
  · exact g32p_row31_cosetBranchStep_1383 s
  · exact g32p_row31_cosetBranchStep_1384 s
  · exact g32p_row31_cosetBranchStep_1385 s
  · exact g32p_row31_cosetBranchStep_1386 s
  · exact g32p_row31_cosetBranchStep_1387 s
  · exact g32p_row31_cosetBranchStep_1388 s
  · exact g32p_row31_cosetBranchStep_1389 s
  · exact g32p_row31_cosetBranchStep_1390 s
  · exact g32p_row31_cosetBranchStep_1391 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1392 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1392) = g32p_row31_cosetRepresentatives 1392 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1392 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1392) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1392))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1392)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1392 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1392) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1392))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1392)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1393 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1393) = g32p_row31_cosetRepresentatives 1393 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1393 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1393) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1393))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1393)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1393 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1393) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1393))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1393)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1394 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1394) = g32p_row31_cosetRepresentatives 1394 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1394 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1394) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1394))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1394)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1394 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1394) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1394))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1394)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1395 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1395) = g32p_row31_cosetRepresentatives 1395 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1395 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1395) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1395))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1395)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1395 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1395) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1395))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1395)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1396 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1396) = g32p_row31_cosetRepresentatives 1396 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1396 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1396) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1396))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1396)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1396 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1396) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1396))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1396)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1397 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1397) = g32p_row31_cosetRepresentatives 1397 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1397 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1397) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1397))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1397)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1397 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1397) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1397))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1397)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1398 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1398) = g32p_row31_cosetRepresentatives 1398 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1398 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1398) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1398))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1398)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1398 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1398) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1398))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1398)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1399 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1399) = g32p_row31_cosetRepresentatives 1399 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1399 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1399) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1399))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1399)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1399 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1399) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1399))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1399)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1400 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1400) = g32p_row31_cosetRepresentatives 1400 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1400 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1400) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1400))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1400)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1400 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1400) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1400))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1400)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1401 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1401) = g32p_row31_cosetRepresentatives 1401 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1401 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1401) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1401))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1401)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1401 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1401) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1401))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1401)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1402 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1402) = g32p_row31_cosetRepresentatives 1402 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1402 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1402) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1402))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1402)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1402 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1402) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1402))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1402)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1403 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1403) = g32p_row31_cosetRepresentatives 1403 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1403 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1403) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1403))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1403)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1403 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1403) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1403))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1403)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1404 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1404) = g32p_row31_cosetRepresentatives 1404 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1404 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1404) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1404))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1404)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1404 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1404) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1404))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1404)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1405 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1405) = g32p_row31_cosetRepresentatives 1405 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1405 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1405) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1405))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1405)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1405 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1405) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1405))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1405)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1406 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1406) = g32p_row31_cosetRepresentatives 1406 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1406 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1406) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1406))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1406)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1406 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1406) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1406))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1406)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1407 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1407) = g32p_row31_cosetRepresentatives 1407 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1407 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1407) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1407))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1407)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1407 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1407) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1407))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1407)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0087 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 87 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 87 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1392
  · exact g32p_row31_cosetWord_1393
  · exact g32p_row31_cosetWord_1394
  · exact g32p_row31_cosetWord_1395
  · exact g32p_row31_cosetWord_1396
  · exact g32p_row31_cosetWord_1397
  · exact g32p_row31_cosetWord_1398
  · exact g32p_row31_cosetWord_1399
  · exact g32p_row31_cosetWord_1400
  · exact g32p_row31_cosetWord_1401
  · exact g32p_row31_cosetWord_1402
  · exact g32p_row31_cosetWord_1403
  · exact g32p_row31_cosetWord_1404
  · exact g32p_row31_cosetWord_1405
  · exact g32p_row31_cosetWord_1406
  · exact g32p_row31_cosetWord_1407

theorem g32p_row31_cosetGeneratorBlock_0087 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 87 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 87 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 87 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1392 s
  · exact g32p_row31_cosetGeneratorStep_1393 s
  · exact g32p_row31_cosetGeneratorStep_1394 s
  · exact g32p_row31_cosetGeneratorStep_1395 s
  · exact g32p_row31_cosetGeneratorStep_1396 s
  · exact g32p_row31_cosetGeneratorStep_1397 s
  · exact g32p_row31_cosetGeneratorStep_1398 s
  · exact g32p_row31_cosetGeneratorStep_1399 s
  · exact g32p_row31_cosetGeneratorStep_1400 s
  · exact g32p_row31_cosetGeneratorStep_1401 s
  · exact g32p_row31_cosetGeneratorStep_1402 s
  · exact g32p_row31_cosetGeneratorStep_1403 s
  · exact g32p_row31_cosetGeneratorStep_1404 s
  · exact g32p_row31_cosetGeneratorStep_1405 s
  · exact g32p_row31_cosetGeneratorStep_1406 s
  · exact g32p_row31_cosetGeneratorStep_1407 s

theorem g32p_row31_cosetBranchBlock_0087 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 87 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 87 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 87 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1392 s
  · exact g32p_row31_cosetBranchStep_1393 s
  · exact g32p_row31_cosetBranchStep_1394 s
  · exact g32p_row31_cosetBranchStep_1395 s
  · exact g32p_row31_cosetBranchStep_1396 s
  · exact g32p_row31_cosetBranchStep_1397 s
  · exact g32p_row31_cosetBranchStep_1398 s
  · exact g32p_row31_cosetBranchStep_1399 s
  · exact g32p_row31_cosetBranchStep_1400 s
  · exact g32p_row31_cosetBranchStep_1401 s
  · exact g32p_row31_cosetBranchStep_1402 s
  · exact g32p_row31_cosetBranchStep_1403 s
  · exact g32p_row31_cosetBranchStep_1404 s
  · exact g32p_row31_cosetBranchStep_1405 s
  · exact g32p_row31_cosetBranchStep_1406 s
  · exact g32p_row31_cosetBranchStep_1407 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1408 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1408) = g32p_row31_cosetRepresentatives 1408 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1408 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1408) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1408))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1408)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1408 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1408) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1408))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1408)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1409 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1409) = g32p_row31_cosetRepresentatives 1409 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1409 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1409) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1409))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1409)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1409 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1409) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1409))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1409)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1410 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1410) = g32p_row31_cosetRepresentatives 1410 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1410 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1410) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1410))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1410)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1410 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1410) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1410))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1410)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1411 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1411) = g32p_row31_cosetRepresentatives 1411 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1411 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1411) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1411))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1411)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1411 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1411) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1411))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1411)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1412 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1412) = g32p_row31_cosetRepresentatives 1412 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1412 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1412) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1412))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1412)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1412 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1412) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1412))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1412)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1413 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1413) = g32p_row31_cosetRepresentatives 1413 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1413 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1413) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1413))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1413)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1413 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1413) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1413))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1413)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1414 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1414) = g32p_row31_cosetRepresentatives 1414 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1414 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1414) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1414))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1414)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1414 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1414) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1414))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1414)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1415 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1415) = g32p_row31_cosetRepresentatives 1415 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1415 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1415) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1415))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1415)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1415 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1415) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1415))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1415)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1416 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1416) = g32p_row31_cosetRepresentatives 1416 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1416 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1416) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1416))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1416)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1416 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1416) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1416))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1416)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1417 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1417) = g32p_row31_cosetRepresentatives 1417 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1417 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1417) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1417))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1417)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1417 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1417) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1417))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1417)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1418 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1418) = g32p_row31_cosetRepresentatives 1418 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1418 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1418) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1418))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1418)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1418 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1418) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1418))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1418)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1419 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1419) = g32p_row31_cosetRepresentatives 1419 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1419 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1419) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1419))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1419)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1419 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1419) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1419))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1419)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1420 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1420) = g32p_row31_cosetRepresentatives 1420 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1420 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1420) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1420))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1420)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1420 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1420) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1420))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1420)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1421 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1421) = g32p_row31_cosetRepresentatives 1421 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1421 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1421) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1421))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1421)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1421 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1421) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1421))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1421)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1422 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1422) = g32p_row31_cosetRepresentatives 1422 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1422 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1422) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1422))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1422)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1422 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1422) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1422))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1422)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1423 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1423) = g32p_row31_cosetRepresentatives 1423 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1423 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1423) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1423))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1423)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1423 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1423) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1423))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1423)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0088 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 88 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 88 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1408
  · exact g32p_row31_cosetWord_1409
  · exact g32p_row31_cosetWord_1410
  · exact g32p_row31_cosetWord_1411
  · exact g32p_row31_cosetWord_1412
  · exact g32p_row31_cosetWord_1413
  · exact g32p_row31_cosetWord_1414
  · exact g32p_row31_cosetWord_1415
  · exact g32p_row31_cosetWord_1416
  · exact g32p_row31_cosetWord_1417
  · exact g32p_row31_cosetWord_1418
  · exact g32p_row31_cosetWord_1419
  · exact g32p_row31_cosetWord_1420
  · exact g32p_row31_cosetWord_1421
  · exact g32p_row31_cosetWord_1422
  · exact g32p_row31_cosetWord_1423

theorem g32p_row31_cosetGeneratorBlock_0088 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 88 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 88 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 88 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1408 s
  · exact g32p_row31_cosetGeneratorStep_1409 s
  · exact g32p_row31_cosetGeneratorStep_1410 s
  · exact g32p_row31_cosetGeneratorStep_1411 s
  · exact g32p_row31_cosetGeneratorStep_1412 s
  · exact g32p_row31_cosetGeneratorStep_1413 s
  · exact g32p_row31_cosetGeneratorStep_1414 s
  · exact g32p_row31_cosetGeneratorStep_1415 s
  · exact g32p_row31_cosetGeneratorStep_1416 s
  · exact g32p_row31_cosetGeneratorStep_1417 s
  · exact g32p_row31_cosetGeneratorStep_1418 s
  · exact g32p_row31_cosetGeneratorStep_1419 s
  · exact g32p_row31_cosetGeneratorStep_1420 s
  · exact g32p_row31_cosetGeneratorStep_1421 s
  · exact g32p_row31_cosetGeneratorStep_1422 s
  · exact g32p_row31_cosetGeneratorStep_1423 s

theorem g32p_row31_cosetBranchBlock_0088 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 88 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 88 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 88 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1408 s
  · exact g32p_row31_cosetBranchStep_1409 s
  · exact g32p_row31_cosetBranchStep_1410 s
  · exact g32p_row31_cosetBranchStep_1411 s
  · exact g32p_row31_cosetBranchStep_1412 s
  · exact g32p_row31_cosetBranchStep_1413 s
  · exact g32p_row31_cosetBranchStep_1414 s
  · exact g32p_row31_cosetBranchStep_1415 s
  · exact g32p_row31_cosetBranchStep_1416 s
  · exact g32p_row31_cosetBranchStep_1417 s
  · exact g32p_row31_cosetBranchStep_1418 s
  · exact g32p_row31_cosetBranchStep_1419 s
  · exact g32p_row31_cosetBranchStep_1420 s
  · exact g32p_row31_cosetBranchStep_1421 s
  · exact g32p_row31_cosetBranchStep_1422 s
  · exact g32p_row31_cosetBranchStep_1423 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1424 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1424) = g32p_row31_cosetRepresentatives 1424 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1424 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1424) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1424))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1424)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1424 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1424) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1424))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1424)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1425 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1425) = g32p_row31_cosetRepresentatives 1425 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1425 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1425) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1425))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1425)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1425 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1425) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1425))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1425)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1426 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1426) = g32p_row31_cosetRepresentatives 1426 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1426 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1426) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1426))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1426)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1426 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1426) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1426))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1426)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1427 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1427) = g32p_row31_cosetRepresentatives 1427 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1427 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1427) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1427))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1427)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1427 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1427) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1427))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1427)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1428 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1428) = g32p_row31_cosetRepresentatives 1428 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1428 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1428) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1428))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1428)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1428 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1428) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1428))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1428)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1429 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1429) = g32p_row31_cosetRepresentatives 1429 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1429 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1429) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1429))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1429)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1429 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1429) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1429))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1429)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1430 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1430) = g32p_row31_cosetRepresentatives 1430 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1430 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1430) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1430))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1430)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1430 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1430) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1430))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1430)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1431 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1431) = g32p_row31_cosetRepresentatives 1431 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1431 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1431) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1431))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1431)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1431 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1431) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1431))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1431)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1432 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1432) = g32p_row31_cosetRepresentatives 1432 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1432 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1432) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1432))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1432)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1432 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1432) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1432))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1432)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1433 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1433) = g32p_row31_cosetRepresentatives 1433 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1433 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1433) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1433))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1433)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1433 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1433) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1433))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1433)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1434 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1434) = g32p_row31_cosetRepresentatives 1434 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1434 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1434) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1434))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1434)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1434 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1434) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1434))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1434)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1435 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1435) = g32p_row31_cosetRepresentatives 1435 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1435 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1435) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1435))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1435)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1435 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1435) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1435))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1435)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1436 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1436) = g32p_row31_cosetRepresentatives 1436 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1436 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1436) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1436))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1436)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1436 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1436) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1436))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1436)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1437 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1437) = g32p_row31_cosetRepresentatives 1437 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1437 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1437) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1437))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1437)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1437 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1437) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1437))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1437)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1438 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1438) = g32p_row31_cosetRepresentatives 1438 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1438 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1438) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1438))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1438)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1438 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1438) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1438))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1438)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1439 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1439) = g32p_row31_cosetRepresentatives 1439 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1439 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1439) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1439))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1439)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1439 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1439) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1439))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1439)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0089 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 89 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 89 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1424
  · exact g32p_row31_cosetWord_1425
  · exact g32p_row31_cosetWord_1426
  · exact g32p_row31_cosetWord_1427
  · exact g32p_row31_cosetWord_1428
  · exact g32p_row31_cosetWord_1429
  · exact g32p_row31_cosetWord_1430
  · exact g32p_row31_cosetWord_1431
  · exact g32p_row31_cosetWord_1432
  · exact g32p_row31_cosetWord_1433
  · exact g32p_row31_cosetWord_1434
  · exact g32p_row31_cosetWord_1435
  · exact g32p_row31_cosetWord_1436
  · exact g32p_row31_cosetWord_1437
  · exact g32p_row31_cosetWord_1438
  · exact g32p_row31_cosetWord_1439

theorem g32p_row31_cosetGeneratorBlock_0089 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 89 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 89 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 89 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1424 s
  · exact g32p_row31_cosetGeneratorStep_1425 s
  · exact g32p_row31_cosetGeneratorStep_1426 s
  · exact g32p_row31_cosetGeneratorStep_1427 s
  · exact g32p_row31_cosetGeneratorStep_1428 s
  · exact g32p_row31_cosetGeneratorStep_1429 s
  · exact g32p_row31_cosetGeneratorStep_1430 s
  · exact g32p_row31_cosetGeneratorStep_1431 s
  · exact g32p_row31_cosetGeneratorStep_1432 s
  · exact g32p_row31_cosetGeneratorStep_1433 s
  · exact g32p_row31_cosetGeneratorStep_1434 s
  · exact g32p_row31_cosetGeneratorStep_1435 s
  · exact g32p_row31_cosetGeneratorStep_1436 s
  · exact g32p_row31_cosetGeneratorStep_1437 s
  · exact g32p_row31_cosetGeneratorStep_1438 s
  · exact g32p_row31_cosetGeneratorStep_1439 s

theorem g32p_row31_cosetBranchBlock_0089 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 89 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 89 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 89 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1424 s
  · exact g32p_row31_cosetBranchStep_1425 s
  · exact g32p_row31_cosetBranchStep_1426 s
  · exact g32p_row31_cosetBranchStep_1427 s
  · exact g32p_row31_cosetBranchStep_1428 s
  · exact g32p_row31_cosetBranchStep_1429 s
  · exact g32p_row31_cosetBranchStep_1430 s
  · exact g32p_row31_cosetBranchStep_1431 s
  · exact g32p_row31_cosetBranchStep_1432 s
  · exact g32p_row31_cosetBranchStep_1433 s
  · exact g32p_row31_cosetBranchStep_1434 s
  · exact g32p_row31_cosetBranchStep_1435 s
  · exact g32p_row31_cosetBranchStep_1436 s
  · exact g32p_row31_cosetBranchStep_1437 s
  · exact g32p_row31_cosetBranchStep_1438 s
  · exact g32p_row31_cosetBranchStep_1439 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1440 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1440) = g32p_row31_cosetRepresentatives 1440 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1440 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1440) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1440))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1440)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1440 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1440) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1440))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1440)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1441 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1441) = g32p_row31_cosetRepresentatives 1441 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1441 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1441) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1441))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1441)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1441 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1441) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1441))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1441)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1442 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1442) = g32p_row31_cosetRepresentatives 1442 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1442 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1442) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1442))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1442)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1442 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1442) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1442))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1442)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1443 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1443) = g32p_row31_cosetRepresentatives 1443 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1443 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1443) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1443))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1443)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1443 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1443) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1443))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1443)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1444 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1444) = g32p_row31_cosetRepresentatives 1444 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1444 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1444) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1444))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1444)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1444 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1444) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1444))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1444)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1445 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1445) = g32p_row31_cosetRepresentatives 1445 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1445 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1445) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1445))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1445)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1445 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1445) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1445))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1445)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1446 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1446) = g32p_row31_cosetRepresentatives 1446 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1446 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1446) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1446))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1446)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1446 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1446) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1446))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1446)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1447 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1447) = g32p_row31_cosetRepresentatives 1447 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1447 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1447) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1447))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1447)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1447 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1447) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1447))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1447)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1448 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1448) = g32p_row31_cosetRepresentatives 1448 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1448 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1448) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1448))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1448)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1448 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1448) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1448))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1448)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1449 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1449) = g32p_row31_cosetRepresentatives 1449 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1449 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1449) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1449))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1449)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1449 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1449) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1449))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1449)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1450 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1450) = g32p_row31_cosetRepresentatives 1450 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1450 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1450) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1450))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1450)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1450 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1450) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1450))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1450)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1451 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1451) = g32p_row31_cosetRepresentatives 1451 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1451 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1451) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1451))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1451)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1451 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1451) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1451))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1451)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1452 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1452) = g32p_row31_cosetRepresentatives 1452 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1452 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1452) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1452))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1452)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1452 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1452) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1452))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1452)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1453 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1453) = g32p_row31_cosetRepresentatives 1453 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1453 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1453) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1453))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1453)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1453 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1453) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1453))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1453)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1454 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1454) = g32p_row31_cosetRepresentatives 1454 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1454 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1454) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1454))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1454)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1454 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1454) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1454))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1454)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1455 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1455) = g32p_row31_cosetRepresentatives 1455 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1455 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1455) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1455))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1455)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1455 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1455) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1455))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1455)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0090 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 90 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 90 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1440
  · exact g32p_row31_cosetWord_1441
  · exact g32p_row31_cosetWord_1442
  · exact g32p_row31_cosetWord_1443
  · exact g32p_row31_cosetWord_1444
  · exact g32p_row31_cosetWord_1445
  · exact g32p_row31_cosetWord_1446
  · exact g32p_row31_cosetWord_1447
  · exact g32p_row31_cosetWord_1448
  · exact g32p_row31_cosetWord_1449
  · exact g32p_row31_cosetWord_1450
  · exact g32p_row31_cosetWord_1451
  · exact g32p_row31_cosetWord_1452
  · exact g32p_row31_cosetWord_1453
  · exact g32p_row31_cosetWord_1454
  · exact g32p_row31_cosetWord_1455

theorem g32p_row31_cosetGeneratorBlock_0090 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 90 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 90 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 90 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1440 s
  · exact g32p_row31_cosetGeneratorStep_1441 s
  · exact g32p_row31_cosetGeneratorStep_1442 s
  · exact g32p_row31_cosetGeneratorStep_1443 s
  · exact g32p_row31_cosetGeneratorStep_1444 s
  · exact g32p_row31_cosetGeneratorStep_1445 s
  · exact g32p_row31_cosetGeneratorStep_1446 s
  · exact g32p_row31_cosetGeneratorStep_1447 s
  · exact g32p_row31_cosetGeneratorStep_1448 s
  · exact g32p_row31_cosetGeneratorStep_1449 s
  · exact g32p_row31_cosetGeneratorStep_1450 s
  · exact g32p_row31_cosetGeneratorStep_1451 s
  · exact g32p_row31_cosetGeneratorStep_1452 s
  · exact g32p_row31_cosetGeneratorStep_1453 s
  · exact g32p_row31_cosetGeneratorStep_1454 s
  · exact g32p_row31_cosetGeneratorStep_1455 s

theorem g32p_row31_cosetBranchBlock_0090 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 90 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 90 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 90 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1440 s
  · exact g32p_row31_cosetBranchStep_1441 s
  · exact g32p_row31_cosetBranchStep_1442 s
  · exact g32p_row31_cosetBranchStep_1443 s
  · exact g32p_row31_cosetBranchStep_1444 s
  · exact g32p_row31_cosetBranchStep_1445 s
  · exact g32p_row31_cosetBranchStep_1446 s
  · exact g32p_row31_cosetBranchStep_1447 s
  · exact g32p_row31_cosetBranchStep_1448 s
  · exact g32p_row31_cosetBranchStep_1449 s
  · exact g32p_row31_cosetBranchStep_1450 s
  · exact g32p_row31_cosetBranchStep_1451 s
  · exact g32p_row31_cosetBranchStep_1452 s
  · exact g32p_row31_cosetBranchStep_1453 s
  · exact g32p_row31_cosetBranchStep_1454 s
  · exact g32p_row31_cosetBranchStep_1455 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1456 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1456) = g32p_row31_cosetRepresentatives 1456 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1456 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1456) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1456))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1456)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1456 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1456) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1456))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1456)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1457 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1457) = g32p_row31_cosetRepresentatives 1457 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1457 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1457) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1457))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1457)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1457 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1457) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1457))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1457)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1458 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1458) = g32p_row31_cosetRepresentatives 1458 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1458 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1458) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1458))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1458)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1458 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1458) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1458))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1458)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1459 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1459) = g32p_row31_cosetRepresentatives 1459 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1459 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1459) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1459))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1459)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1459 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1459) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1459))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1459)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1460 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1460) = g32p_row31_cosetRepresentatives 1460 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1460 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1460) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1460))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1460)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1460 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1460) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1460))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1460)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1461 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1461) = g32p_row31_cosetRepresentatives 1461 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1461 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1461) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1461))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1461)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1461 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1461) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1461))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1461)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1462 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1462) = g32p_row31_cosetRepresentatives 1462 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1462 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1462) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1462))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1462)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1462 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1462) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1462))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1462)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1463 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1463) = g32p_row31_cosetRepresentatives 1463 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1463 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1463) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1463))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1463)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1463 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1463) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1463))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1463)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1464 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1464) = g32p_row31_cosetRepresentatives 1464 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1464 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1464) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1464))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1464)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1464 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1464) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1464))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1464)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1465 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1465) = g32p_row31_cosetRepresentatives 1465 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1465 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1465) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1465))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1465)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1465 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1465) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1465))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1465)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1466 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1466) = g32p_row31_cosetRepresentatives 1466 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1466 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1466) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1466))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1466)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1466 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1466) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1466))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1466)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1467 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1467) = g32p_row31_cosetRepresentatives 1467 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1467 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1467) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1467))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1467)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1467 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1467) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1467))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1467)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1468 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1468) = g32p_row31_cosetRepresentatives 1468 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1468 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1468) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1468))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1468)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1468 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1468) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1468))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1468)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1469 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1469) = g32p_row31_cosetRepresentatives 1469 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1469 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1469) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1469))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1469)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1469 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1469) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1469))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1469)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1470 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1470) = g32p_row31_cosetRepresentatives 1470 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1470 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1470) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1470))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1470)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1470 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1470) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1470))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1470)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1471 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1471) = g32p_row31_cosetRepresentatives 1471 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1471 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1471) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1471))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1471)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1471 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1471) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1471))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1471)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0091 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 91 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 91 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1456
  · exact g32p_row31_cosetWord_1457
  · exact g32p_row31_cosetWord_1458
  · exact g32p_row31_cosetWord_1459
  · exact g32p_row31_cosetWord_1460
  · exact g32p_row31_cosetWord_1461
  · exact g32p_row31_cosetWord_1462
  · exact g32p_row31_cosetWord_1463
  · exact g32p_row31_cosetWord_1464
  · exact g32p_row31_cosetWord_1465
  · exact g32p_row31_cosetWord_1466
  · exact g32p_row31_cosetWord_1467
  · exact g32p_row31_cosetWord_1468
  · exact g32p_row31_cosetWord_1469
  · exact g32p_row31_cosetWord_1470
  · exact g32p_row31_cosetWord_1471

theorem g32p_row31_cosetGeneratorBlock_0091 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 91 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 91 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 91 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1456 s
  · exact g32p_row31_cosetGeneratorStep_1457 s
  · exact g32p_row31_cosetGeneratorStep_1458 s
  · exact g32p_row31_cosetGeneratorStep_1459 s
  · exact g32p_row31_cosetGeneratorStep_1460 s
  · exact g32p_row31_cosetGeneratorStep_1461 s
  · exact g32p_row31_cosetGeneratorStep_1462 s
  · exact g32p_row31_cosetGeneratorStep_1463 s
  · exact g32p_row31_cosetGeneratorStep_1464 s
  · exact g32p_row31_cosetGeneratorStep_1465 s
  · exact g32p_row31_cosetGeneratorStep_1466 s
  · exact g32p_row31_cosetGeneratorStep_1467 s
  · exact g32p_row31_cosetGeneratorStep_1468 s
  · exact g32p_row31_cosetGeneratorStep_1469 s
  · exact g32p_row31_cosetGeneratorStep_1470 s
  · exact g32p_row31_cosetGeneratorStep_1471 s

theorem g32p_row31_cosetBranchBlock_0091 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 91 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 91 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 91 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1456 s
  · exact g32p_row31_cosetBranchStep_1457 s
  · exact g32p_row31_cosetBranchStep_1458 s
  · exact g32p_row31_cosetBranchStep_1459 s
  · exact g32p_row31_cosetBranchStep_1460 s
  · exact g32p_row31_cosetBranchStep_1461 s
  · exact g32p_row31_cosetBranchStep_1462 s
  · exact g32p_row31_cosetBranchStep_1463 s
  · exact g32p_row31_cosetBranchStep_1464 s
  · exact g32p_row31_cosetBranchStep_1465 s
  · exact g32p_row31_cosetBranchStep_1466 s
  · exact g32p_row31_cosetBranchStep_1467 s
  · exact g32p_row31_cosetBranchStep_1468 s
  · exact g32p_row31_cosetBranchStep_1469 s
  · exact g32p_row31_cosetBranchStep_1470 s
  · exact g32p_row31_cosetBranchStep_1471 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1472 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1472) = g32p_row31_cosetRepresentatives 1472 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1472 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1472) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1472))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1472)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1472 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1472) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1472))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1472)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1473 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1473) = g32p_row31_cosetRepresentatives 1473 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1473 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1473) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1473))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1473)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1473 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1473) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1473))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1473)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1474 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1474) = g32p_row31_cosetRepresentatives 1474 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1474 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1474) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1474))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1474)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1474 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1474) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1474))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1474)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1475 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1475) = g32p_row31_cosetRepresentatives 1475 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1475 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1475) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1475))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1475)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1475 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1475) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1475))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1475)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1476 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1476) = g32p_row31_cosetRepresentatives 1476 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1476 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1476) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1476))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1476)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1476 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1476) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1476))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1476)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1477 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1477) = g32p_row31_cosetRepresentatives 1477 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1477 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1477) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1477))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1477)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1477 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1477) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1477))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1477)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1478 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1478) = g32p_row31_cosetRepresentatives 1478 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1478 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1478) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1478))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1478)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1478 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1478) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1478))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1478)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1479 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1479) = g32p_row31_cosetRepresentatives 1479 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1479 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1479) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1479))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1479)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1479 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1479) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1479))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1479)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1480 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1480) = g32p_row31_cosetRepresentatives 1480 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1480 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1480) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1480))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1480)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1480 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1480) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1480))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1480)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1481 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1481) = g32p_row31_cosetRepresentatives 1481 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1481 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1481) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1481))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1481)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1481 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1481) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1481))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1481)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1482 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1482) = g32p_row31_cosetRepresentatives 1482 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1482 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1482) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1482))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1482)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1482 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1482) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1482))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1482)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1483 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1483) = g32p_row31_cosetRepresentatives 1483 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1483 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1483) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1483))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1483)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1483 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1483) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1483))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1483)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1484 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1484) = g32p_row31_cosetRepresentatives 1484 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1484 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1484) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1484))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1484)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1484 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1484) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1484))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1484)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1485 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1485) = g32p_row31_cosetRepresentatives 1485 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1485 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1485) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1485))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1485)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1485 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1485) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1485))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1485)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1486 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1486) = g32p_row31_cosetRepresentatives 1486 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1486 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1486) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1486))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1486)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1486 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1486) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1486))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1486)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1487 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1487) = g32p_row31_cosetRepresentatives 1487 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1487 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1487) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1487))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1487)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1487 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1487) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1487))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1487)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0092 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 92 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 92 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1472
  · exact g32p_row31_cosetWord_1473
  · exact g32p_row31_cosetWord_1474
  · exact g32p_row31_cosetWord_1475
  · exact g32p_row31_cosetWord_1476
  · exact g32p_row31_cosetWord_1477
  · exact g32p_row31_cosetWord_1478
  · exact g32p_row31_cosetWord_1479
  · exact g32p_row31_cosetWord_1480
  · exact g32p_row31_cosetWord_1481
  · exact g32p_row31_cosetWord_1482
  · exact g32p_row31_cosetWord_1483
  · exact g32p_row31_cosetWord_1484
  · exact g32p_row31_cosetWord_1485
  · exact g32p_row31_cosetWord_1486
  · exact g32p_row31_cosetWord_1487

theorem g32p_row31_cosetGeneratorBlock_0092 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 92 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 92 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 92 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1472 s
  · exact g32p_row31_cosetGeneratorStep_1473 s
  · exact g32p_row31_cosetGeneratorStep_1474 s
  · exact g32p_row31_cosetGeneratorStep_1475 s
  · exact g32p_row31_cosetGeneratorStep_1476 s
  · exact g32p_row31_cosetGeneratorStep_1477 s
  · exact g32p_row31_cosetGeneratorStep_1478 s
  · exact g32p_row31_cosetGeneratorStep_1479 s
  · exact g32p_row31_cosetGeneratorStep_1480 s
  · exact g32p_row31_cosetGeneratorStep_1481 s
  · exact g32p_row31_cosetGeneratorStep_1482 s
  · exact g32p_row31_cosetGeneratorStep_1483 s
  · exact g32p_row31_cosetGeneratorStep_1484 s
  · exact g32p_row31_cosetGeneratorStep_1485 s
  · exact g32p_row31_cosetGeneratorStep_1486 s
  · exact g32p_row31_cosetGeneratorStep_1487 s

theorem g32p_row31_cosetBranchBlock_0092 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 92 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 92 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 92 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1472 s
  · exact g32p_row31_cosetBranchStep_1473 s
  · exact g32p_row31_cosetBranchStep_1474 s
  · exact g32p_row31_cosetBranchStep_1475 s
  · exact g32p_row31_cosetBranchStep_1476 s
  · exact g32p_row31_cosetBranchStep_1477 s
  · exact g32p_row31_cosetBranchStep_1478 s
  · exact g32p_row31_cosetBranchStep_1479 s
  · exact g32p_row31_cosetBranchStep_1480 s
  · exact g32p_row31_cosetBranchStep_1481 s
  · exact g32p_row31_cosetBranchStep_1482 s
  · exact g32p_row31_cosetBranchStep_1483 s
  · exact g32p_row31_cosetBranchStep_1484 s
  · exact g32p_row31_cosetBranchStep_1485 s
  · exact g32p_row31_cosetBranchStep_1486 s
  · exact g32p_row31_cosetBranchStep_1487 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1488 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1488) = g32p_row31_cosetRepresentatives 1488 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1488 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1488) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1488))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1488)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1488 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1488) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1488))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1488)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1489 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1489) = g32p_row31_cosetRepresentatives 1489 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1489 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1489) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1489))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1489)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1489 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1489) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1489))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1489)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1490 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1490) = g32p_row31_cosetRepresentatives 1490 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1490 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1490) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1490))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1490)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1490 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1490) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1490))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1490)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1491 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1491) = g32p_row31_cosetRepresentatives 1491 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1491 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1491) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1491))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1491)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1491 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1491) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1491))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1491)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1492 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1492) = g32p_row31_cosetRepresentatives 1492 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1492 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1492) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1492))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1492)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1492 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1492) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1492))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1492)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1493 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1493) = g32p_row31_cosetRepresentatives 1493 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1493 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1493) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1493))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1493)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1493 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1493) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1493))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1493)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1494 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1494) = g32p_row31_cosetRepresentatives 1494 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1494 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1494) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1494))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1494)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1494 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1494) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1494))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1494)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1495 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1495) = g32p_row31_cosetRepresentatives 1495 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1495 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1495) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1495))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1495)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1495 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1495) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1495))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1495)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1496 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1496) = g32p_row31_cosetRepresentatives 1496 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1496 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1496) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1496))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1496)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1496 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1496) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1496))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1496)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1497 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1497) = g32p_row31_cosetRepresentatives 1497 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1497 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1497) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1497))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1497)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1497 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1497) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1497))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1497)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1498 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1498) = g32p_row31_cosetRepresentatives 1498 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1498 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1498) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1498))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1498)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1498 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1498) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1498))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1498)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1499 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1499) = g32p_row31_cosetRepresentatives 1499 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1499 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1499) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1499))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1499)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1499 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1499) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1499))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1499)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1500 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1500) = g32p_row31_cosetRepresentatives 1500 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1500 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1500) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1500))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1500)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1500 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1500) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1500))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1500)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1501 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1501) = g32p_row31_cosetRepresentatives 1501 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1501 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1501) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1501))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1501)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1501 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1501) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1501))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1501)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1502 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1502) = g32p_row31_cosetRepresentatives 1502 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1502 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1502) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1502))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1502)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1502 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1502) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1502))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1502)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1503 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1503) = g32p_row31_cosetRepresentatives 1503 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1503 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1503) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1503))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1503)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1503 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1503) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1503))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1503)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0093 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 93 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 93 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1488
  · exact g32p_row31_cosetWord_1489
  · exact g32p_row31_cosetWord_1490
  · exact g32p_row31_cosetWord_1491
  · exact g32p_row31_cosetWord_1492
  · exact g32p_row31_cosetWord_1493
  · exact g32p_row31_cosetWord_1494
  · exact g32p_row31_cosetWord_1495
  · exact g32p_row31_cosetWord_1496
  · exact g32p_row31_cosetWord_1497
  · exact g32p_row31_cosetWord_1498
  · exact g32p_row31_cosetWord_1499
  · exact g32p_row31_cosetWord_1500
  · exact g32p_row31_cosetWord_1501
  · exact g32p_row31_cosetWord_1502
  · exact g32p_row31_cosetWord_1503

theorem g32p_row31_cosetGeneratorBlock_0093 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 93 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 93 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 93 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1488 s
  · exact g32p_row31_cosetGeneratorStep_1489 s
  · exact g32p_row31_cosetGeneratorStep_1490 s
  · exact g32p_row31_cosetGeneratorStep_1491 s
  · exact g32p_row31_cosetGeneratorStep_1492 s
  · exact g32p_row31_cosetGeneratorStep_1493 s
  · exact g32p_row31_cosetGeneratorStep_1494 s
  · exact g32p_row31_cosetGeneratorStep_1495 s
  · exact g32p_row31_cosetGeneratorStep_1496 s
  · exact g32p_row31_cosetGeneratorStep_1497 s
  · exact g32p_row31_cosetGeneratorStep_1498 s
  · exact g32p_row31_cosetGeneratorStep_1499 s
  · exact g32p_row31_cosetGeneratorStep_1500 s
  · exact g32p_row31_cosetGeneratorStep_1501 s
  · exact g32p_row31_cosetGeneratorStep_1502 s
  · exact g32p_row31_cosetGeneratorStep_1503 s

theorem g32p_row31_cosetBranchBlock_0093 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 93 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 93 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 93 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1488 s
  · exact g32p_row31_cosetBranchStep_1489 s
  · exact g32p_row31_cosetBranchStep_1490 s
  · exact g32p_row31_cosetBranchStep_1491 s
  · exact g32p_row31_cosetBranchStep_1492 s
  · exact g32p_row31_cosetBranchStep_1493 s
  · exact g32p_row31_cosetBranchStep_1494 s
  · exact g32p_row31_cosetBranchStep_1495 s
  · exact g32p_row31_cosetBranchStep_1496 s
  · exact g32p_row31_cosetBranchStep_1497 s
  · exact g32p_row31_cosetBranchStep_1498 s
  · exact g32p_row31_cosetBranchStep_1499 s
  · exact g32p_row31_cosetBranchStep_1500 s
  · exact g32p_row31_cosetBranchStep_1501 s
  · exact g32p_row31_cosetBranchStep_1502 s
  · exact g32p_row31_cosetBranchStep_1503 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1504 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1504) = g32p_row31_cosetRepresentatives 1504 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1504 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1504) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1504))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1504)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1504 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1504) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1504))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1504)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1505 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1505) = g32p_row31_cosetRepresentatives 1505 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1505 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1505) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1505))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1505)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1505 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1505) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1505))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1505)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1506 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1506) = g32p_row31_cosetRepresentatives 1506 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1506 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1506) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1506))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1506)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1506 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1506) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1506))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1506)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1507 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1507) = g32p_row31_cosetRepresentatives 1507 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1507 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1507) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1507))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1507)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1507 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1507) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1507))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1507)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1508 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1508) = g32p_row31_cosetRepresentatives 1508 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1508 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1508) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1508))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1508)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1508 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1508) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1508))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1508)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1509 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1509) = g32p_row31_cosetRepresentatives 1509 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1509 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1509) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1509))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1509)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1509 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1509) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1509))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1509)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1510 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1510) = g32p_row31_cosetRepresentatives 1510 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1510 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1510) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1510))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1510)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1510 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1510) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1510))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1510)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1511 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1511) = g32p_row31_cosetRepresentatives 1511 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1511 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1511) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1511))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1511)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1511 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1511) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1511))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1511)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1512 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1512) = g32p_row31_cosetRepresentatives 1512 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1512 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1512) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1512))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1512)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1512 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1512) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1512))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1512)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1513 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1513) = g32p_row31_cosetRepresentatives 1513 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1513 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1513) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1513))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1513)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1513 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1513) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1513))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1513)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1514 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1514) = g32p_row31_cosetRepresentatives 1514 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1514 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1514) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1514))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1514)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1514 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1514) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1514))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1514)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1515 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1515) = g32p_row31_cosetRepresentatives 1515 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1515 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1515) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1515))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1515)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1515 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1515) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1515))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1515)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1516 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1516) = g32p_row31_cosetRepresentatives 1516 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1516 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1516) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1516))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1516)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1516 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1516) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1516))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1516)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1517 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1517) = g32p_row31_cosetRepresentatives 1517 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1517 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1517) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1517))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1517)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1517 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1517) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1517))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1517)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1518 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1518) = g32p_row31_cosetRepresentatives 1518 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1518 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1518) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1518))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1518)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1518 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1518) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1518))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1518)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1519 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1519) = g32p_row31_cosetRepresentatives 1519 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1519 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1519) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1519))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1519)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1519 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1519) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1519))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1519)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0094 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 94 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 94 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1504
  · exact g32p_row31_cosetWord_1505
  · exact g32p_row31_cosetWord_1506
  · exact g32p_row31_cosetWord_1507
  · exact g32p_row31_cosetWord_1508
  · exact g32p_row31_cosetWord_1509
  · exact g32p_row31_cosetWord_1510
  · exact g32p_row31_cosetWord_1511
  · exact g32p_row31_cosetWord_1512
  · exact g32p_row31_cosetWord_1513
  · exact g32p_row31_cosetWord_1514
  · exact g32p_row31_cosetWord_1515
  · exact g32p_row31_cosetWord_1516
  · exact g32p_row31_cosetWord_1517
  · exact g32p_row31_cosetWord_1518
  · exact g32p_row31_cosetWord_1519

theorem g32p_row31_cosetGeneratorBlock_0094 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 94 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 94 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 94 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1504 s
  · exact g32p_row31_cosetGeneratorStep_1505 s
  · exact g32p_row31_cosetGeneratorStep_1506 s
  · exact g32p_row31_cosetGeneratorStep_1507 s
  · exact g32p_row31_cosetGeneratorStep_1508 s
  · exact g32p_row31_cosetGeneratorStep_1509 s
  · exact g32p_row31_cosetGeneratorStep_1510 s
  · exact g32p_row31_cosetGeneratorStep_1511 s
  · exact g32p_row31_cosetGeneratorStep_1512 s
  · exact g32p_row31_cosetGeneratorStep_1513 s
  · exact g32p_row31_cosetGeneratorStep_1514 s
  · exact g32p_row31_cosetGeneratorStep_1515 s
  · exact g32p_row31_cosetGeneratorStep_1516 s
  · exact g32p_row31_cosetGeneratorStep_1517 s
  · exact g32p_row31_cosetGeneratorStep_1518 s
  · exact g32p_row31_cosetGeneratorStep_1519 s

theorem g32p_row31_cosetBranchBlock_0094 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 94 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 94 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 94 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1504 s
  · exact g32p_row31_cosetBranchStep_1505 s
  · exact g32p_row31_cosetBranchStep_1506 s
  · exact g32p_row31_cosetBranchStep_1507 s
  · exact g32p_row31_cosetBranchStep_1508 s
  · exact g32p_row31_cosetBranchStep_1509 s
  · exact g32p_row31_cosetBranchStep_1510 s
  · exact g32p_row31_cosetBranchStep_1511 s
  · exact g32p_row31_cosetBranchStep_1512 s
  · exact g32p_row31_cosetBranchStep_1513 s
  · exact g32p_row31_cosetBranchStep_1514 s
  · exact g32p_row31_cosetBranchStep_1515 s
  · exact g32p_row31_cosetBranchStep_1516 s
  · exact g32p_row31_cosetBranchStep_1517 s
  · exact g32p_row31_cosetBranchStep_1518 s
  · exact g32p_row31_cosetBranchStep_1519 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_1520 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1520) = g32p_row31_cosetRepresentatives 1520 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1520 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1520) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1520))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1520)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1520 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1520) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1520))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1520)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1521 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1521) = g32p_row31_cosetRepresentatives 1521 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1521 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1521) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1521))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1521)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1521 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1521) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1521))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1521)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1522 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1522) = g32p_row31_cosetRepresentatives 1522 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1522 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1522) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1522))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1522)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1522 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1522) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1522))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1522)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1523 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1523) = g32p_row31_cosetRepresentatives 1523 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1523 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1523) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1523))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1523)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1523 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1523) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1523))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1523)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1524 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1524) = g32p_row31_cosetRepresentatives 1524 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1524 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1524) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1524))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1524)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1524 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1524) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1524))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1524)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1525 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1525) = g32p_row31_cosetRepresentatives 1525 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1525 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1525) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1525))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1525)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1525 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1525) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1525))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1525)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1526 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1526) = g32p_row31_cosetRepresentatives 1526 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1526 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1526) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1526))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1526)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1526 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1526) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1526))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1526)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1527 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1527) = g32p_row31_cosetRepresentatives 1527 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1527 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1527) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1527))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1527)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1527 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1527) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1527))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1527)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1528 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1528) = g32p_row31_cosetRepresentatives 1528 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1528 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1528) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1528))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1528)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1528 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1528) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1528))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1528)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1529 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1529) = g32p_row31_cosetRepresentatives 1529 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1529 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1529) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1529))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1529)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1529 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1529) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1529))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1529)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1530 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1530) = g32p_row31_cosetRepresentatives 1530 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1530 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1530) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1530))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1530)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1530 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1530) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1530))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1530)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1531 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1531) = g32p_row31_cosetRepresentatives 1531 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1531 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1531) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1531))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1531)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1531 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1531) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1531))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1531)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1532 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1532) = g32p_row31_cosetRepresentatives 1532 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1532 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1532) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1532))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1532)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1532 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1532) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1532))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1532)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1533 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1533) = g32p_row31_cosetRepresentatives 1533 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1533 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1533) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1533))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1533)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1533 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1533) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1533))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1533)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1534 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1534) = g32p_row31_cosetRepresentatives 1534 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1534 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1534) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1534))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1534)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1534 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1534) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1534))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1534)) := by
  decide +kernel

theorem g32p_row31_cosetWord_1535 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 1535) = g32p_row31_cosetRepresentatives 1535 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_1535 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 1535) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 1535))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 1535)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_1535 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 1535) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 1535))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 1535)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0095 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 95 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 95 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_1520
  · exact g32p_row31_cosetWord_1521
  · exact g32p_row31_cosetWord_1522
  · exact g32p_row31_cosetWord_1523
  · exact g32p_row31_cosetWord_1524
  · exact g32p_row31_cosetWord_1525
  · exact g32p_row31_cosetWord_1526
  · exact g32p_row31_cosetWord_1527
  · exact g32p_row31_cosetWord_1528
  · exact g32p_row31_cosetWord_1529
  · exact g32p_row31_cosetWord_1530
  · exact g32p_row31_cosetWord_1531
  · exact g32p_row31_cosetWord_1532
  · exact g32p_row31_cosetWord_1533
  · exact g32p_row31_cosetWord_1534
  · exact g32p_row31_cosetWord_1535

theorem g32p_row31_cosetGeneratorBlock_0095 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 95 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 95 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 95 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_1520 s
  · exact g32p_row31_cosetGeneratorStep_1521 s
  · exact g32p_row31_cosetGeneratorStep_1522 s
  · exact g32p_row31_cosetGeneratorStep_1523 s
  · exact g32p_row31_cosetGeneratorStep_1524 s
  · exact g32p_row31_cosetGeneratorStep_1525 s
  · exact g32p_row31_cosetGeneratorStep_1526 s
  · exact g32p_row31_cosetGeneratorStep_1527 s
  · exact g32p_row31_cosetGeneratorStep_1528 s
  · exact g32p_row31_cosetGeneratorStep_1529 s
  · exact g32p_row31_cosetGeneratorStep_1530 s
  · exact g32p_row31_cosetGeneratorStep_1531 s
  · exact g32p_row31_cosetGeneratorStep_1532 s
  · exact g32p_row31_cosetGeneratorStep_1533 s
  · exact g32p_row31_cosetGeneratorStep_1534 s
  · exact g32p_row31_cosetGeneratorStep_1535 s

theorem g32p_row31_cosetBranchBlock_0095 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 95 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 95 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 95 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_1520 s
  · exact g32p_row31_cosetBranchStep_1521 s
  · exact g32p_row31_cosetBranchStep_1522 s
  · exact g32p_row31_cosetBranchStep_1523 s
  · exact g32p_row31_cosetBranchStep_1524 s
  · exact g32p_row31_cosetBranchStep_1525 s
  · exact g32p_row31_cosetBranchStep_1526 s
  · exact g32p_row31_cosetBranchStep_1527 s
  · exact g32p_row31_cosetBranchStep_1528 s
  · exact g32p_row31_cosetBranchStep_1529 s
  · exact g32p_row31_cosetBranchStep_1530 s
  · exact g32p_row31_cosetBranchStep_1531 s
  · exact g32p_row31_cosetBranchStep_1532 s
  · exact g32p_row31_cosetBranchStep_1533 s
  · exact g32p_row31_cosetBranchStep_1534 s
  · exact g32p_row31_cosetBranchStep_1535 s


end HodgeLean.Foundations.Program

end
