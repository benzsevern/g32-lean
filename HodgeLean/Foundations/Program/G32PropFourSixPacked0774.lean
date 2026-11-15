import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness23CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0769
import HodgeLean.Foundations.Program.G32PropFourSixPacked0770
import HodgeLean.Foundations.Program.G32PropFourSixPacked0771
import HodgeLean.Foundations.Program.G32PropFourSixPacked0772
import HodgeLean.Foundations.Program.G32PropFourSixPacked0773
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow23
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1280 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1280) = g32p_row23_cosetRepresentatives 1280 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1280) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1280))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1280)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1280) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1280))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1280)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1281 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1281) = g32p_row23_cosetRepresentatives 1281 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1281) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1281))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1281)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1281) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1281))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1281)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1282 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1282) = g32p_row23_cosetRepresentatives 1282 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1282) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1282))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1282)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1282) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1282))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1282)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1283 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1283) = g32p_row23_cosetRepresentatives 1283 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1283) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1283))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1283)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1283) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1283))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1283)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1284 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1284) = g32p_row23_cosetRepresentatives 1284 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1284) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1284))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1284)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1284) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1284))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1284)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1285 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1285) = g32p_row23_cosetRepresentatives 1285 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1285) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1285))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1285)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1285) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1285))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1285)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1286 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1286) = g32p_row23_cosetRepresentatives 1286 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1286) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1286))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1286)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1286) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1286))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1286)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1287 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1287) = g32p_row23_cosetRepresentatives 1287 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1287) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1287))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1287)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1287) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1287))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1287)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1288 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1288) = g32p_row23_cosetRepresentatives 1288 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1288) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1288))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1288)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1288) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1288))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1288)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1289 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1289) = g32p_row23_cosetRepresentatives 1289 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1289) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1289))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1289)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1289) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1289))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1289)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1290 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1290) = g32p_row23_cosetRepresentatives 1290 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1290) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1290))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1290)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1290) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1290))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1290)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1291 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1291) = g32p_row23_cosetRepresentatives 1291 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1291) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1291))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1291)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1291) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1291))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1291)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1292 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1292) = g32p_row23_cosetRepresentatives 1292 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1292) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1292))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1292)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1292) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1292))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1292)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1293 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1293) = g32p_row23_cosetRepresentatives 1293 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1293) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1293))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1293)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1293) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1293))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1293)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1294 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1294) = g32p_row23_cosetRepresentatives 1294 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1294) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1294))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1294)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1294) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1294))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1294)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1295 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1295) = g32p_row23_cosetRepresentatives 1295 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1295) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1295))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1295)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1295) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1295))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1295)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0080 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 80 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 80 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1280
  · exact g32p_row23_cosetWord_1281
  · exact g32p_row23_cosetWord_1282
  · exact g32p_row23_cosetWord_1283
  · exact g32p_row23_cosetWord_1284
  · exact g32p_row23_cosetWord_1285
  · exact g32p_row23_cosetWord_1286
  · exact g32p_row23_cosetWord_1287
  · exact g32p_row23_cosetWord_1288
  · exact g32p_row23_cosetWord_1289
  · exact g32p_row23_cosetWord_1290
  · exact g32p_row23_cosetWord_1291
  · exact g32p_row23_cosetWord_1292
  · exact g32p_row23_cosetWord_1293
  · exact g32p_row23_cosetWord_1294
  · exact g32p_row23_cosetWord_1295

theorem g32p_row23_cosetGeneratorBlock_0080 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 80 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 80 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 80 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1280 s
  · exact g32p_row23_cosetGeneratorStep_1281 s
  · exact g32p_row23_cosetGeneratorStep_1282 s
  · exact g32p_row23_cosetGeneratorStep_1283 s
  · exact g32p_row23_cosetGeneratorStep_1284 s
  · exact g32p_row23_cosetGeneratorStep_1285 s
  · exact g32p_row23_cosetGeneratorStep_1286 s
  · exact g32p_row23_cosetGeneratorStep_1287 s
  · exact g32p_row23_cosetGeneratorStep_1288 s
  · exact g32p_row23_cosetGeneratorStep_1289 s
  · exact g32p_row23_cosetGeneratorStep_1290 s
  · exact g32p_row23_cosetGeneratorStep_1291 s
  · exact g32p_row23_cosetGeneratorStep_1292 s
  · exact g32p_row23_cosetGeneratorStep_1293 s
  · exact g32p_row23_cosetGeneratorStep_1294 s
  · exact g32p_row23_cosetGeneratorStep_1295 s

theorem g32p_row23_cosetBranchBlock_0080 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 80 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 80 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 80 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1280 s
  · exact g32p_row23_cosetBranchStep_1281 s
  · exact g32p_row23_cosetBranchStep_1282 s
  · exact g32p_row23_cosetBranchStep_1283 s
  · exact g32p_row23_cosetBranchStep_1284 s
  · exact g32p_row23_cosetBranchStep_1285 s
  · exact g32p_row23_cosetBranchStep_1286 s
  · exact g32p_row23_cosetBranchStep_1287 s
  · exact g32p_row23_cosetBranchStep_1288 s
  · exact g32p_row23_cosetBranchStep_1289 s
  · exact g32p_row23_cosetBranchStep_1290 s
  · exact g32p_row23_cosetBranchStep_1291 s
  · exact g32p_row23_cosetBranchStep_1292 s
  · exact g32p_row23_cosetBranchStep_1293 s
  · exact g32p_row23_cosetBranchStep_1294 s
  · exact g32p_row23_cosetBranchStep_1295 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1296 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1296) = g32p_row23_cosetRepresentatives 1296 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1296) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1296))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1296)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1296) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1296))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1296)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1297 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1297) = g32p_row23_cosetRepresentatives 1297 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1297) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1297))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1297)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1297) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1297))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1297)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1298 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1298) = g32p_row23_cosetRepresentatives 1298 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1298) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1298))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1298)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1298) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1298))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1298)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1299 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1299) = g32p_row23_cosetRepresentatives 1299 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1299) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1299))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1299)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1299) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1299))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1299)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1300 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1300) = g32p_row23_cosetRepresentatives 1300 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1300) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1300))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1300)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1300) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1300))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1300)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1301 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1301) = g32p_row23_cosetRepresentatives 1301 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1301) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1301))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1301)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1301) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1301))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1301)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1302 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1302) = g32p_row23_cosetRepresentatives 1302 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1302) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1302))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1302)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1302) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1302))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1302)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1303 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1303) = g32p_row23_cosetRepresentatives 1303 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1303) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1303))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1303)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1303) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1303))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1303)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1304 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1304) = g32p_row23_cosetRepresentatives 1304 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1304) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1304))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1304)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1304) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1304))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1304)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1305 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1305) = g32p_row23_cosetRepresentatives 1305 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1305) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1305))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1305)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1305) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1305))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1305)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1306 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1306) = g32p_row23_cosetRepresentatives 1306 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1306) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1306))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1306)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1306) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1306))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1306)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1307 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1307) = g32p_row23_cosetRepresentatives 1307 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1307) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1307))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1307)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1307) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1307))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1307)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1308 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1308) = g32p_row23_cosetRepresentatives 1308 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1308) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1308))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1308)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1308) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1308))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1308)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1309 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1309) = g32p_row23_cosetRepresentatives 1309 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1309) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1309))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1309)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1309) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1309))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1309)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1310 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1310) = g32p_row23_cosetRepresentatives 1310 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1310) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1310))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1310)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1310) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1310))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1310)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1311 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1311) = g32p_row23_cosetRepresentatives 1311 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1311) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1311))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1311)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1311) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1311))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1311)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0081 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 81 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 81 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1296
  · exact g32p_row23_cosetWord_1297
  · exact g32p_row23_cosetWord_1298
  · exact g32p_row23_cosetWord_1299
  · exact g32p_row23_cosetWord_1300
  · exact g32p_row23_cosetWord_1301
  · exact g32p_row23_cosetWord_1302
  · exact g32p_row23_cosetWord_1303
  · exact g32p_row23_cosetWord_1304
  · exact g32p_row23_cosetWord_1305
  · exact g32p_row23_cosetWord_1306
  · exact g32p_row23_cosetWord_1307
  · exact g32p_row23_cosetWord_1308
  · exact g32p_row23_cosetWord_1309
  · exact g32p_row23_cosetWord_1310
  · exact g32p_row23_cosetWord_1311

theorem g32p_row23_cosetGeneratorBlock_0081 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 81 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 81 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 81 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1296 s
  · exact g32p_row23_cosetGeneratorStep_1297 s
  · exact g32p_row23_cosetGeneratorStep_1298 s
  · exact g32p_row23_cosetGeneratorStep_1299 s
  · exact g32p_row23_cosetGeneratorStep_1300 s
  · exact g32p_row23_cosetGeneratorStep_1301 s
  · exact g32p_row23_cosetGeneratorStep_1302 s
  · exact g32p_row23_cosetGeneratorStep_1303 s
  · exact g32p_row23_cosetGeneratorStep_1304 s
  · exact g32p_row23_cosetGeneratorStep_1305 s
  · exact g32p_row23_cosetGeneratorStep_1306 s
  · exact g32p_row23_cosetGeneratorStep_1307 s
  · exact g32p_row23_cosetGeneratorStep_1308 s
  · exact g32p_row23_cosetGeneratorStep_1309 s
  · exact g32p_row23_cosetGeneratorStep_1310 s
  · exact g32p_row23_cosetGeneratorStep_1311 s

theorem g32p_row23_cosetBranchBlock_0081 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 81 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 81 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 81 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1296 s
  · exact g32p_row23_cosetBranchStep_1297 s
  · exact g32p_row23_cosetBranchStep_1298 s
  · exact g32p_row23_cosetBranchStep_1299 s
  · exact g32p_row23_cosetBranchStep_1300 s
  · exact g32p_row23_cosetBranchStep_1301 s
  · exact g32p_row23_cosetBranchStep_1302 s
  · exact g32p_row23_cosetBranchStep_1303 s
  · exact g32p_row23_cosetBranchStep_1304 s
  · exact g32p_row23_cosetBranchStep_1305 s
  · exact g32p_row23_cosetBranchStep_1306 s
  · exact g32p_row23_cosetBranchStep_1307 s
  · exact g32p_row23_cosetBranchStep_1308 s
  · exact g32p_row23_cosetBranchStep_1309 s
  · exact g32p_row23_cosetBranchStep_1310 s
  · exact g32p_row23_cosetBranchStep_1311 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1312 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1312) = g32p_row23_cosetRepresentatives 1312 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1312) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1312))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1312)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1312) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1312))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1312)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1313 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1313) = g32p_row23_cosetRepresentatives 1313 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1313) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1313))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1313)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1313) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1313))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1313)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1314 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1314) = g32p_row23_cosetRepresentatives 1314 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1314) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1314))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1314)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1314) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1314))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1314)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1315 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1315) = g32p_row23_cosetRepresentatives 1315 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1315) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1315))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1315)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1315) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1315))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1315)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1316 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1316) = g32p_row23_cosetRepresentatives 1316 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1316) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1316))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1316)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1316) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1316))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1316)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1317 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1317) = g32p_row23_cosetRepresentatives 1317 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1317) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1317))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1317)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1317) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1317))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1317)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1318 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1318) = g32p_row23_cosetRepresentatives 1318 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1318) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1318))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1318)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1318) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1318))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1318)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1319 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1319) = g32p_row23_cosetRepresentatives 1319 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1319) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1319))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1319)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1319) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1319))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1319)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1320 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1320) = g32p_row23_cosetRepresentatives 1320 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1320) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1320))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1320)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1320) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1320))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1320)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1321 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1321) = g32p_row23_cosetRepresentatives 1321 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1321) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1321))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1321)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1321) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1321))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1321)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1322 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1322) = g32p_row23_cosetRepresentatives 1322 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1322) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1322))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1322)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1322) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1322))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1322)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1323 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1323) = g32p_row23_cosetRepresentatives 1323 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1323) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1323))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1323)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1323) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1323))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1323)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1324 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1324) = g32p_row23_cosetRepresentatives 1324 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1324) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1324))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1324)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1324) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1324))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1324)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1325 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1325) = g32p_row23_cosetRepresentatives 1325 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1325) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1325))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1325)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1325) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1325))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1325)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1326 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1326) = g32p_row23_cosetRepresentatives 1326 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1326) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1326))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1326)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1326) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1326))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1326)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1327 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1327) = g32p_row23_cosetRepresentatives 1327 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1327) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1327))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1327)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1327) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1327))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1327)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0082 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 82 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 82 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1312
  · exact g32p_row23_cosetWord_1313
  · exact g32p_row23_cosetWord_1314
  · exact g32p_row23_cosetWord_1315
  · exact g32p_row23_cosetWord_1316
  · exact g32p_row23_cosetWord_1317
  · exact g32p_row23_cosetWord_1318
  · exact g32p_row23_cosetWord_1319
  · exact g32p_row23_cosetWord_1320
  · exact g32p_row23_cosetWord_1321
  · exact g32p_row23_cosetWord_1322
  · exact g32p_row23_cosetWord_1323
  · exact g32p_row23_cosetWord_1324
  · exact g32p_row23_cosetWord_1325
  · exact g32p_row23_cosetWord_1326
  · exact g32p_row23_cosetWord_1327

theorem g32p_row23_cosetGeneratorBlock_0082 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 82 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 82 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 82 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1312 s
  · exact g32p_row23_cosetGeneratorStep_1313 s
  · exact g32p_row23_cosetGeneratorStep_1314 s
  · exact g32p_row23_cosetGeneratorStep_1315 s
  · exact g32p_row23_cosetGeneratorStep_1316 s
  · exact g32p_row23_cosetGeneratorStep_1317 s
  · exact g32p_row23_cosetGeneratorStep_1318 s
  · exact g32p_row23_cosetGeneratorStep_1319 s
  · exact g32p_row23_cosetGeneratorStep_1320 s
  · exact g32p_row23_cosetGeneratorStep_1321 s
  · exact g32p_row23_cosetGeneratorStep_1322 s
  · exact g32p_row23_cosetGeneratorStep_1323 s
  · exact g32p_row23_cosetGeneratorStep_1324 s
  · exact g32p_row23_cosetGeneratorStep_1325 s
  · exact g32p_row23_cosetGeneratorStep_1326 s
  · exact g32p_row23_cosetGeneratorStep_1327 s

theorem g32p_row23_cosetBranchBlock_0082 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 82 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 82 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 82 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1312 s
  · exact g32p_row23_cosetBranchStep_1313 s
  · exact g32p_row23_cosetBranchStep_1314 s
  · exact g32p_row23_cosetBranchStep_1315 s
  · exact g32p_row23_cosetBranchStep_1316 s
  · exact g32p_row23_cosetBranchStep_1317 s
  · exact g32p_row23_cosetBranchStep_1318 s
  · exact g32p_row23_cosetBranchStep_1319 s
  · exact g32p_row23_cosetBranchStep_1320 s
  · exact g32p_row23_cosetBranchStep_1321 s
  · exact g32p_row23_cosetBranchStep_1322 s
  · exact g32p_row23_cosetBranchStep_1323 s
  · exact g32p_row23_cosetBranchStep_1324 s
  · exact g32p_row23_cosetBranchStep_1325 s
  · exact g32p_row23_cosetBranchStep_1326 s
  · exact g32p_row23_cosetBranchStep_1327 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1328 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1328) = g32p_row23_cosetRepresentatives 1328 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1328 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1328) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1328))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1328)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1328 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1328) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1328))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1328)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1329 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1329) = g32p_row23_cosetRepresentatives 1329 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1329 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1329) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1329))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1329)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1329 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1329) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1329))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1329)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1330 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1330) = g32p_row23_cosetRepresentatives 1330 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1330 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1330) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1330))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1330)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1330 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1330) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1330))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1330)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1331 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1331) = g32p_row23_cosetRepresentatives 1331 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1331 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1331) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1331))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1331)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1331 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1331) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1331))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1331)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1332 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1332) = g32p_row23_cosetRepresentatives 1332 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1332 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1332) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1332))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1332)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1332 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1332) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1332))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1332)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1333 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1333) = g32p_row23_cosetRepresentatives 1333 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1333 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1333) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1333))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1333)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1333 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1333) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1333))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1333)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1334 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1334) = g32p_row23_cosetRepresentatives 1334 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1334 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1334) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1334))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1334)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1334 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1334) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1334))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1334)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1335 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1335) = g32p_row23_cosetRepresentatives 1335 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1335 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1335) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1335))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1335)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1335 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1335) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1335))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1335)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1336 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1336) = g32p_row23_cosetRepresentatives 1336 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1336 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1336) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1336))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1336)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1336 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1336) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1336))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1336)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1337 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1337) = g32p_row23_cosetRepresentatives 1337 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1337 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1337) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1337))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1337)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1337 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1337) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1337))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1337)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1338 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1338) = g32p_row23_cosetRepresentatives 1338 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1338 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1338) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1338))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1338)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1338 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1338) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1338))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1338)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1339 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1339) = g32p_row23_cosetRepresentatives 1339 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1339 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1339) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1339))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1339)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1339 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1339) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1339))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1339)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1340 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1340) = g32p_row23_cosetRepresentatives 1340 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1340 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1340) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1340))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1340)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1340 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1340) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1340))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1340)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1341 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1341) = g32p_row23_cosetRepresentatives 1341 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1341 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1341) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1341))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1341)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1341 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1341) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1341))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1341)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1342 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1342) = g32p_row23_cosetRepresentatives 1342 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1342 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1342) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1342))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1342)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1342 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1342) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1342))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1342)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1343 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1343) = g32p_row23_cosetRepresentatives 1343 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1343 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1343) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1343))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1343)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1343 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1343) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1343))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1343)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0083 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 83 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 83 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1328
  · exact g32p_row23_cosetWord_1329
  · exact g32p_row23_cosetWord_1330
  · exact g32p_row23_cosetWord_1331
  · exact g32p_row23_cosetWord_1332
  · exact g32p_row23_cosetWord_1333
  · exact g32p_row23_cosetWord_1334
  · exact g32p_row23_cosetWord_1335
  · exact g32p_row23_cosetWord_1336
  · exact g32p_row23_cosetWord_1337
  · exact g32p_row23_cosetWord_1338
  · exact g32p_row23_cosetWord_1339
  · exact g32p_row23_cosetWord_1340
  · exact g32p_row23_cosetWord_1341
  · exact g32p_row23_cosetWord_1342
  · exact g32p_row23_cosetWord_1343

theorem g32p_row23_cosetGeneratorBlock_0083 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 83 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 83 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 83 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1328 s
  · exact g32p_row23_cosetGeneratorStep_1329 s
  · exact g32p_row23_cosetGeneratorStep_1330 s
  · exact g32p_row23_cosetGeneratorStep_1331 s
  · exact g32p_row23_cosetGeneratorStep_1332 s
  · exact g32p_row23_cosetGeneratorStep_1333 s
  · exact g32p_row23_cosetGeneratorStep_1334 s
  · exact g32p_row23_cosetGeneratorStep_1335 s
  · exact g32p_row23_cosetGeneratorStep_1336 s
  · exact g32p_row23_cosetGeneratorStep_1337 s
  · exact g32p_row23_cosetGeneratorStep_1338 s
  · exact g32p_row23_cosetGeneratorStep_1339 s
  · exact g32p_row23_cosetGeneratorStep_1340 s
  · exact g32p_row23_cosetGeneratorStep_1341 s
  · exact g32p_row23_cosetGeneratorStep_1342 s
  · exact g32p_row23_cosetGeneratorStep_1343 s

theorem g32p_row23_cosetBranchBlock_0083 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 83 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 83 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 83 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1328 s
  · exact g32p_row23_cosetBranchStep_1329 s
  · exact g32p_row23_cosetBranchStep_1330 s
  · exact g32p_row23_cosetBranchStep_1331 s
  · exact g32p_row23_cosetBranchStep_1332 s
  · exact g32p_row23_cosetBranchStep_1333 s
  · exact g32p_row23_cosetBranchStep_1334 s
  · exact g32p_row23_cosetBranchStep_1335 s
  · exact g32p_row23_cosetBranchStep_1336 s
  · exact g32p_row23_cosetBranchStep_1337 s
  · exact g32p_row23_cosetBranchStep_1338 s
  · exact g32p_row23_cosetBranchStep_1339 s
  · exact g32p_row23_cosetBranchStep_1340 s
  · exact g32p_row23_cosetBranchStep_1341 s
  · exact g32p_row23_cosetBranchStep_1342 s
  · exact g32p_row23_cosetBranchStep_1343 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1344 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1344) = g32p_row23_cosetRepresentatives 1344 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1344 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1344) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1344))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1344)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1344 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1344) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1344))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1344)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1345 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1345) = g32p_row23_cosetRepresentatives 1345 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1345 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1345) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1345))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1345)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1345 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1345) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1345))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1345)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1346 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1346) = g32p_row23_cosetRepresentatives 1346 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1346 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1346) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1346))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1346)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1346 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1346) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1346))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1346)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1347 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1347) = g32p_row23_cosetRepresentatives 1347 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1347 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1347) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1347))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1347)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1347 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1347) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1347))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1347)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1348 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1348) = g32p_row23_cosetRepresentatives 1348 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1348 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1348) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1348))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1348)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1348 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1348) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1348))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1348)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1349 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1349) = g32p_row23_cosetRepresentatives 1349 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1349 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1349) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1349))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1349)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1349 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1349) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1349))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1349)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1350 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1350) = g32p_row23_cosetRepresentatives 1350 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1350 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1350) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1350))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1350)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1350 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1350) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1350))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1350)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1351 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1351) = g32p_row23_cosetRepresentatives 1351 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1351 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1351) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1351))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1351)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1351 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1351) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1351))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1351)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1352 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1352) = g32p_row23_cosetRepresentatives 1352 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1352 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1352) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1352))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1352)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1352 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1352) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1352))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1352)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1353 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1353) = g32p_row23_cosetRepresentatives 1353 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1353 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1353) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1353))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1353)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1353 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1353) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1353))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1353)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1354 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1354) = g32p_row23_cosetRepresentatives 1354 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1354 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1354) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1354))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1354)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1354 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1354) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1354))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1354)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1355 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1355) = g32p_row23_cosetRepresentatives 1355 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1355 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1355) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1355))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1355)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1355 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1355) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1355))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1355)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1356 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1356) = g32p_row23_cosetRepresentatives 1356 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1356 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1356) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1356))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1356)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1356 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1356) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1356))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1356)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1357 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1357) = g32p_row23_cosetRepresentatives 1357 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1357 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1357) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1357))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1357)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1357 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1357) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1357))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1357)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1358 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1358) = g32p_row23_cosetRepresentatives 1358 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1358 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1358) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1358))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1358)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1358 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1358) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1358))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1358)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1359 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1359) = g32p_row23_cosetRepresentatives 1359 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1359 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1359) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1359))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1359)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1359 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1359) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1359))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1359)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0084 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 84 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 84 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1344
  · exact g32p_row23_cosetWord_1345
  · exact g32p_row23_cosetWord_1346
  · exact g32p_row23_cosetWord_1347
  · exact g32p_row23_cosetWord_1348
  · exact g32p_row23_cosetWord_1349
  · exact g32p_row23_cosetWord_1350
  · exact g32p_row23_cosetWord_1351
  · exact g32p_row23_cosetWord_1352
  · exact g32p_row23_cosetWord_1353
  · exact g32p_row23_cosetWord_1354
  · exact g32p_row23_cosetWord_1355
  · exact g32p_row23_cosetWord_1356
  · exact g32p_row23_cosetWord_1357
  · exact g32p_row23_cosetWord_1358
  · exact g32p_row23_cosetWord_1359

theorem g32p_row23_cosetGeneratorBlock_0084 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 84 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 84 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 84 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1344 s
  · exact g32p_row23_cosetGeneratorStep_1345 s
  · exact g32p_row23_cosetGeneratorStep_1346 s
  · exact g32p_row23_cosetGeneratorStep_1347 s
  · exact g32p_row23_cosetGeneratorStep_1348 s
  · exact g32p_row23_cosetGeneratorStep_1349 s
  · exact g32p_row23_cosetGeneratorStep_1350 s
  · exact g32p_row23_cosetGeneratorStep_1351 s
  · exact g32p_row23_cosetGeneratorStep_1352 s
  · exact g32p_row23_cosetGeneratorStep_1353 s
  · exact g32p_row23_cosetGeneratorStep_1354 s
  · exact g32p_row23_cosetGeneratorStep_1355 s
  · exact g32p_row23_cosetGeneratorStep_1356 s
  · exact g32p_row23_cosetGeneratorStep_1357 s
  · exact g32p_row23_cosetGeneratorStep_1358 s
  · exact g32p_row23_cosetGeneratorStep_1359 s

theorem g32p_row23_cosetBranchBlock_0084 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 84 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 84 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 84 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1344 s
  · exact g32p_row23_cosetBranchStep_1345 s
  · exact g32p_row23_cosetBranchStep_1346 s
  · exact g32p_row23_cosetBranchStep_1347 s
  · exact g32p_row23_cosetBranchStep_1348 s
  · exact g32p_row23_cosetBranchStep_1349 s
  · exact g32p_row23_cosetBranchStep_1350 s
  · exact g32p_row23_cosetBranchStep_1351 s
  · exact g32p_row23_cosetBranchStep_1352 s
  · exact g32p_row23_cosetBranchStep_1353 s
  · exact g32p_row23_cosetBranchStep_1354 s
  · exact g32p_row23_cosetBranchStep_1355 s
  · exact g32p_row23_cosetBranchStep_1356 s
  · exact g32p_row23_cosetBranchStep_1357 s
  · exact g32p_row23_cosetBranchStep_1358 s
  · exact g32p_row23_cosetBranchStep_1359 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1360 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1360) = g32p_row23_cosetRepresentatives 1360 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1360 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1360) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1360))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1360)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1360 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1360) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1360))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1360)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1361 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1361) = g32p_row23_cosetRepresentatives 1361 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1361 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1361) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1361))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1361)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1361 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1361) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1361))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1361)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1362 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1362) = g32p_row23_cosetRepresentatives 1362 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1362 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1362) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1362))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1362)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1362 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1362) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1362))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1362)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1363 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1363) = g32p_row23_cosetRepresentatives 1363 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1363 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1363) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1363))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1363)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1363 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1363) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1363))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1363)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1364 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1364) = g32p_row23_cosetRepresentatives 1364 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1364 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1364) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1364))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1364)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1364 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1364) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1364))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1364)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1365 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1365) = g32p_row23_cosetRepresentatives 1365 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1365 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1365) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1365))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1365)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1365 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1365) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1365))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1365)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1366 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1366) = g32p_row23_cosetRepresentatives 1366 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1366 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1366) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1366))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1366)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1366 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1366) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1366))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1366)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1367 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1367) = g32p_row23_cosetRepresentatives 1367 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1367 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1367) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1367))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1367)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1367 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1367) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1367))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1367)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1368 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1368) = g32p_row23_cosetRepresentatives 1368 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1368 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1368) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1368))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1368)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1368 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1368) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1368))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1368)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1369 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1369) = g32p_row23_cosetRepresentatives 1369 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1369 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1369) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1369))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1369)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1369 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1369) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1369))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1369)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1370 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1370) = g32p_row23_cosetRepresentatives 1370 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1370 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1370) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1370))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1370)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1370 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1370) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1370))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1370)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1371 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1371) = g32p_row23_cosetRepresentatives 1371 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1371 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1371) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1371))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1371)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1371 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1371) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1371))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1371)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1372 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1372) = g32p_row23_cosetRepresentatives 1372 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1372 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1372) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1372))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1372)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1372 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1372) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1372))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1372)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1373 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1373) = g32p_row23_cosetRepresentatives 1373 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1373 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1373) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1373))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1373)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1373 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1373) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1373))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1373)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1374 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1374) = g32p_row23_cosetRepresentatives 1374 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1374 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1374) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1374))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1374)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1374 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1374) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1374))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1374)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1375 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1375) = g32p_row23_cosetRepresentatives 1375 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1375 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1375) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1375))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1375)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1375 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1375) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1375))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1375)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0085 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 85 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 85 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1360
  · exact g32p_row23_cosetWord_1361
  · exact g32p_row23_cosetWord_1362
  · exact g32p_row23_cosetWord_1363
  · exact g32p_row23_cosetWord_1364
  · exact g32p_row23_cosetWord_1365
  · exact g32p_row23_cosetWord_1366
  · exact g32p_row23_cosetWord_1367
  · exact g32p_row23_cosetWord_1368
  · exact g32p_row23_cosetWord_1369
  · exact g32p_row23_cosetWord_1370
  · exact g32p_row23_cosetWord_1371
  · exact g32p_row23_cosetWord_1372
  · exact g32p_row23_cosetWord_1373
  · exact g32p_row23_cosetWord_1374
  · exact g32p_row23_cosetWord_1375

theorem g32p_row23_cosetGeneratorBlock_0085 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 85 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 85 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 85 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1360 s
  · exact g32p_row23_cosetGeneratorStep_1361 s
  · exact g32p_row23_cosetGeneratorStep_1362 s
  · exact g32p_row23_cosetGeneratorStep_1363 s
  · exact g32p_row23_cosetGeneratorStep_1364 s
  · exact g32p_row23_cosetGeneratorStep_1365 s
  · exact g32p_row23_cosetGeneratorStep_1366 s
  · exact g32p_row23_cosetGeneratorStep_1367 s
  · exact g32p_row23_cosetGeneratorStep_1368 s
  · exact g32p_row23_cosetGeneratorStep_1369 s
  · exact g32p_row23_cosetGeneratorStep_1370 s
  · exact g32p_row23_cosetGeneratorStep_1371 s
  · exact g32p_row23_cosetGeneratorStep_1372 s
  · exact g32p_row23_cosetGeneratorStep_1373 s
  · exact g32p_row23_cosetGeneratorStep_1374 s
  · exact g32p_row23_cosetGeneratorStep_1375 s

theorem g32p_row23_cosetBranchBlock_0085 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 85 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 85 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 85 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1360 s
  · exact g32p_row23_cosetBranchStep_1361 s
  · exact g32p_row23_cosetBranchStep_1362 s
  · exact g32p_row23_cosetBranchStep_1363 s
  · exact g32p_row23_cosetBranchStep_1364 s
  · exact g32p_row23_cosetBranchStep_1365 s
  · exact g32p_row23_cosetBranchStep_1366 s
  · exact g32p_row23_cosetBranchStep_1367 s
  · exact g32p_row23_cosetBranchStep_1368 s
  · exact g32p_row23_cosetBranchStep_1369 s
  · exact g32p_row23_cosetBranchStep_1370 s
  · exact g32p_row23_cosetBranchStep_1371 s
  · exact g32p_row23_cosetBranchStep_1372 s
  · exact g32p_row23_cosetBranchStep_1373 s
  · exact g32p_row23_cosetBranchStep_1374 s
  · exact g32p_row23_cosetBranchStep_1375 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1376 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1376) = g32p_row23_cosetRepresentatives 1376 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1376 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1376) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1376))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1376)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1376 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1376) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1376))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1376)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1377 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1377) = g32p_row23_cosetRepresentatives 1377 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1377 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1377) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1377))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1377)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1377 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1377) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1377))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1377)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1378 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1378) = g32p_row23_cosetRepresentatives 1378 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1378 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1378) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1378))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1378)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1378 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1378) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1378))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1378)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1379 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1379) = g32p_row23_cosetRepresentatives 1379 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1379 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1379) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1379))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1379)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1379 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1379) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1379))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1379)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1380 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1380) = g32p_row23_cosetRepresentatives 1380 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1380 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1380) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1380))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1380)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1380 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1380) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1380))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1380)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1381 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1381) = g32p_row23_cosetRepresentatives 1381 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1381 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1381) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1381))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1381)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1381 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1381) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1381))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1381)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1382 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1382) = g32p_row23_cosetRepresentatives 1382 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1382 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1382) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1382))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1382)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1382 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1382) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1382))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1382)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1383 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1383) = g32p_row23_cosetRepresentatives 1383 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1383 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1383) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1383))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1383)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1383 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1383) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1383))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1383)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1384 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1384) = g32p_row23_cosetRepresentatives 1384 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1384 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1384) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1384))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1384)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1384 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1384) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1384))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1384)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1385 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1385) = g32p_row23_cosetRepresentatives 1385 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1385 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1385) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1385))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1385)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1385 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1385) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1385))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1385)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1386 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1386) = g32p_row23_cosetRepresentatives 1386 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1386 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1386) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1386))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1386)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1386 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1386) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1386))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1386)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1387 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1387) = g32p_row23_cosetRepresentatives 1387 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1387 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1387) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1387))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1387)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1387 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1387) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1387))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1387)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1388 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1388) = g32p_row23_cosetRepresentatives 1388 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1388 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1388) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1388))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1388)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1388 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1388) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1388))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1388)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1389 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1389) = g32p_row23_cosetRepresentatives 1389 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1389 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1389) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1389))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1389)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1389 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1389) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1389))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1389)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1390 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1390) = g32p_row23_cosetRepresentatives 1390 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1390 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1390) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1390))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1390)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1390 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1390) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1390))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1390)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1391 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1391) = g32p_row23_cosetRepresentatives 1391 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1391 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1391) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1391))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1391)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1391 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1391) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1391))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1391)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0086 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 86 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 86 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1376
  · exact g32p_row23_cosetWord_1377
  · exact g32p_row23_cosetWord_1378
  · exact g32p_row23_cosetWord_1379
  · exact g32p_row23_cosetWord_1380
  · exact g32p_row23_cosetWord_1381
  · exact g32p_row23_cosetWord_1382
  · exact g32p_row23_cosetWord_1383
  · exact g32p_row23_cosetWord_1384
  · exact g32p_row23_cosetWord_1385
  · exact g32p_row23_cosetWord_1386
  · exact g32p_row23_cosetWord_1387
  · exact g32p_row23_cosetWord_1388
  · exact g32p_row23_cosetWord_1389
  · exact g32p_row23_cosetWord_1390
  · exact g32p_row23_cosetWord_1391

theorem g32p_row23_cosetGeneratorBlock_0086 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 86 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 86 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 86 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1376 s
  · exact g32p_row23_cosetGeneratorStep_1377 s
  · exact g32p_row23_cosetGeneratorStep_1378 s
  · exact g32p_row23_cosetGeneratorStep_1379 s
  · exact g32p_row23_cosetGeneratorStep_1380 s
  · exact g32p_row23_cosetGeneratorStep_1381 s
  · exact g32p_row23_cosetGeneratorStep_1382 s
  · exact g32p_row23_cosetGeneratorStep_1383 s
  · exact g32p_row23_cosetGeneratorStep_1384 s
  · exact g32p_row23_cosetGeneratorStep_1385 s
  · exact g32p_row23_cosetGeneratorStep_1386 s
  · exact g32p_row23_cosetGeneratorStep_1387 s
  · exact g32p_row23_cosetGeneratorStep_1388 s
  · exact g32p_row23_cosetGeneratorStep_1389 s
  · exact g32p_row23_cosetGeneratorStep_1390 s
  · exact g32p_row23_cosetGeneratorStep_1391 s

theorem g32p_row23_cosetBranchBlock_0086 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 86 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 86 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 86 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1376 s
  · exact g32p_row23_cosetBranchStep_1377 s
  · exact g32p_row23_cosetBranchStep_1378 s
  · exact g32p_row23_cosetBranchStep_1379 s
  · exact g32p_row23_cosetBranchStep_1380 s
  · exact g32p_row23_cosetBranchStep_1381 s
  · exact g32p_row23_cosetBranchStep_1382 s
  · exact g32p_row23_cosetBranchStep_1383 s
  · exact g32p_row23_cosetBranchStep_1384 s
  · exact g32p_row23_cosetBranchStep_1385 s
  · exact g32p_row23_cosetBranchStep_1386 s
  · exact g32p_row23_cosetBranchStep_1387 s
  · exact g32p_row23_cosetBranchStep_1388 s
  · exact g32p_row23_cosetBranchStep_1389 s
  · exact g32p_row23_cosetBranchStep_1390 s
  · exact g32p_row23_cosetBranchStep_1391 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1392 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1392) = g32p_row23_cosetRepresentatives 1392 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1392 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1392) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1392))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1392)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1392 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1392) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1392))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1392)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1393 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1393) = g32p_row23_cosetRepresentatives 1393 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1393 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1393) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1393))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1393)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1393 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1393) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1393))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1393)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1394 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1394) = g32p_row23_cosetRepresentatives 1394 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1394 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1394) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1394))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1394)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1394 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1394) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1394))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1394)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1395 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1395) = g32p_row23_cosetRepresentatives 1395 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1395 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1395) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1395))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1395)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1395 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1395) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1395))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1395)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1396 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1396) = g32p_row23_cosetRepresentatives 1396 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1396 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1396) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1396))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1396)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1396 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1396) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1396))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1396)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1397 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1397) = g32p_row23_cosetRepresentatives 1397 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1397 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1397) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1397))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1397)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1397 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1397) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1397))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1397)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1398 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1398) = g32p_row23_cosetRepresentatives 1398 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1398 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1398) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1398))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1398)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1398 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1398) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1398))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1398)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1399 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1399) = g32p_row23_cosetRepresentatives 1399 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1399 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1399) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1399))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1399)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1399 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1399) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1399))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1399)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1400 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1400) = g32p_row23_cosetRepresentatives 1400 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1400 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1400) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1400))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1400)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1400 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1400) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1400))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1400)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1401 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1401) = g32p_row23_cosetRepresentatives 1401 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1401 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1401) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1401))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1401)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1401 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1401) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1401))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1401)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1402 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1402) = g32p_row23_cosetRepresentatives 1402 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1402 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1402) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1402))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1402)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1402 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1402) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1402))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1402)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1403 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1403) = g32p_row23_cosetRepresentatives 1403 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1403 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1403) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1403))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1403)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1403 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1403) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1403))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1403)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1404 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1404) = g32p_row23_cosetRepresentatives 1404 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1404 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1404) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1404))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1404)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1404 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1404) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1404))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1404)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1405 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1405) = g32p_row23_cosetRepresentatives 1405 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1405 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1405) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1405))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1405)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1405 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1405) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1405))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1405)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1406 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1406) = g32p_row23_cosetRepresentatives 1406 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1406 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1406) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1406))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1406)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1406 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1406) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1406))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1406)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1407 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1407) = g32p_row23_cosetRepresentatives 1407 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1407 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1407) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1407))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1407)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1407 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1407) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1407))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1407)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0087 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 87 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 87 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1392
  · exact g32p_row23_cosetWord_1393
  · exact g32p_row23_cosetWord_1394
  · exact g32p_row23_cosetWord_1395
  · exact g32p_row23_cosetWord_1396
  · exact g32p_row23_cosetWord_1397
  · exact g32p_row23_cosetWord_1398
  · exact g32p_row23_cosetWord_1399
  · exact g32p_row23_cosetWord_1400
  · exact g32p_row23_cosetWord_1401
  · exact g32p_row23_cosetWord_1402
  · exact g32p_row23_cosetWord_1403
  · exact g32p_row23_cosetWord_1404
  · exact g32p_row23_cosetWord_1405
  · exact g32p_row23_cosetWord_1406
  · exact g32p_row23_cosetWord_1407

theorem g32p_row23_cosetGeneratorBlock_0087 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 87 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 87 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 87 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1392 s
  · exact g32p_row23_cosetGeneratorStep_1393 s
  · exact g32p_row23_cosetGeneratorStep_1394 s
  · exact g32p_row23_cosetGeneratorStep_1395 s
  · exact g32p_row23_cosetGeneratorStep_1396 s
  · exact g32p_row23_cosetGeneratorStep_1397 s
  · exact g32p_row23_cosetGeneratorStep_1398 s
  · exact g32p_row23_cosetGeneratorStep_1399 s
  · exact g32p_row23_cosetGeneratorStep_1400 s
  · exact g32p_row23_cosetGeneratorStep_1401 s
  · exact g32p_row23_cosetGeneratorStep_1402 s
  · exact g32p_row23_cosetGeneratorStep_1403 s
  · exact g32p_row23_cosetGeneratorStep_1404 s
  · exact g32p_row23_cosetGeneratorStep_1405 s
  · exact g32p_row23_cosetGeneratorStep_1406 s
  · exact g32p_row23_cosetGeneratorStep_1407 s

theorem g32p_row23_cosetBranchBlock_0087 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 87 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 87 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 87 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1392 s
  · exact g32p_row23_cosetBranchStep_1393 s
  · exact g32p_row23_cosetBranchStep_1394 s
  · exact g32p_row23_cosetBranchStep_1395 s
  · exact g32p_row23_cosetBranchStep_1396 s
  · exact g32p_row23_cosetBranchStep_1397 s
  · exact g32p_row23_cosetBranchStep_1398 s
  · exact g32p_row23_cosetBranchStep_1399 s
  · exact g32p_row23_cosetBranchStep_1400 s
  · exact g32p_row23_cosetBranchStep_1401 s
  · exact g32p_row23_cosetBranchStep_1402 s
  · exact g32p_row23_cosetBranchStep_1403 s
  · exact g32p_row23_cosetBranchStep_1404 s
  · exact g32p_row23_cosetBranchStep_1405 s
  · exact g32p_row23_cosetBranchStep_1406 s
  · exact g32p_row23_cosetBranchStep_1407 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1408 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1408) = g32p_row23_cosetRepresentatives 1408 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1408 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1408) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1408))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1408)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1408 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1408) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1408))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1408)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1409 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1409) = g32p_row23_cosetRepresentatives 1409 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1409 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1409) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1409))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1409)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1409 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1409) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1409))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1409)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1410 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1410) = g32p_row23_cosetRepresentatives 1410 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1410 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1410) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1410))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1410)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1410 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1410) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1410))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1410)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1411 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1411) = g32p_row23_cosetRepresentatives 1411 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1411 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1411) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1411))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1411)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1411 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1411) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1411))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1411)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1412 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1412) = g32p_row23_cosetRepresentatives 1412 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1412 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1412) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1412))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1412)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1412 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1412) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1412))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1412)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1413 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1413) = g32p_row23_cosetRepresentatives 1413 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1413 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1413) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1413))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1413)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1413 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1413) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1413))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1413)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1414 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1414) = g32p_row23_cosetRepresentatives 1414 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1414 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1414) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1414))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1414)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1414 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1414) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1414))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1414)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1415 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1415) = g32p_row23_cosetRepresentatives 1415 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1415 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1415) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1415))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1415)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1415 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1415) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1415))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1415)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1416 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1416) = g32p_row23_cosetRepresentatives 1416 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1416 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1416) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1416))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1416)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1416 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1416) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1416))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1416)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1417 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1417) = g32p_row23_cosetRepresentatives 1417 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1417 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1417) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1417))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1417)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1417 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1417) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1417))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1417)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1418 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1418) = g32p_row23_cosetRepresentatives 1418 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1418 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1418) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1418))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1418)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1418 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1418) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1418))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1418)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1419 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1419) = g32p_row23_cosetRepresentatives 1419 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1419 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1419) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1419))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1419)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1419 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1419) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1419))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1419)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1420 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1420) = g32p_row23_cosetRepresentatives 1420 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1420 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1420) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1420))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1420)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1420 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1420) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1420))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1420)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1421 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1421) = g32p_row23_cosetRepresentatives 1421 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1421 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1421) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1421))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1421)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1421 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1421) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1421))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1421)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1422 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1422) = g32p_row23_cosetRepresentatives 1422 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1422 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1422) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1422))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1422)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1422 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1422) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1422))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1422)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1423 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1423) = g32p_row23_cosetRepresentatives 1423 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1423 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1423) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1423))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1423)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1423 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1423) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1423))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1423)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0088 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 88 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 88 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1408
  · exact g32p_row23_cosetWord_1409
  · exact g32p_row23_cosetWord_1410
  · exact g32p_row23_cosetWord_1411
  · exact g32p_row23_cosetWord_1412
  · exact g32p_row23_cosetWord_1413
  · exact g32p_row23_cosetWord_1414
  · exact g32p_row23_cosetWord_1415
  · exact g32p_row23_cosetWord_1416
  · exact g32p_row23_cosetWord_1417
  · exact g32p_row23_cosetWord_1418
  · exact g32p_row23_cosetWord_1419
  · exact g32p_row23_cosetWord_1420
  · exact g32p_row23_cosetWord_1421
  · exact g32p_row23_cosetWord_1422
  · exact g32p_row23_cosetWord_1423

theorem g32p_row23_cosetGeneratorBlock_0088 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 88 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 88 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 88 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1408 s
  · exact g32p_row23_cosetGeneratorStep_1409 s
  · exact g32p_row23_cosetGeneratorStep_1410 s
  · exact g32p_row23_cosetGeneratorStep_1411 s
  · exact g32p_row23_cosetGeneratorStep_1412 s
  · exact g32p_row23_cosetGeneratorStep_1413 s
  · exact g32p_row23_cosetGeneratorStep_1414 s
  · exact g32p_row23_cosetGeneratorStep_1415 s
  · exact g32p_row23_cosetGeneratorStep_1416 s
  · exact g32p_row23_cosetGeneratorStep_1417 s
  · exact g32p_row23_cosetGeneratorStep_1418 s
  · exact g32p_row23_cosetGeneratorStep_1419 s
  · exact g32p_row23_cosetGeneratorStep_1420 s
  · exact g32p_row23_cosetGeneratorStep_1421 s
  · exact g32p_row23_cosetGeneratorStep_1422 s
  · exact g32p_row23_cosetGeneratorStep_1423 s

theorem g32p_row23_cosetBranchBlock_0088 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 88 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 88 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 88 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1408 s
  · exact g32p_row23_cosetBranchStep_1409 s
  · exact g32p_row23_cosetBranchStep_1410 s
  · exact g32p_row23_cosetBranchStep_1411 s
  · exact g32p_row23_cosetBranchStep_1412 s
  · exact g32p_row23_cosetBranchStep_1413 s
  · exact g32p_row23_cosetBranchStep_1414 s
  · exact g32p_row23_cosetBranchStep_1415 s
  · exact g32p_row23_cosetBranchStep_1416 s
  · exact g32p_row23_cosetBranchStep_1417 s
  · exact g32p_row23_cosetBranchStep_1418 s
  · exact g32p_row23_cosetBranchStep_1419 s
  · exact g32p_row23_cosetBranchStep_1420 s
  · exact g32p_row23_cosetBranchStep_1421 s
  · exact g32p_row23_cosetBranchStep_1422 s
  · exact g32p_row23_cosetBranchStep_1423 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1424 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1424) = g32p_row23_cosetRepresentatives 1424 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1424 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1424) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1424))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1424)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1424 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1424) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1424))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1424)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1425 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1425) = g32p_row23_cosetRepresentatives 1425 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1425 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1425) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1425))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1425)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1425 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1425) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1425))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1425)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1426 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1426) = g32p_row23_cosetRepresentatives 1426 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1426 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1426) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1426))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1426)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1426 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1426) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1426))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1426)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1427 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1427) = g32p_row23_cosetRepresentatives 1427 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1427 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1427) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1427))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1427)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1427 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1427) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1427))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1427)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1428 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1428) = g32p_row23_cosetRepresentatives 1428 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1428 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1428) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1428))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1428)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1428 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1428) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1428))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1428)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1429 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1429) = g32p_row23_cosetRepresentatives 1429 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1429 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1429) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1429))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1429)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1429 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1429) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1429))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1429)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1430 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1430) = g32p_row23_cosetRepresentatives 1430 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1430 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1430) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1430))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1430)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1430 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1430) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1430))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1430)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1431 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1431) = g32p_row23_cosetRepresentatives 1431 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1431 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1431) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1431))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1431)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1431 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1431) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1431))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1431)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1432 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1432) = g32p_row23_cosetRepresentatives 1432 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1432 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1432) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1432))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1432)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1432 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1432) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1432))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1432)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1433 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1433) = g32p_row23_cosetRepresentatives 1433 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1433 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1433) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1433))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1433)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1433 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1433) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1433))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1433)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1434 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1434) = g32p_row23_cosetRepresentatives 1434 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1434 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1434) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1434))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1434)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1434 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1434) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1434))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1434)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1435 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1435) = g32p_row23_cosetRepresentatives 1435 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1435 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1435) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1435))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1435)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1435 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1435) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1435))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1435)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1436 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1436) = g32p_row23_cosetRepresentatives 1436 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1436 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1436) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1436))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1436)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1436 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1436) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1436))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1436)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1437 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1437) = g32p_row23_cosetRepresentatives 1437 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1437 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1437) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1437))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1437)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1437 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1437) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1437))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1437)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1438 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1438) = g32p_row23_cosetRepresentatives 1438 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1438 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1438) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1438))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1438)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1438 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1438) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1438))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1438)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1439 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1439) = g32p_row23_cosetRepresentatives 1439 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1439 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1439) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1439))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1439)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1439 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1439) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1439))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1439)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0089 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 89 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 89 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1424
  · exact g32p_row23_cosetWord_1425
  · exact g32p_row23_cosetWord_1426
  · exact g32p_row23_cosetWord_1427
  · exact g32p_row23_cosetWord_1428
  · exact g32p_row23_cosetWord_1429
  · exact g32p_row23_cosetWord_1430
  · exact g32p_row23_cosetWord_1431
  · exact g32p_row23_cosetWord_1432
  · exact g32p_row23_cosetWord_1433
  · exact g32p_row23_cosetWord_1434
  · exact g32p_row23_cosetWord_1435
  · exact g32p_row23_cosetWord_1436
  · exact g32p_row23_cosetWord_1437
  · exact g32p_row23_cosetWord_1438
  · exact g32p_row23_cosetWord_1439

theorem g32p_row23_cosetGeneratorBlock_0089 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 89 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 89 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 89 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1424 s
  · exact g32p_row23_cosetGeneratorStep_1425 s
  · exact g32p_row23_cosetGeneratorStep_1426 s
  · exact g32p_row23_cosetGeneratorStep_1427 s
  · exact g32p_row23_cosetGeneratorStep_1428 s
  · exact g32p_row23_cosetGeneratorStep_1429 s
  · exact g32p_row23_cosetGeneratorStep_1430 s
  · exact g32p_row23_cosetGeneratorStep_1431 s
  · exact g32p_row23_cosetGeneratorStep_1432 s
  · exact g32p_row23_cosetGeneratorStep_1433 s
  · exact g32p_row23_cosetGeneratorStep_1434 s
  · exact g32p_row23_cosetGeneratorStep_1435 s
  · exact g32p_row23_cosetGeneratorStep_1436 s
  · exact g32p_row23_cosetGeneratorStep_1437 s
  · exact g32p_row23_cosetGeneratorStep_1438 s
  · exact g32p_row23_cosetGeneratorStep_1439 s

theorem g32p_row23_cosetBranchBlock_0089 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 89 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 89 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 89 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1424 s
  · exact g32p_row23_cosetBranchStep_1425 s
  · exact g32p_row23_cosetBranchStep_1426 s
  · exact g32p_row23_cosetBranchStep_1427 s
  · exact g32p_row23_cosetBranchStep_1428 s
  · exact g32p_row23_cosetBranchStep_1429 s
  · exact g32p_row23_cosetBranchStep_1430 s
  · exact g32p_row23_cosetBranchStep_1431 s
  · exact g32p_row23_cosetBranchStep_1432 s
  · exact g32p_row23_cosetBranchStep_1433 s
  · exact g32p_row23_cosetBranchStep_1434 s
  · exact g32p_row23_cosetBranchStep_1435 s
  · exact g32p_row23_cosetBranchStep_1436 s
  · exact g32p_row23_cosetBranchStep_1437 s
  · exact g32p_row23_cosetBranchStep_1438 s
  · exact g32p_row23_cosetBranchStep_1439 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row23_cosetWord (i : Fin 1440) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords i) = g32p_row23_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row23_cosetWordBlock_0000
  · exact g32p_row23_cosetWordBlock_0001
  · exact g32p_row23_cosetWordBlock_0002
  · exact g32p_row23_cosetWordBlock_0003
  · exact g32p_row23_cosetWordBlock_0004
  · exact g32p_row23_cosetWordBlock_0005
  · exact g32p_row23_cosetWordBlock_0006
  · exact g32p_row23_cosetWordBlock_0007
  · exact g32p_row23_cosetWordBlock_0008
  · exact g32p_row23_cosetWordBlock_0009
  · exact g32p_row23_cosetWordBlock_0010
  · exact g32p_row23_cosetWordBlock_0011
  · exact g32p_row23_cosetWordBlock_0012
  · exact g32p_row23_cosetWordBlock_0013
  · exact g32p_row23_cosetWordBlock_0014
  · exact g32p_row23_cosetWordBlock_0015
  · exact g32p_row23_cosetWordBlock_0016
  · exact g32p_row23_cosetWordBlock_0017
  · exact g32p_row23_cosetWordBlock_0018
  · exact g32p_row23_cosetWordBlock_0019
  · exact g32p_row23_cosetWordBlock_0020
  · exact g32p_row23_cosetWordBlock_0021
  · exact g32p_row23_cosetWordBlock_0022
  · exact g32p_row23_cosetWordBlock_0023
  · exact g32p_row23_cosetWordBlock_0024
  · exact g32p_row23_cosetWordBlock_0025
  · exact g32p_row23_cosetWordBlock_0026
  · exact g32p_row23_cosetWordBlock_0027
  · exact g32p_row23_cosetWordBlock_0028
  · exact g32p_row23_cosetWordBlock_0029
  · exact g32p_row23_cosetWordBlock_0030
  · exact g32p_row23_cosetWordBlock_0031
  · exact g32p_row23_cosetWordBlock_0032
  · exact g32p_row23_cosetWordBlock_0033
  · exact g32p_row23_cosetWordBlock_0034
  · exact g32p_row23_cosetWordBlock_0035
  · exact g32p_row23_cosetWordBlock_0036
  · exact g32p_row23_cosetWordBlock_0037
  · exact g32p_row23_cosetWordBlock_0038
  · exact g32p_row23_cosetWordBlock_0039
  · exact g32p_row23_cosetWordBlock_0040
  · exact g32p_row23_cosetWordBlock_0041
  · exact g32p_row23_cosetWordBlock_0042
  · exact g32p_row23_cosetWordBlock_0043
  · exact g32p_row23_cosetWordBlock_0044
  · exact g32p_row23_cosetWordBlock_0045
  · exact g32p_row23_cosetWordBlock_0046
  · exact g32p_row23_cosetWordBlock_0047
  · exact g32p_row23_cosetWordBlock_0048
  · exact g32p_row23_cosetWordBlock_0049
  · exact g32p_row23_cosetWordBlock_0050
  · exact g32p_row23_cosetWordBlock_0051
  · exact g32p_row23_cosetWordBlock_0052
  · exact g32p_row23_cosetWordBlock_0053
  · exact g32p_row23_cosetWordBlock_0054
  · exact g32p_row23_cosetWordBlock_0055
  · exact g32p_row23_cosetWordBlock_0056
  · exact g32p_row23_cosetWordBlock_0057
  · exact g32p_row23_cosetWordBlock_0058
  · exact g32p_row23_cosetWordBlock_0059
  · exact g32p_row23_cosetWordBlock_0060
  · exact g32p_row23_cosetWordBlock_0061
  · exact g32p_row23_cosetWordBlock_0062
  · exact g32p_row23_cosetWordBlock_0063
  · exact g32p_row23_cosetWordBlock_0064
  · exact g32p_row23_cosetWordBlock_0065
  · exact g32p_row23_cosetWordBlock_0066
  · exact g32p_row23_cosetWordBlock_0067
  · exact g32p_row23_cosetWordBlock_0068
  · exact g32p_row23_cosetWordBlock_0069
  · exact g32p_row23_cosetWordBlock_0070
  · exact g32p_row23_cosetWordBlock_0071
  · exact g32p_row23_cosetWordBlock_0072
  · exact g32p_row23_cosetWordBlock_0073
  · exact g32p_row23_cosetWordBlock_0074
  · exact g32p_row23_cosetWordBlock_0075
  · exact g32p_row23_cosetWordBlock_0076
  · exact g32p_row23_cosetWordBlock_0077
  · exact g32p_row23_cosetWordBlock_0078
  · exact g32p_row23_cosetWordBlock_0079
  · exact g32p_row23_cosetWordBlock_0080
  · exact g32p_row23_cosetWordBlock_0081
  · exact g32p_row23_cosetWordBlock_0082
  · exact g32p_row23_cosetWordBlock_0083
  · exact g32p_row23_cosetWordBlock_0084
  · exact g32p_row23_cosetWordBlock_0085
  · exact g32p_row23_cosetWordBlock_0086
  · exact g32p_row23_cosetWordBlock_0087
  · exact g32p_row23_cosetWordBlock_0088
  · exact g32p_row23_cosetWordBlock_0089


def g32p_row23_cosetActualRepresentatives (i : Fin 1440) : g32p_G := g32p_archiveWord (g32p_row23_cosetWords i)

theorem g32p_row23_cosetActualRepresentatives_map (i : Fin 1440) :
    b4b_toMatrix (g32p_row23_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row23_cosetRepresentatives i)) := by
  rw [g32p_row23_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row23_cosetWord]

theorem g32p_row23_cosetGeneratorStep (s : Fin 4) (i : Fin 1440) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s i))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row23_cosetGeneratorBlock_0000 s
  · exact g32p_row23_cosetGeneratorBlock_0001 s
  · exact g32p_row23_cosetGeneratorBlock_0002 s
  · exact g32p_row23_cosetGeneratorBlock_0003 s
  · exact g32p_row23_cosetGeneratorBlock_0004 s
  · exact g32p_row23_cosetGeneratorBlock_0005 s
  · exact g32p_row23_cosetGeneratorBlock_0006 s
  · exact g32p_row23_cosetGeneratorBlock_0007 s
  · exact g32p_row23_cosetGeneratorBlock_0008 s
  · exact g32p_row23_cosetGeneratorBlock_0009 s
  · exact g32p_row23_cosetGeneratorBlock_0010 s
  · exact g32p_row23_cosetGeneratorBlock_0011 s
  · exact g32p_row23_cosetGeneratorBlock_0012 s
  · exact g32p_row23_cosetGeneratorBlock_0013 s
  · exact g32p_row23_cosetGeneratorBlock_0014 s
  · exact g32p_row23_cosetGeneratorBlock_0015 s
  · exact g32p_row23_cosetGeneratorBlock_0016 s
  · exact g32p_row23_cosetGeneratorBlock_0017 s
  · exact g32p_row23_cosetGeneratorBlock_0018 s
  · exact g32p_row23_cosetGeneratorBlock_0019 s
  · exact g32p_row23_cosetGeneratorBlock_0020 s
  · exact g32p_row23_cosetGeneratorBlock_0021 s
  · exact g32p_row23_cosetGeneratorBlock_0022 s
  · exact g32p_row23_cosetGeneratorBlock_0023 s
  · exact g32p_row23_cosetGeneratorBlock_0024 s
  · exact g32p_row23_cosetGeneratorBlock_0025 s
  · exact g32p_row23_cosetGeneratorBlock_0026 s
  · exact g32p_row23_cosetGeneratorBlock_0027 s
  · exact g32p_row23_cosetGeneratorBlock_0028 s
  · exact g32p_row23_cosetGeneratorBlock_0029 s
  · exact g32p_row23_cosetGeneratorBlock_0030 s
  · exact g32p_row23_cosetGeneratorBlock_0031 s
  · exact g32p_row23_cosetGeneratorBlock_0032 s
  · exact g32p_row23_cosetGeneratorBlock_0033 s
  · exact g32p_row23_cosetGeneratorBlock_0034 s
  · exact g32p_row23_cosetGeneratorBlock_0035 s
  · exact g32p_row23_cosetGeneratorBlock_0036 s
  · exact g32p_row23_cosetGeneratorBlock_0037 s
  · exact g32p_row23_cosetGeneratorBlock_0038 s
  · exact g32p_row23_cosetGeneratorBlock_0039 s
  · exact g32p_row23_cosetGeneratorBlock_0040 s
  · exact g32p_row23_cosetGeneratorBlock_0041 s
  · exact g32p_row23_cosetGeneratorBlock_0042 s
  · exact g32p_row23_cosetGeneratorBlock_0043 s
  · exact g32p_row23_cosetGeneratorBlock_0044 s
  · exact g32p_row23_cosetGeneratorBlock_0045 s
  · exact g32p_row23_cosetGeneratorBlock_0046 s
  · exact g32p_row23_cosetGeneratorBlock_0047 s
  · exact g32p_row23_cosetGeneratorBlock_0048 s
  · exact g32p_row23_cosetGeneratorBlock_0049 s
  · exact g32p_row23_cosetGeneratorBlock_0050 s
  · exact g32p_row23_cosetGeneratorBlock_0051 s
  · exact g32p_row23_cosetGeneratorBlock_0052 s
  · exact g32p_row23_cosetGeneratorBlock_0053 s
  · exact g32p_row23_cosetGeneratorBlock_0054 s
  · exact g32p_row23_cosetGeneratorBlock_0055 s
  · exact g32p_row23_cosetGeneratorBlock_0056 s
  · exact g32p_row23_cosetGeneratorBlock_0057 s
  · exact g32p_row23_cosetGeneratorBlock_0058 s
  · exact g32p_row23_cosetGeneratorBlock_0059 s
  · exact g32p_row23_cosetGeneratorBlock_0060 s
  · exact g32p_row23_cosetGeneratorBlock_0061 s
  · exact g32p_row23_cosetGeneratorBlock_0062 s
  · exact g32p_row23_cosetGeneratorBlock_0063 s
  · exact g32p_row23_cosetGeneratorBlock_0064 s
  · exact g32p_row23_cosetGeneratorBlock_0065 s
  · exact g32p_row23_cosetGeneratorBlock_0066 s
  · exact g32p_row23_cosetGeneratorBlock_0067 s
  · exact g32p_row23_cosetGeneratorBlock_0068 s
  · exact g32p_row23_cosetGeneratorBlock_0069 s
  · exact g32p_row23_cosetGeneratorBlock_0070 s
  · exact g32p_row23_cosetGeneratorBlock_0071 s
  · exact g32p_row23_cosetGeneratorBlock_0072 s
  · exact g32p_row23_cosetGeneratorBlock_0073 s
  · exact g32p_row23_cosetGeneratorBlock_0074 s
  · exact g32p_row23_cosetGeneratorBlock_0075 s
  · exact g32p_row23_cosetGeneratorBlock_0076 s
  · exact g32p_row23_cosetGeneratorBlock_0077 s
  · exact g32p_row23_cosetGeneratorBlock_0078 s
  · exact g32p_row23_cosetGeneratorBlock_0079 s
  · exact g32p_row23_cosetGeneratorBlock_0080 s
  · exact g32p_row23_cosetGeneratorBlock_0081 s
  · exact g32p_row23_cosetGeneratorBlock_0082 s
  · exact g32p_row23_cosetGeneratorBlock_0083 s
  · exact g32p_row23_cosetGeneratorBlock_0084 s
  · exact g32p_row23_cosetGeneratorBlock_0085 s
  · exact g32p_row23_cosetGeneratorBlock_0086 s
  · exact g32p_row23_cosetGeneratorBlock_0087 s
  · exact g32p_row23_cosetGeneratorBlock_0088 s
  · exact g32p_row23_cosetGeneratorBlock_0089 s


theorem g32p_row23_cosetActualStep (s : Fin 4) (i : Fin 1440) :
    g32p_word (g32p_archiveWords s) * g32p_row23_cosetActualRepresentatives i =
      g32p_row23_cosetActualRepresentatives (g32p_row23_cosetGeneratorNext s i) *
        (g32p_row23_groupEquiv (g32p_row23_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row23_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row23_cosetActualRepresentatives (g32p_row23_cosetGeneratorNext s i) *
      (g32p_row23_groupEquiv (g32p_row23_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row23_cosetActualRepresentatives_map,
    g32p_row23_cosetActualRepresentatives_map, g32p_row23_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row23_cosetGeneratorStep]

theorem g32p_row23_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row23_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row23_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row23_cosetGeneratorNext
      (fun s i => g32p_row23_groupEquiv (g32p_row23_cosetGeneratorFactor s i))
    exact g32p_row23_cosetActualStep
  · rw [g32p_row23_finiteSupplier_order]
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

theorem g32p_row23_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 0)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 0)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 0) = g32p_row23_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 1)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 1)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 1) = g32p_row23_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 2)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 2)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 2) = g32p_row23_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 3)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 3)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 3) = g32p_row23_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 4)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 4)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 4) = g32p_row23_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 5)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 5)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 5) = g32p_row23_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 6)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 6)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 6) = g32p_row23_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 7)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 7)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 7) = g32p_row23_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 8)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 8)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 8) = g32p_row23_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 9)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 9)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 9) = g32p_row23_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 10)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 10)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 10) = g32p_row23_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 11)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 11)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 11) = g32p_row23_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 12)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 12)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 12) = g32p_row23_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 13)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 13)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 13) = g32p_row23_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 14)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 14)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 14) = g32p_row23_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 15)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 15)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 15) = g32p_row23_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row23_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row23_cosetBranchMatrices 0) (g32p_row23_cosetLengths0 (g32p_finBlockIndex 528 0 r)))
      (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 0 r))) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 0 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 0 r))) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 0 r)) = g32p_row23_cosetExponents0 (g32p_finBlockIndex 528 0 r) := by
  fin_cases r
  · exact g32p_row23_cosetMonodromy_0_0000
  · exact g32p_row23_cosetMonodromy_0_0001
  · exact g32p_row23_cosetMonodromy_0_0002
  · exact g32p_row23_cosetMonodromy_0_0003
  · exact g32p_row23_cosetMonodromy_0_0004
  · exact g32p_row23_cosetMonodromy_0_0005
  · exact g32p_row23_cosetMonodromy_0_0006
  · exact g32p_row23_cosetMonodromy_0_0007
  · exact g32p_row23_cosetMonodromy_0_0008
  · exact g32p_row23_cosetMonodromy_0_0009
  · exact g32p_row23_cosetMonodromy_0_0010
  · exact g32p_row23_cosetMonodromy_0_0011
  · exact g32p_row23_cosetMonodromy_0_0012
  · exact g32p_row23_cosetMonodromy_0_0013
  · exact g32p_row23_cosetMonodromy_0_0014
  · exact g32p_row23_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 16)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 16)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 16) = g32p_row23_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 17)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 17)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 17) = g32p_row23_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 18)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 18)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 18) = g32p_row23_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 19)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 19)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 19) = g32p_row23_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 20)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 20)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 20) = g32p_row23_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row23_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 21)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 21)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 21) = g32p_row23_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 22)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 22)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 22) = g32p_row23_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 23)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 23)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 23) = g32p_row23_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 24)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 24)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 24) = g32p_row23_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 25)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 25)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 25) = g32p_row23_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 26)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 26)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 26) = g32p_row23_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 27)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 27)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 27) = g32p_row23_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 28)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 28)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 28) = g32p_row23_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 29) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 29)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 29)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 29) = g32p_row23_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 30)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 30)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 30) = g32p_row23_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 31)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 31)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 31) = g32p_row23_cosetExponents0 31 := by
  decide +kernel

theorem g32p_row23_cosetMonodromyBlock0_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row23_cosetBranchMatrices 0) (g32p_row23_cosetLengths0 (g32p_finBlockIndex 528 1 r)))
      (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 1 r))) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 1 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 1 r))) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 1 r)) = g32p_row23_cosetExponents0 (g32p_finBlockIndex 528 1 r) := by
  fin_cases r
  · exact g32p_row23_cosetMonodromy_0_0016
  · exact g32p_row23_cosetMonodromy_0_0017
  · exact g32p_row23_cosetMonodromy_0_0018
  · exact g32p_row23_cosetMonodromy_0_0019
  · exact g32p_row23_cosetMonodromy_0_0020
  · exact g32p_row23_cosetMonodromy_0_0021
  · exact g32p_row23_cosetMonodromy_0_0022
  · exact g32p_row23_cosetMonodromy_0_0023
  · exact g32p_row23_cosetMonodromy_0_0024
  · exact g32p_row23_cosetMonodromy_0_0025
  · exact g32p_row23_cosetMonodromy_0_0026
  · exact g32p_row23_cosetMonodromy_0_0027
  · exact g32p_row23_cosetMonodromy_0_0028
  · exact g32p_row23_cosetMonodromy_0_0029
  · exact g32p_row23_cosetMonodromy_0_0030
  · exact g32p_row23_cosetMonodromy_0_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetMonodromy_0_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 32)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 32)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 32) = g32p_row23_cosetExponents0 32 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 33)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 33)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 33) = g32p_row23_cosetExponents0 33 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 34)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 34)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 34) = g32p_row23_cosetExponents0 34 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 35)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 35)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 35) = g32p_row23_cosetExponents0 35 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 36)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 36)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 36) = g32p_row23_cosetExponents0 36 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 37)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 37)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 37) = g32p_row23_cosetExponents0 37 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 38)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 38)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 38) = g32p_row23_cosetExponents0 38 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 39)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 39)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 39) = g32p_row23_cosetExponents0 39 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 40)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 40)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 40) = g32p_row23_cosetExponents0 40 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 41)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 41)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 41) = g32p_row23_cosetExponents0 41 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 42)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 42)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 42) = g32p_row23_cosetExponents0 42 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 43)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 43)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 43) = g32p_row23_cosetExponents0 43 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 44)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 44)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 44) = g32p_row23_cosetExponents0 44 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 45)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 45)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 45) = g32p_row23_cosetExponents0 45 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 46)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 46)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 46) = g32p_row23_cosetExponents0 46 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 47)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 47)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 47) = g32p_row23_cosetExponents0 47 := by
  decide +kernel

theorem g32p_row23_cosetMonodromyBlock0_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row23_cosetBranchMatrices 0) (g32p_row23_cosetLengths0 (g32p_finBlockIndex 528 2 r)))
      (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 2 r))) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 2 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 2 r))) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 2 r)) = g32p_row23_cosetExponents0 (g32p_finBlockIndex 528 2 r) := by
  fin_cases r
  · exact g32p_row23_cosetMonodromy_0_0032
  · exact g32p_row23_cosetMonodromy_0_0033
  · exact g32p_row23_cosetMonodromy_0_0034
  · exact g32p_row23_cosetMonodromy_0_0035
  · exact g32p_row23_cosetMonodromy_0_0036
  · exact g32p_row23_cosetMonodromy_0_0037
  · exact g32p_row23_cosetMonodromy_0_0038
  · exact g32p_row23_cosetMonodromy_0_0039
  · exact g32p_row23_cosetMonodromy_0_0040
  · exact g32p_row23_cosetMonodromy_0_0041
  · exact g32p_row23_cosetMonodromy_0_0042
  · exact g32p_row23_cosetMonodromy_0_0043
  · exact g32p_row23_cosetMonodromy_0_0044
  · exact g32p_row23_cosetMonodromy_0_0045
  · exact g32p_row23_cosetMonodromy_0_0046
  · exact g32p_row23_cosetMonodromy_0_0047


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetMonodromy_0_0048 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 48)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 48)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 48) = g32p_row23_cosetExponents0 48 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0049 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 49)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 49)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 49) = g32p_row23_cosetExponents0 49 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0050 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row23_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 50)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 50)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 50) = g32p_row23_cosetExponents0 50 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0051 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 51)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 51)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 51) = g32p_row23_cosetExponents0 51 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0052 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 52)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 52)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 52) = g32p_row23_cosetExponents0 52 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0053 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 53)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 53)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 53) = g32p_row23_cosetExponents0 53 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0054 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 54)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 54)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 54) = g32p_row23_cosetExponents0 54 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0055 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 55)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 55)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 55) = g32p_row23_cosetExponents0 55 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0056 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 56)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 56)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 56) = g32p_row23_cosetExponents0 56 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0057 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 57) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 57)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 57)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 57) = g32p_row23_cosetExponents0 57 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0058 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 58)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 58)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 58) = g32p_row23_cosetExponents0 58 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0059 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row23_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 59)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 59)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 59) = g32p_row23_cosetExponents0 59 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0060 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 60) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 60)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 60)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 60) = g32p_row23_cosetExponents0 60 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0061 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 62)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 61)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 61) = g32p_row23_cosetExponents0 61 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0062 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row23_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 63)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 62)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 62) = g32p_row23_cosetExponents0 62 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0063 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row23_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 65)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 63)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 63) = g32p_row23_cosetExponents0 63 := by
  decide +kernel

theorem g32p_row23_cosetMonodromyBlock0_0003 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row23_cosetBranchMatrices 0) (g32p_row23_cosetLengths0 (g32p_finBlockIndex 528 3 r)))
      (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 3 r))) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 3 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 3 r))) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 3 r)) = g32p_row23_cosetExponents0 (g32p_finBlockIndex 528 3 r) := by
  fin_cases r
  · exact g32p_row23_cosetMonodromy_0_0048
  · exact g32p_row23_cosetMonodromy_0_0049
  · exact g32p_row23_cosetMonodromy_0_0050
  · exact g32p_row23_cosetMonodromy_0_0051
  · exact g32p_row23_cosetMonodromy_0_0052
  · exact g32p_row23_cosetMonodromy_0_0053
  · exact g32p_row23_cosetMonodromy_0_0054
  · exact g32p_row23_cosetMonodromy_0_0055
  · exact g32p_row23_cosetMonodromy_0_0056
  · exact g32p_row23_cosetMonodromy_0_0057
  · exact g32p_row23_cosetMonodromy_0_0058
  · exact g32p_row23_cosetMonodromy_0_0059
  · exact g32p_row23_cosetMonodromy_0_0060
  · exact g32p_row23_cosetMonodromy_0_0061
  · exact g32p_row23_cosetMonodromy_0_0062
  · exact g32p_row23_cosetMonodromy_0_0063


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetMonodromy_0_0064 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 66)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 64)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 64) = g32p_row23_cosetExponents0 64 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0065 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 67) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 67)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 65)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 65) = g32p_row23_cosetExponents0 65 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0066 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 68)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 66)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 66) = g32p_row23_cosetExponents0 66 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0067 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 69)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 67)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 67) = g32p_row23_cosetExponents0 67 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0068 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 70)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 68)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 68) = g32p_row23_cosetExponents0 68 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0069 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 71)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 69)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 69) = g32p_row23_cosetExponents0 69 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0070 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 72)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 70)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 70) = g32p_row23_cosetExponents0 70 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0071 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 73)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 71)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 71) = g32p_row23_cosetExponents0 71 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0072 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 74)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 72)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 72) = g32p_row23_cosetExponents0 72 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0073 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)) (g32p_row23_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 75)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 73)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 73) = g32p_row23_cosetExponents0 73 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0074 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 77)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 74)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 74) = g32p_row23_cosetExponents0 74 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0075 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 78) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 78)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 75)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 75) = g32p_row23_cosetExponents0 75 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0076 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 79)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 76)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 76) = g32p_row23_cosetExponents0 76 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0077 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 80) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 80)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 77)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 77) = g32p_row23_cosetExponents0 77 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0078 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 81) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 81)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 78)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 78) = g32p_row23_cosetExponents0 78 := by
  decide +kernel

theorem g32p_row23_cosetMonodromy_0_0079 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row23_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives 82)
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 79)) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 79) = g32p_row23_cosetExponents0 79 := by
  decide +kernel

theorem g32p_row23_cosetMonodromyBlock0_0004 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row23_cosetBranchMatrices 0) (g32p_row23_cosetLengths0 (g32p_finBlockIndex 528 4 r)))
      (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 4 r))) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetRoots0 (g32p_finBlockIndex 528 4 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 4 r))) ∧
    g32p_row23_characterValues (g32p_row23_cosetMonodromies0 (g32p_finBlockIndex 528 4 r)) = g32p_row23_cosetExponents0 (g32p_finBlockIndex 528 4 r) := by
  fin_cases r
  · exact g32p_row23_cosetMonodromy_0_0064
  · exact g32p_row23_cosetMonodromy_0_0065
  · exact g32p_row23_cosetMonodromy_0_0066
  · exact g32p_row23_cosetMonodromy_0_0067
  · exact g32p_row23_cosetMonodromy_0_0068
  · exact g32p_row23_cosetMonodromy_0_0069
  · exact g32p_row23_cosetMonodromy_0_0070
  · exact g32p_row23_cosetMonodromy_0_0071
  · exact g32p_row23_cosetMonodromy_0_0072
  · exact g32p_row23_cosetMonodromy_0_0073
  · exact g32p_row23_cosetMonodromy_0_0074
  · exact g32p_row23_cosetMonodromy_0_0075
  · exact g32p_row23_cosetMonodromy_0_0076
  · exact g32p_row23_cosetMonodromy_0_0077
  · exact g32p_row23_cosetMonodromy_0_0078
  · exact g32p_row23_cosetMonodromy_0_0079


end HodgeLean.Foundations.Program

end
