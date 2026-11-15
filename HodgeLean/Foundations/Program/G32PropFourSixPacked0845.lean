import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0835

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2304 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2304) = g32p_row31_cosetRepresentatives 2304 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2304) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2304))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2304)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2304) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2304))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2304)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2305 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2305) = g32p_row31_cosetRepresentatives 2305 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2305) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2305))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2305)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2305) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2305))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2305)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2306 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2306) = g32p_row31_cosetRepresentatives 2306 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2306) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2306))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2306)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2306) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2306))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2306)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2307 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2307) = g32p_row31_cosetRepresentatives 2307 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2307) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2307))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2307)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2307) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2307))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2307)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2308 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2308) = g32p_row31_cosetRepresentatives 2308 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2308) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2308))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2308)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2308) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2308))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2308)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2309 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2309) = g32p_row31_cosetRepresentatives 2309 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2309) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2309))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2309)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2309) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2309))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2309)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2310 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2310) = g32p_row31_cosetRepresentatives 2310 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2310) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2310))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2310)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2310) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2310))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2310)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2311 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2311) = g32p_row31_cosetRepresentatives 2311 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2311) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2311))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2311)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2311) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2311))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2311)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2312 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2312) = g32p_row31_cosetRepresentatives 2312 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2312) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2312))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2312)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2312) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2312))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2312)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2313 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2313) = g32p_row31_cosetRepresentatives 2313 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2313) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2313))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2313)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2313) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2313))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2313)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2314 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2314) = g32p_row31_cosetRepresentatives 2314 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2314) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2314))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2314)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2314) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2314))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2314)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2315 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2315) = g32p_row31_cosetRepresentatives 2315 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2315) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2315))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2315)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2315) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2315))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2315)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2316 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2316) = g32p_row31_cosetRepresentatives 2316 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2316) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2316))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2316)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2316) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2316))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2316)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2317 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2317) = g32p_row31_cosetRepresentatives 2317 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2317) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2317))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2317)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2317) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2317))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2317)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2318 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2318) = g32p_row31_cosetRepresentatives 2318 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2318) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2318))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2318)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2318) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2318))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2318)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2319 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2319) = g32p_row31_cosetRepresentatives 2319 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2319) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2319))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2319)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2319) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2319))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2319)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0144 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 144 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 144 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2304
  · exact g32p_row31_cosetWord_2305
  · exact g32p_row31_cosetWord_2306
  · exact g32p_row31_cosetWord_2307
  · exact g32p_row31_cosetWord_2308
  · exact g32p_row31_cosetWord_2309
  · exact g32p_row31_cosetWord_2310
  · exact g32p_row31_cosetWord_2311
  · exact g32p_row31_cosetWord_2312
  · exact g32p_row31_cosetWord_2313
  · exact g32p_row31_cosetWord_2314
  · exact g32p_row31_cosetWord_2315
  · exact g32p_row31_cosetWord_2316
  · exact g32p_row31_cosetWord_2317
  · exact g32p_row31_cosetWord_2318
  · exact g32p_row31_cosetWord_2319

theorem g32p_row31_cosetGeneratorBlock_0144 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 144 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 144 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 144 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2304 s
  · exact g32p_row31_cosetGeneratorStep_2305 s
  · exact g32p_row31_cosetGeneratorStep_2306 s
  · exact g32p_row31_cosetGeneratorStep_2307 s
  · exact g32p_row31_cosetGeneratorStep_2308 s
  · exact g32p_row31_cosetGeneratorStep_2309 s
  · exact g32p_row31_cosetGeneratorStep_2310 s
  · exact g32p_row31_cosetGeneratorStep_2311 s
  · exact g32p_row31_cosetGeneratorStep_2312 s
  · exact g32p_row31_cosetGeneratorStep_2313 s
  · exact g32p_row31_cosetGeneratorStep_2314 s
  · exact g32p_row31_cosetGeneratorStep_2315 s
  · exact g32p_row31_cosetGeneratorStep_2316 s
  · exact g32p_row31_cosetGeneratorStep_2317 s
  · exact g32p_row31_cosetGeneratorStep_2318 s
  · exact g32p_row31_cosetGeneratorStep_2319 s

theorem g32p_row31_cosetBranchBlock_0144 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 144 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 144 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 144 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2304 s
  · exact g32p_row31_cosetBranchStep_2305 s
  · exact g32p_row31_cosetBranchStep_2306 s
  · exact g32p_row31_cosetBranchStep_2307 s
  · exact g32p_row31_cosetBranchStep_2308 s
  · exact g32p_row31_cosetBranchStep_2309 s
  · exact g32p_row31_cosetBranchStep_2310 s
  · exact g32p_row31_cosetBranchStep_2311 s
  · exact g32p_row31_cosetBranchStep_2312 s
  · exact g32p_row31_cosetBranchStep_2313 s
  · exact g32p_row31_cosetBranchStep_2314 s
  · exact g32p_row31_cosetBranchStep_2315 s
  · exact g32p_row31_cosetBranchStep_2316 s
  · exact g32p_row31_cosetBranchStep_2317 s
  · exact g32p_row31_cosetBranchStep_2318 s
  · exact g32p_row31_cosetBranchStep_2319 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2320 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2320) = g32p_row31_cosetRepresentatives 2320 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2320) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2320))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2320)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2320) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2320))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2320)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2321 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2321) = g32p_row31_cosetRepresentatives 2321 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2321) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2321))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2321)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2321) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2321))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2321)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2322 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2322) = g32p_row31_cosetRepresentatives 2322 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2322) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2322))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2322)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2322) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2322))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2322)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2323 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2323) = g32p_row31_cosetRepresentatives 2323 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2323) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2323))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2323)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2323) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2323))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2323)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2324 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2324) = g32p_row31_cosetRepresentatives 2324 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2324) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2324))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2324)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2324) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2324))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2324)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2325 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2325) = g32p_row31_cosetRepresentatives 2325 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2325) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2325))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2325)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2325) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2325))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2325)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2326 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2326) = g32p_row31_cosetRepresentatives 2326 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2326) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2326))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2326)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2326) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2326))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2326)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2327 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2327) = g32p_row31_cosetRepresentatives 2327 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2327) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2327))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2327)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2327) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2327))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2327)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2328 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2328) = g32p_row31_cosetRepresentatives 2328 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2328 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2328) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2328))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2328)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2328 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2328) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2328))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2328)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2329 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2329) = g32p_row31_cosetRepresentatives 2329 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2329 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2329) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2329))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2329)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2329 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2329) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2329))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2329)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2330 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2330) = g32p_row31_cosetRepresentatives 2330 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2330 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2330) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2330))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2330)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2330 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2330) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2330))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2330)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2331 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2331) = g32p_row31_cosetRepresentatives 2331 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2331 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2331) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2331))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2331)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2331 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2331) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2331))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2331)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2332 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2332) = g32p_row31_cosetRepresentatives 2332 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2332 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2332) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2332))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2332)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2332 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2332) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2332))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2332)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2333 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2333) = g32p_row31_cosetRepresentatives 2333 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2333 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2333) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2333))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2333)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2333 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2333) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2333))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2333)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2334 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2334) = g32p_row31_cosetRepresentatives 2334 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2334 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2334) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2334))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2334)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2334 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2334) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2334))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2334)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2335 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2335) = g32p_row31_cosetRepresentatives 2335 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2335 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2335) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2335))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2335)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2335 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2335) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2335))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2335)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0145 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 145 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 145 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2320
  · exact g32p_row31_cosetWord_2321
  · exact g32p_row31_cosetWord_2322
  · exact g32p_row31_cosetWord_2323
  · exact g32p_row31_cosetWord_2324
  · exact g32p_row31_cosetWord_2325
  · exact g32p_row31_cosetWord_2326
  · exact g32p_row31_cosetWord_2327
  · exact g32p_row31_cosetWord_2328
  · exact g32p_row31_cosetWord_2329
  · exact g32p_row31_cosetWord_2330
  · exact g32p_row31_cosetWord_2331
  · exact g32p_row31_cosetWord_2332
  · exact g32p_row31_cosetWord_2333
  · exact g32p_row31_cosetWord_2334
  · exact g32p_row31_cosetWord_2335

theorem g32p_row31_cosetGeneratorBlock_0145 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 145 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 145 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 145 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2320 s
  · exact g32p_row31_cosetGeneratorStep_2321 s
  · exact g32p_row31_cosetGeneratorStep_2322 s
  · exact g32p_row31_cosetGeneratorStep_2323 s
  · exact g32p_row31_cosetGeneratorStep_2324 s
  · exact g32p_row31_cosetGeneratorStep_2325 s
  · exact g32p_row31_cosetGeneratorStep_2326 s
  · exact g32p_row31_cosetGeneratorStep_2327 s
  · exact g32p_row31_cosetGeneratorStep_2328 s
  · exact g32p_row31_cosetGeneratorStep_2329 s
  · exact g32p_row31_cosetGeneratorStep_2330 s
  · exact g32p_row31_cosetGeneratorStep_2331 s
  · exact g32p_row31_cosetGeneratorStep_2332 s
  · exact g32p_row31_cosetGeneratorStep_2333 s
  · exact g32p_row31_cosetGeneratorStep_2334 s
  · exact g32p_row31_cosetGeneratorStep_2335 s

theorem g32p_row31_cosetBranchBlock_0145 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 145 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 145 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 145 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2320 s
  · exact g32p_row31_cosetBranchStep_2321 s
  · exact g32p_row31_cosetBranchStep_2322 s
  · exact g32p_row31_cosetBranchStep_2323 s
  · exact g32p_row31_cosetBranchStep_2324 s
  · exact g32p_row31_cosetBranchStep_2325 s
  · exact g32p_row31_cosetBranchStep_2326 s
  · exact g32p_row31_cosetBranchStep_2327 s
  · exact g32p_row31_cosetBranchStep_2328 s
  · exact g32p_row31_cosetBranchStep_2329 s
  · exact g32p_row31_cosetBranchStep_2330 s
  · exact g32p_row31_cosetBranchStep_2331 s
  · exact g32p_row31_cosetBranchStep_2332 s
  · exact g32p_row31_cosetBranchStep_2333 s
  · exact g32p_row31_cosetBranchStep_2334 s
  · exact g32p_row31_cosetBranchStep_2335 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2336 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2336) = g32p_row31_cosetRepresentatives 2336 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2336 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2336) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2336))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2336)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2336 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2336) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2336))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2336)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2337 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2337) = g32p_row31_cosetRepresentatives 2337 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2337 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2337) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2337))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2337)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2337 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2337) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2337))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2337)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2338 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2338) = g32p_row31_cosetRepresentatives 2338 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2338 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2338) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2338))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2338)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2338 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2338) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2338))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2338)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2339 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2339) = g32p_row31_cosetRepresentatives 2339 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2339 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2339) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2339))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2339)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2339 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2339) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2339))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2339)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2340 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2340) = g32p_row31_cosetRepresentatives 2340 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2340 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2340) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2340))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2340)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2340 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2340) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2340))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2340)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2341 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2341) = g32p_row31_cosetRepresentatives 2341 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2341 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2341) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2341))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2341)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2341 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2341) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2341))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2341)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2342 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2342) = g32p_row31_cosetRepresentatives 2342 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2342 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2342) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2342))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2342)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2342 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2342) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2342))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2342)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2343 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2343) = g32p_row31_cosetRepresentatives 2343 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2343 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2343) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2343))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2343)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2343 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2343) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2343))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2343)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2344 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2344) = g32p_row31_cosetRepresentatives 2344 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2344 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2344) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2344))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2344)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2344 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2344) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2344))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2344)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2345 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2345) = g32p_row31_cosetRepresentatives 2345 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2345 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2345) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2345))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2345)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2345 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2345) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2345))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2345)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2346 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2346) = g32p_row31_cosetRepresentatives 2346 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2346 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2346) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2346))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2346)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2346 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2346) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2346))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2346)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2347 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2347) = g32p_row31_cosetRepresentatives 2347 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2347 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2347) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2347))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2347)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2347 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2347) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2347))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2347)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2348 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2348) = g32p_row31_cosetRepresentatives 2348 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2348 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2348) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2348))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2348)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2348 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2348) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2348))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2348)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2349 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2349) = g32p_row31_cosetRepresentatives 2349 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2349 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2349) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2349))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2349)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2349 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2349) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2349))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2349)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2350 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2350) = g32p_row31_cosetRepresentatives 2350 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2350 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2350) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2350))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2350)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2350 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2350) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2350))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2350)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2351 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2351) = g32p_row31_cosetRepresentatives 2351 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2351 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2351) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2351))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2351)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2351 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2351) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2351))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2351)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0146 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 146 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 146 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2336
  · exact g32p_row31_cosetWord_2337
  · exact g32p_row31_cosetWord_2338
  · exact g32p_row31_cosetWord_2339
  · exact g32p_row31_cosetWord_2340
  · exact g32p_row31_cosetWord_2341
  · exact g32p_row31_cosetWord_2342
  · exact g32p_row31_cosetWord_2343
  · exact g32p_row31_cosetWord_2344
  · exact g32p_row31_cosetWord_2345
  · exact g32p_row31_cosetWord_2346
  · exact g32p_row31_cosetWord_2347
  · exact g32p_row31_cosetWord_2348
  · exact g32p_row31_cosetWord_2349
  · exact g32p_row31_cosetWord_2350
  · exact g32p_row31_cosetWord_2351

theorem g32p_row31_cosetGeneratorBlock_0146 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 146 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 146 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 146 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2336 s
  · exact g32p_row31_cosetGeneratorStep_2337 s
  · exact g32p_row31_cosetGeneratorStep_2338 s
  · exact g32p_row31_cosetGeneratorStep_2339 s
  · exact g32p_row31_cosetGeneratorStep_2340 s
  · exact g32p_row31_cosetGeneratorStep_2341 s
  · exact g32p_row31_cosetGeneratorStep_2342 s
  · exact g32p_row31_cosetGeneratorStep_2343 s
  · exact g32p_row31_cosetGeneratorStep_2344 s
  · exact g32p_row31_cosetGeneratorStep_2345 s
  · exact g32p_row31_cosetGeneratorStep_2346 s
  · exact g32p_row31_cosetGeneratorStep_2347 s
  · exact g32p_row31_cosetGeneratorStep_2348 s
  · exact g32p_row31_cosetGeneratorStep_2349 s
  · exact g32p_row31_cosetGeneratorStep_2350 s
  · exact g32p_row31_cosetGeneratorStep_2351 s

theorem g32p_row31_cosetBranchBlock_0146 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 146 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 146 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 146 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2336 s
  · exact g32p_row31_cosetBranchStep_2337 s
  · exact g32p_row31_cosetBranchStep_2338 s
  · exact g32p_row31_cosetBranchStep_2339 s
  · exact g32p_row31_cosetBranchStep_2340 s
  · exact g32p_row31_cosetBranchStep_2341 s
  · exact g32p_row31_cosetBranchStep_2342 s
  · exact g32p_row31_cosetBranchStep_2343 s
  · exact g32p_row31_cosetBranchStep_2344 s
  · exact g32p_row31_cosetBranchStep_2345 s
  · exact g32p_row31_cosetBranchStep_2346 s
  · exact g32p_row31_cosetBranchStep_2347 s
  · exact g32p_row31_cosetBranchStep_2348 s
  · exact g32p_row31_cosetBranchStep_2349 s
  · exact g32p_row31_cosetBranchStep_2350 s
  · exact g32p_row31_cosetBranchStep_2351 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2352 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2352) = g32p_row31_cosetRepresentatives 2352 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2352 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2352) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2352))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2352)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2352 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2352) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2352))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2352)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2353 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2353) = g32p_row31_cosetRepresentatives 2353 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2353 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2353) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2353))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2353)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2353 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2353) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2353))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2353)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2354 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2354) = g32p_row31_cosetRepresentatives 2354 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2354 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2354) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2354))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2354)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2354 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2354) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2354))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2354)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2355 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2355) = g32p_row31_cosetRepresentatives 2355 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2355 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2355) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2355))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2355)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2355 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2355) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2355))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2355)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2356 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2356) = g32p_row31_cosetRepresentatives 2356 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2356 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2356) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2356))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2356)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2356 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2356) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2356))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2356)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2357 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2357) = g32p_row31_cosetRepresentatives 2357 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2357 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2357) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2357))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2357)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2357 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2357) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2357))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2357)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2358 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2358) = g32p_row31_cosetRepresentatives 2358 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2358 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2358) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2358))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2358)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2358 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2358) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2358))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2358)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2359 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2359) = g32p_row31_cosetRepresentatives 2359 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2359 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2359) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2359))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2359)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2359 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2359) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2359))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2359)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2360 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2360) = g32p_row31_cosetRepresentatives 2360 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2360 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2360) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2360))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2360)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2360 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2360) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2360))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2360)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2361 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2361) = g32p_row31_cosetRepresentatives 2361 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2361 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2361) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2361))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2361)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2361 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2361) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2361))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2361)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2362 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2362) = g32p_row31_cosetRepresentatives 2362 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2362 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2362) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2362))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2362)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2362 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2362) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2362))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2362)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2363 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2363) = g32p_row31_cosetRepresentatives 2363 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2363 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2363) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2363))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2363)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2363 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2363) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2363))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2363)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2364 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2364) = g32p_row31_cosetRepresentatives 2364 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2364 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2364) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2364))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2364)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2364 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2364) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2364))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2364)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2365 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2365) = g32p_row31_cosetRepresentatives 2365 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2365 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2365) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2365))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2365)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2365 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2365) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2365))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2365)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2366 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2366) = g32p_row31_cosetRepresentatives 2366 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2366 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2366) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2366))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2366)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2366 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2366) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2366))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2366)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2367 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2367) = g32p_row31_cosetRepresentatives 2367 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2367 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2367) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2367))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2367)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2367 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2367) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2367))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2367)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0147 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 147 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 147 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2352
  · exact g32p_row31_cosetWord_2353
  · exact g32p_row31_cosetWord_2354
  · exact g32p_row31_cosetWord_2355
  · exact g32p_row31_cosetWord_2356
  · exact g32p_row31_cosetWord_2357
  · exact g32p_row31_cosetWord_2358
  · exact g32p_row31_cosetWord_2359
  · exact g32p_row31_cosetWord_2360
  · exact g32p_row31_cosetWord_2361
  · exact g32p_row31_cosetWord_2362
  · exact g32p_row31_cosetWord_2363
  · exact g32p_row31_cosetWord_2364
  · exact g32p_row31_cosetWord_2365
  · exact g32p_row31_cosetWord_2366
  · exact g32p_row31_cosetWord_2367

theorem g32p_row31_cosetGeneratorBlock_0147 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 147 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 147 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 147 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2352 s
  · exact g32p_row31_cosetGeneratorStep_2353 s
  · exact g32p_row31_cosetGeneratorStep_2354 s
  · exact g32p_row31_cosetGeneratorStep_2355 s
  · exact g32p_row31_cosetGeneratorStep_2356 s
  · exact g32p_row31_cosetGeneratorStep_2357 s
  · exact g32p_row31_cosetGeneratorStep_2358 s
  · exact g32p_row31_cosetGeneratorStep_2359 s
  · exact g32p_row31_cosetGeneratorStep_2360 s
  · exact g32p_row31_cosetGeneratorStep_2361 s
  · exact g32p_row31_cosetGeneratorStep_2362 s
  · exact g32p_row31_cosetGeneratorStep_2363 s
  · exact g32p_row31_cosetGeneratorStep_2364 s
  · exact g32p_row31_cosetGeneratorStep_2365 s
  · exact g32p_row31_cosetGeneratorStep_2366 s
  · exact g32p_row31_cosetGeneratorStep_2367 s

theorem g32p_row31_cosetBranchBlock_0147 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 147 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 147 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 147 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2352 s
  · exact g32p_row31_cosetBranchStep_2353 s
  · exact g32p_row31_cosetBranchStep_2354 s
  · exact g32p_row31_cosetBranchStep_2355 s
  · exact g32p_row31_cosetBranchStep_2356 s
  · exact g32p_row31_cosetBranchStep_2357 s
  · exact g32p_row31_cosetBranchStep_2358 s
  · exact g32p_row31_cosetBranchStep_2359 s
  · exact g32p_row31_cosetBranchStep_2360 s
  · exact g32p_row31_cosetBranchStep_2361 s
  · exact g32p_row31_cosetBranchStep_2362 s
  · exact g32p_row31_cosetBranchStep_2363 s
  · exact g32p_row31_cosetBranchStep_2364 s
  · exact g32p_row31_cosetBranchStep_2365 s
  · exact g32p_row31_cosetBranchStep_2366 s
  · exact g32p_row31_cosetBranchStep_2367 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2368 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2368) = g32p_row31_cosetRepresentatives 2368 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2368 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2368) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2368))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2368)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2368 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2368) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2368))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2368)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2369 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2369) = g32p_row31_cosetRepresentatives 2369 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2369 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2369) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2369))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2369)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2369 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2369) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2369))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2369)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2370 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2370) = g32p_row31_cosetRepresentatives 2370 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2370 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2370) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2370))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2370)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2370 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2370) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2370))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2370)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2371 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2371) = g32p_row31_cosetRepresentatives 2371 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2371 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2371) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2371))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2371)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2371 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2371) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2371))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2371)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2372 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2372) = g32p_row31_cosetRepresentatives 2372 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2372 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2372) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2372))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2372)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2372 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2372) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2372))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2372)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2373 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2373) = g32p_row31_cosetRepresentatives 2373 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2373 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2373) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2373))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2373)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2373 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2373) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2373))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2373)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2374 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2374) = g32p_row31_cosetRepresentatives 2374 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2374 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2374) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2374))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2374)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2374 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2374) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2374))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2374)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2375 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2375) = g32p_row31_cosetRepresentatives 2375 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2375 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2375) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2375))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2375)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2375 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2375) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2375))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2375)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2376 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2376) = g32p_row31_cosetRepresentatives 2376 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2376 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2376) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2376))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2376)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2376 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2376) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2376))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2376)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2377 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2377) = g32p_row31_cosetRepresentatives 2377 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2377 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2377) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2377))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2377)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2377 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2377) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2377))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2377)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2378 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2378) = g32p_row31_cosetRepresentatives 2378 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2378 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2378) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2378))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2378)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2378 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2378) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2378))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2378)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2379 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2379) = g32p_row31_cosetRepresentatives 2379 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2379 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2379) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2379))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2379)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2379 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2379) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2379))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2379)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2380 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2380) = g32p_row31_cosetRepresentatives 2380 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2380 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2380) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2380))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2380)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2380 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2380) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2380))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2380)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2381 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2381) = g32p_row31_cosetRepresentatives 2381 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2381 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2381) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2381))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2381)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2381 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2381) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2381))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2381)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2382 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2382) = g32p_row31_cosetRepresentatives 2382 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2382 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2382) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2382))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2382)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2382 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2382) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2382))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2382)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2383 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2383) = g32p_row31_cosetRepresentatives 2383 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2383 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2383) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2383))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2383)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2383 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2383) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2383))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2383)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0148 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 148 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 148 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2368
  · exact g32p_row31_cosetWord_2369
  · exact g32p_row31_cosetWord_2370
  · exact g32p_row31_cosetWord_2371
  · exact g32p_row31_cosetWord_2372
  · exact g32p_row31_cosetWord_2373
  · exact g32p_row31_cosetWord_2374
  · exact g32p_row31_cosetWord_2375
  · exact g32p_row31_cosetWord_2376
  · exact g32p_row31_cosetWord_2377
  · exact g32p_row31_cosetWord_2378
  · exact g32p_row31_cosetWord_2379
  · exact g32p_row31_cosetWord_2380
  · exact g32p_row31_cosetWord_2381
  · exact g32p_row31_cosetWord_2382
  · exact g32p_row31_cosetWord_2383

theorem g32p_row31_cosetGeneratorBlock_0148 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 148 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 148 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 148 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2368 s
  · exact g32p_row31_cosetGeneratorStep_2369 s
  · exact g32p_row31_cosetGeneratorStep_2370 s
  · exact g32p_row31_cosetGeneratorStep_2371 s
  · exact g32p_row31_cosetGeneratorStep_2372 s
  · exact g32p_row31_cosetGeneratorStep_2373 s
  · exact g32p_row31_cosetGeneratorStep_2374 s
  · exact g32p_row31_cosetGeneratorStep_2375 s
  · exact g32p_row31_cosetGeneratorStep_2376 s
  · exact g32p_row31_cosetGeneratorStep_2377 s
  · exact g32p_row31_cosetGeneratorStep_2378 s
  · exact g32p_row31_cosetGeneratorStep_2379 s
  · exact g32p_row31_cosetGeneratorStep_2380 s
  · exact g32p_row31_cosetGeneratorStep_2381 s
  · exact g32p_row31_cosetGeneratorStep_2382 s
  · exact g32p_row31_cosetGeneratorStep_2383 s

theorem g32p_row31_cosetBranchBlock_0148 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 148 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 148 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 148 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2368 s
  · exact g32p_row31_cosetBranchStep_2369 s
  · exact g32p_row31_cosetBranchStep_2370 s
  · exact g32p_row31_cosetBranchStep_2371 s
  · exact g32p_row31_cosetBranchStep_2372 s
  · exact g32p_row31_cosetBranchStep_2373 s
  · exact g32p_row31_cosetBranchStep_2374 s
  · exact g32p_row31_cosetBranchStep_2375 s
  · exact g32p_row31_cosetBranchStep_2376 s
  · exact g32p_row31_cosetBranchStep_2377 s
  · exact g32p_row31_cosetBranchStep_2378 s
  · exact g32p_row31_cosetBranchStep_2379 s
  · exact g32p_row31_cosetBranchStep_2380 s
  · exact g32p_row31_cosetBranchStep_2381 s
  · exact g32p_row31_cosetBranchStep_2382 s
  · exact g32p_row31_cosetBranchStep_2383 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2384 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2384) = g32p_row31_cosetRepresentatives 2384 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2384 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2384) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2384))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2384)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2384 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2384) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2384))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2384)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2385 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2385) = g32p_row31_cosetRepresentatives 2385 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2385 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2385) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2385))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2385)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2385 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2385) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2385))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2385)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2386 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2386) = g32p_row31_cosetRepresentatives 2386 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2386 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2386) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2386))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2386)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2386 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2386) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2386))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2386)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2387 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2387) = g32p_row31_cosetRepresentatives 2387 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2387 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2387) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2387))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2387)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2387 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2387) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2387))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2387)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2388 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2388) = g32p_row31_cosetRepresentatives 2388 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2388 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2388) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2388))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2388)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2388 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2388) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2388))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2388)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2389 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2389) = g32p_row31_cosetRepresentatives 2389 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2389 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2389) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2389))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2389)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2389 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2389) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2389))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2389)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2390 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2390) = g32p_row31_cosetRepresentatives 2390 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2390 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2390) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2390))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2390)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2390 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2390) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2390))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2390)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2391 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2391) = g32p_row31_cosetRepresentatives 2391 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2391 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2391) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2391))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2391)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2391 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2391) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2391))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2391)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2392 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2392) = g32p_row31_cosetRepresentatives 2392 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2392 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2392) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2392))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2392)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2392 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2392) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2392))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2392)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2393 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2393) = g32p_row31_cosetRepresentatives 2393 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2393 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2393) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2393))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2393)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2393 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2393) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2393))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2393)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2394 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2394) = g32p_row31_cosetRepresentatives 2394 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2394 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2394) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2394))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2394)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2394 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2394) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2394))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2394)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2395 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2395) = g32p_row31_cosetRepresentatives 2395 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2395 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2395) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2395))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2395)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2395 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2395) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2395))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2395)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2396 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2396) = g32p_row31_cosetRepresentatives 2396 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2396 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2396) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2396))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2396)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2396 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2396) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2396))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2396)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2397 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2397) = g32p_row31_cosetRepresentatives 2397 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2397 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2397) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2397))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2397)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2397 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2397) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2397))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2397)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2398 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2398) = g32p_row31_cosetRepresentatives 2398 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2398 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2398) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2398))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2398)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2398 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2398) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2398))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2398)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2399 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2399) = g32p_row31_cosetRepresentatives 2399 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2399 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2399) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2399))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2399)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2399 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2399) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2399))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2399)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0149 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 149 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 149 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2384
  · exact g32p_row31_cosetWord_2385
  · exact g32p_row31_cosetWord_2386
  · exact g32p_row31_cosetWord_2387
  · exact g32p_row31_cosetWord_2388
  · exact g32p_row31_cosetWord_2389
  · exact g32p_row31_cosetWord_2390
  · exact g32p_row31_cosetWord_2391
  · exact g32p_row31_cosetWord_2392
  · exact g32p_row31_cosetWord_2393
  · exact g32p_row31_cosetWord_2394
  · exact g32p_row31_cosetWord_2395
  · exact g32p_row31_cosetWord_2396
  · exact g32p_row31_cosetWord_2397
  · exact g32p_row31_cosetWord_2398
  · exact g32p_row31_cosetWord_2399

theorem g32p_row31_cosetGeneratorBlock_0149 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 149 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 149 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 149 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2384 s
  · exact g32p_row31_cosetGeneratorStep_2385 s
  · exact g32p_row31_cosetGeneratorStep_2386 s
  · exact g32p_row31_cosetGeneratorStep_2387 s
  · exact g32p_row31_cosetGeneratorStep_2388 s
  · exact g32p_row31_cosetGeneratorStep_2389 s
  · exact g32p_row31_cosetGeneratorStep_2390 s
  · exact g32p_row31_cosetGeneratorStep_2391 s
  · exact g32p_row31_cosetGeneratorStep_2392 s
  · exact g32p_row31_cosetGeneratorStep_2393 s
  · exact g32p_row31_cosetGeneratorStep_2394 s
  · exact g32p_row31_cosetGeneratorStep_2395 s
  · exact g32p_row31_cosetGeneratorStep_2396 s
  · exact g32p_row31_cosetGeneratorStep_2397 s
  · exact g32p_row31_cosetGeneratorStep_2398 s
  · exact g32p_row31_cosetGeneratorStep_2399 s

theorem g32p_row31_cosetBranchBlock_0149 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 149 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 149 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 149 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2384 s
  · exact g32p_row31_cosetBranchStep_2385 s
  · exact g32p_row31_cosetBranchStep_2386 s
  · exact g32p_row31_cosetBranchStep_2387 s
  · exact g32p_row31_cosetBranchStep_2388 s
  · exact g32p_row31_cosetBranchStep_2389 s
  · exact g32p_row31_cosetBranchStep_2390 s
  · exact g32p_row31_cosetBranchStep_2391 s
  · exact g32p_row31_cosetBranchStep_2392 s
  · exact g32p_row31_cosetBranchStep_2393 s
  · exact g32p_row31_cosetBranchStep_2394 s
  · exact g32p_row31_cosetBranchStep_2395 s
  · exact g32p_row31_cosetBranchStep_2396 s
  · exact g32p_row31_cosetBranchStep_2397 s
  · exact g32p_row31_cosetBranchStep_2398 s
  · exact g32p_row31_cosetBranchStep_2399 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2400 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2400) = g32p_row31_cosetRepresentatives 2400 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2400 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2400) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2400))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2400)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2400 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2400) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2400))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2400)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2401 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2401) = g32p_row31_cosetRepresentatives 2401 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2401 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2401) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2401))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2401)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2401 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2401) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2401))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2401)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2402 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2402) = g32p_row31_cosetRepresentatives 2402 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2402 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2402) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2402))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2402)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2402 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2402) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2402))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2402)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2403 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2403) = g32p_row31_cosetRepresentatives 2403 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2403 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2403) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2403))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2403)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2403 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2403) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2403))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2403)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2404 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2404) = g32p_row31_cosetRepresentatives 2404 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2404 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2404) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2404))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2404)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2404 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2404) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2404))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2404)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2405 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2405) = g32p_row31_cosetRepresentatives 2405 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2405 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2405) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2405))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2405)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2405 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2405) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2405))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2405)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2406 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2406) = g32p_row31_cosetRepresentatives 2406 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2406 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2406) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2406))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2406)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2406 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2406) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2406))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2406)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2407 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2407) = g32p_row31_cosetRepresentatives 2407 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2407 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2407) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2407))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2407)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2407 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2407) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2407))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2407)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2408 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2408) = g32p_row31_cosetRepresentatives 2408 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2408 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2408) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2408))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2408)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2408 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2408) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2408))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2408)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2409 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2409) = g32p_row31_cosetRepresentatives 2409 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2409 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2409) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2409))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2409)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2409 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2409) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2409))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2409)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2410 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2410) = g32p_row31_cosetRepresentatives 2410 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2410 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2410) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2410))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2410)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2410 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2410) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2410))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2410)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2411 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2411) = g32p_row31_cosetRepresentatives 2411 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2411 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2411) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2411))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2411)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2411 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2411) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2411))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2411)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2412 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2412) = g32p_row31_cosetRepresentatives 2412 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2412 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2412) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2412))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2412)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2412 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2412) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2412))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2412)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2413 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2413) = g32p_row31_cosetRepresentatives 2413 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2413 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2413) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2413))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2413)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2413 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2413) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2413))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2413)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2414 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2414) = g32p_row31_cosetRepresentatives 2414 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2414 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2414) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2414))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2414)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2414 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2414) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2414))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2414)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2415 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2415) = g32p_row31_cosetRepresentatives 2415 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2415 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2415) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2415))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2415)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2415 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2415) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2415))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2415)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0150 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 150 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 150 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2400
  · exact g32p_row31_cosetWord_2401
  · exact g32p_row31_cosetWord_2402
  · exact g32p_row31_cosetWord_2403
  · exact g32p_row31_cosetWord_2404
  · exact g32p_row31_cosetWord_2405
  · exact g32p_row31_cosetWord_2406
  · exact g32p_row31_cosetWord_2407
  · exact g32p_row31_cosetWord_2408
  · exact g32p_row31_cosetWord_2409
  · exact g32p_row31_cosetWord_2410
  · exact g32p_row31_cosetWord_2411
  · exact g32p_row31_cosetWord_2412
  · exact g32p_row31_cosetWord_2413
  · exact g32p_row31_cosetWord_2414
  · exact g32p_row31_cosetWord_2415

theorem g32p_row31_cosetGeneratorBlock_0150 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 150 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 150 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 150 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2400 s
  · exact g32p_row31_cosetGeneratorStep_2401 s
  · exact g32p_row31_cosetGeneratorStep_2402 s
  · exact g32p_row31_cosetGeneratorStep_2403 s
  · exact g32p_row31_cosetGeneratorStep_2404 s
  · exact g32p_row31_cosetGeneratorStep_2405 s
  · exact g32p_row31_cosetGeneratorStep_2406 s
  · exact g32p_row31_cosetGeneratorStep_2407 s
  · exact g32p_row31_cosetGeneratorStep_2408 s
  · exact g32p_row31_cosetGeneratorStep_2409 s
  · exact g32p_row31_cosetGeneratorStep_2410 s
  · exact g32p_row31_cosetGeneratorStep_2411 s
  · exact g32p_row31_cosetGeneratorStep_2412 s
  · exact g32p_row31_cosetGeneratorStep_2413 s
  · exact g32p_row31_cosetGeneratorStep_2414 s
  · exact g32p_row31_cosetGeneratorStep_2415 s

theorem g32p_row31_cosetBranchBlock_0150 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 150 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 150 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 150 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2400 s
  · exact g32p_row31_cosetBranchStep_2401 s
  · exact g32p_row31_cosetBranchStep_2402 s
  · exact g32p_row31_cosetBranchStep_2403 s
  · exact g32p_row31_cosetBranchStep_2404 s
  · exact g32p_row31_cosetBranchStep_2405 s
  · exact g32p_row31_cosetBranchStep_2406 s
  · exact g32p_row31_cosetBranchStep_2407 s
  · exact g32p_row31_cosetBranchStep_2408 s
  · exact g32p_row31_cosetBranchStep_2409 s
  · exact g32p_row31_cosetBranchStep_2410 s
  · exact g32p_row31_cosetBranchStep_2411 s
  · exact g32p_row31_cosetBranchStep_2412 s
  · exact g32p_row31_cosetBranchStep_2413 s
  · exact g32p_row31_cosetBranchStep_2414 s
  · exact g32p_row31_cosetBranchStep_2415 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2416 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2416) = g32p_row31_cosetRepresentatives 2416 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2416 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2416) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2416))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2416)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2416 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2416) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2416))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2416)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2417 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2417) = g32p_row31_cosetRepresentatives 2417 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2417 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2417) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2417))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2417)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2417 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2417) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2417))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2417)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2418 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2418) = g32p_row31_cosetRepresentatives 2418 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2418 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2418) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2418))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2418)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2418 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2418) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2418))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2418)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2419 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2419) = g32p_row31_cosetRepresentatives 2419 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2419 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2419) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2419))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2419)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2419 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2419) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2419))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2419)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2420 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2420) = g32p_row31_cosetRepresentatives 2420 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2420 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2420) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2420))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2420)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2420 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2420) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2420))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2420)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2421 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2421) = g32p_row31_cosetRepresentatives 2421 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2421 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2421) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2421))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2421)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2421 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2421) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2421))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2421)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2422 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2422) = g32p_row31_cosetRepresentatives 2422 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2422 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2422) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2422))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2422)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2422 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2422) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2422))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2422)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2423 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2423) = g32p_row31_cosetRepresentatives 2423 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2423 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2423) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2423))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2423)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2423 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2423) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2423))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2423)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2424 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2424) = g32p_row31_cosetRepresentatives 2424 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2424 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2424) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2424))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2424)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2424 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2424) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2424))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2424)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2425 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2425) = g32p_row31_cosetRepresentatives 2425 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2425 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2425) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2425))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2425)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2425 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2425) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2425))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2425)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2426 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2426) = g32p_row31_cosetRepresentatives 2426 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2426 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2426) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2426))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2426)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2426 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2426) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2426))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2426)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2427 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2427) = g32p_row31_cosetRepresentatives 2427 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2427 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2427) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2427))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2427)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2427 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2427) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2427))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2427)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2428 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2428) = g32p_row31_cosetRepresentatives 2428 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2428 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2428) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2428))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2428)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2428 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2428) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2428))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2428)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2429 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2429) = g32p_row31_cosetRepresentatives 2429 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2429 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2429) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2429))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2429)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2429 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2429) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2429))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2429)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2430 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2430) = g32p_row31_cosetRepresentatives 2430 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2430 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2430) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2430))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2430)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2430 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2430) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2430))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2430)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2431 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2431) = g32p_row31_cosetRepresentatives 2431 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2431 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2431) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2431))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2431)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2431 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2431) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2431))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2431)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0151 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 151 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 151 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2416
  · exact g32p_row31_cosetWord_2417
  · exact g32p_row31_cosetWord_2418
  · exact g32p_row31_cosetWord_2419
  · exact g32p_row31_cosetWord_2420
  · exact g32p_row31_cosetWord_2421
  · exact g32p_row31_cosetWord_2422
  · exact g32p_row31_cosetWord_2423
  · exact g32p_row31_cosetWord_2424
  · exact g32p_row31_cosetWord_2425
  · exact g32p_row31_cosetWord_2426
  · exact g32p_row31_cosetWord_2427
  · exact g32p_row31_cosetWord_2428
  · exact g32p_row31_cosetWord_2429
  · exact g32p_row31_cosetWord_2430
  · exact g32p_row31_cosetWord_2431

theorem g32p_row31_cosetGeneratorBlock_0151 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 151 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 151 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 151 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2416 s
  · exact g32p_row31_cosetGeneratorStep_2417 s
  · exact g32p_row31_cosetGeneratorStep_2418 s
  · exact g32p_row31_cosetGeneratorStep_2419 s
  · exact g32p_row31_cosetGeneratorStep_2420 s
  · exact g32p_row31_cosetGeneratorStep_2421 s
  · exact g32p_row31_cosetGeneratorStep_2422 s
  · exact g32p_row31_cosetGeneratorStep_2423 s
  · exact g32p_row31_cosetGeneratorStep_2424 s
  · exact g32p_row31_cosetGeneratorStep_2425 s
  · exact g32p_row31_cosetGeneratorStep_2426 s
  · exact g32p_row31_cosetGeneratorStep_2427 s
  · exact g32p_row31_cosetGeneratorStep_2428 s
  · exact g32p_row31_cosetGeneratorStep_2429 s
  · exact g32p_row31_cosetGeneratorStep_2430 s
  · exact g32p_row31_cosetGeneratorStep_2431 s

theorem g32p_row31_cosetBranchBlock_0151 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 151 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 151 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 151 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2416 s
  · exact g32p_row31_cosetBranchStep_2417 s
  · exact g32p_row31_cosetBranchStep_2418 s
  · exact g32p_row31_cosetBranchStep_2419 s
  · exact g32p_row31_cosetBranchStep_2420 s
  · exact g32p_row31_cosetBranchStep_2421 s
  · exact g32p_row31_cosetBranchStep_2422 s
  · exact g32p_row31_cosetBranchStep_2423 s
  · exact g32p_row31_cosetBranchStep_2424 s
  · exact g32p_row31_cosetBranchStep_2425 s
  · exact g32p_row31_cosetBranchStep_2426 s
  · exact g32p_row31_cosetBranchStep_2427 s
  · exact g32p_row31_cosetBranchStep_2428 s
  · exact g32p_row31_cosetBranchStep_2429 s
  · exact g32p_row31_cosetBranchStep_2430 s
  · exact g32p_row31_cosetBranchStep_2431 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2432 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2432) = g32p_row31_cosetRepresentatives 2432 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2432 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2432) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2432))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2432)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2432 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2432) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2432))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2432)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2433 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2433) = g32p_row31_cosetRepresentatives 2433 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2433 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2433) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2433))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2433)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2433 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2433) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2433))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2433)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2434 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2434) = g32p_row31_cosetRepresentatives 2434 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2434 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2434) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2434))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2434)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2434 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2434) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2434))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2434)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2435 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2435) = g32p_row31_cosetRepresentatives 2435 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2435 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2435) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2435))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2435)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2435 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2435) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2435))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2435)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2436 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2436) = g32p_row31_cosetRepresentatives 2436 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2436 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2436) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2436))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2436)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2436 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2436) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2436))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2436)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2437 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2437) = g32p_row31_cosetRepresentatives 2437 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2437 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2437) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2437))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2437)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2437 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2437) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2437))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2437)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2438 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2438) = g32p_row31_cosetRepresentatives 2438 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2438 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2438) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2438))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2438)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2438 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2438) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2438))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2438)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2439 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2439) = g32p_row31_cosetRepresentatives 2439 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2439 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2439) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2439))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2439)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2439 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2439) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2439))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2439)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2440 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2440) = g32p_row31_cosetRepresentatives 2440 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2440 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2440) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2440))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2440)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2440 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2440) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2440))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2440)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2441 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2441) = g32p_row31_cosetRepresentatives 2441 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2441 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2441) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2441))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2441)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2441 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2441) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2441))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2441)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2442 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2442) = g32p_row31_cosetRepresentatives 2442 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2442 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2442) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2442))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2442)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2442 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2442) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2442))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2442)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2443 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2443) = g32p_row31_cosetRepresentatives 2443 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2443 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2443) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2443))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2443)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2443 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2443) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2443))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2443)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2444 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2444) = g32p_row31_cosetRepresentatives 2444 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2444 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2444) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2444))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2444)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2444 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2444) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2444))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2444)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2445 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2445) = g32p_row31_cosetRepresentatives 2445 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2445 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2445) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2445))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2445)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2445 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2445) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2445))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2445)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2446 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2446) = g32p_row31_cosetRepresentatives 2446 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2446 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2446) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2446))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2446)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2446 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2446) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2446))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2446)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2447 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2447) = g32p_row31_cosetRepresentatives 2447 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2447 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2447) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2447))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2447)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2447 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2447) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2447))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2447)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0152 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 152 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 152 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2432
  · exact g32p_row31_cosetWord_2433
  · exact g32p_row31_cosetWord_2434
  · exact g32p_row31_cosetWord_2435
  · exact g32p_row31_cosetWord_2436
  · exact g32p_row31_cosetWord_2437
  · exact g32p_row31_cosetWord_2438
  · exact g32p_row31_cosetWord_2439
  · exact g32p_row31_cosetWord_2440
  · exact g32p_row31_cosetWord_2441
  · exact g32p_row31_cosetWord_2442
  · exact g32p_row31_cosetWord_2443
  · exact g32p_row31_cosetWord_2444
  · exact g32p_row31_cosetWord_2445
  · exact g32p_row31_cosetWord_2446
  · exact g32p_row31_cosetWord_2447

theorem g32p_row31_cosetGeneratorBlock_0152 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 152 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 152 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 152 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2432 s
  · exact g32p_row31_cosetGeneratorStep_2433 s
  · exact g32p_row31_cosetGeneratorStep_2434 s
  · exact g32p_row31_cosetGeneratorStep_2435 s
  · exact g32p_row31_cosetGeneratorStep_2436 s
  · exact g32p_row31_cosetGeneratorStep_2437 s
  · exact g32p_row31_cosetGeneratorStep_2438 s
  · exact g32p_row31_cosetGeneratorStep_2439 s
  · exact g32p_row31_cosetGeneratorStep_2440 s
  · exact g32p_row31_cosetGeneratorStep_2441 s
  · exact g32p_row31_cosetGeneratorStep_2442 s
  · exact g32p_row31_cosetGeneratorStep_2443 s
  · exact g32p_row31_cosetGeneratorStep_2444 s
  · exact g32p_row31_cosetGeneratorStep_2445 s
  · exact g32p_row31_cosetGeneratorStep_2446 s
  · exact g32p_row31_cosetGeneratorStep_2447 s

theorem g32p_row31_cosetBranchBlock_0152 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 152 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 152 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 152 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2432 s
  · exact g32p_row31_cosetBranchStep_2433 s
  · exact g32p_row31_cosetBranchStep_2434 s
  · exact g32p_row31_cosetBranchStep_2435 s
  · exact g32p_row31_cosetBranchStep_2436 s
  · exact g32p_row31_cosetBranchStep_2437 s
  · exact g32p_row31_cosetBranchStep_2438 s
  · exact g32p_row31_cosetBranchStep_2439 s
  · exact g32p_row31_cosetBranchStep_2440 s
  · exact g32p_row31_cosetBranchStep_2441 s
  · exact g32p_row31_cosetBranchStep_2442 s
  · exact g32p_row31_cosetBranchStep_2443 s
  · exact g32p_row31_cosetBranchStep_2444 s
  · exact g32p_row31_cosetBranchStep_2445 s
  · exact g32p_row31_cosetBranchStep_2446 s
  · exact g32p_row31_cosetBranchStep_2447 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2448 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2448) = g32p_row31_cosetRepresentatives 2448 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2448 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2448) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2448))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2448)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2448 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2448) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2448))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2448)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2449 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2449) = g32p_row31_cosetRepresentatives 2449 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2449 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2449) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2449))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2449)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2449 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2449) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2449))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2449)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2450 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2450) = g32p_row31_cosetRepresentatives 2450 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2450 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2450) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2450))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2450)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2450 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2450) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2450))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2450)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2451 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2451) = g32p_row31_cosetRepresentatives 2451 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2451 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2451) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2451))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2451)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2451 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2451) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2451))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2451)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2452 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2452) = g32p_row31_cosetRepresentatives 2452 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2452 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2452) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2452))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2452)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2452 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2452) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2452))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2452)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2453 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2453) = g32p_row31_cosetRepresentatives 2453 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2453 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2453) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2453))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2453)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2453 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2453) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2453))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2453)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2454 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2454) = g32p_row31_cosetRepresentatives 2454 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2454 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2454) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2454))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2454)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2454 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2454) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2454))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2454)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2455 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2455) = g32p_row31_cosetRepresentatives 2455 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2455 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2455) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2455))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2455)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2455 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2455) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2455))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2455)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2456 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2456) = g32p_row31_cosetRepresentatives 2456 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2456 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2456) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2456))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2456)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2456 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2456) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2456))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2456)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2457 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2457) = g32p_row31_cosetRepresentatives 2457 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2457 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2457) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2457))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2457)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2457 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2457) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2457))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2457)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2458 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2458) = g32p_row31_cosetRepresentatives 2458 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2458 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2458) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2458))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2458)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2458 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2458) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2458))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2458)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2459 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2459) = g32p_row31_cosetRepresentatives 2459 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2459 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2459) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2459))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2459)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2459 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2459) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2459))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2459)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2460 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2460) = g32p_row31_cosetRepresentatives 2460 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2460 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2460) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2460))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2460)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2460 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2460) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2460))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2460)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2461 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2461) = g32p_row31_cosetRepresentatives 2461 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2461 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2461) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2461))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2461)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2461 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2461) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2461))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2461)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2462 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2462) = g32p_row31_cosetRepresentatives 2462 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2462 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2462) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2462))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2462)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2462 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2462) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2462))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2462)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2463 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2463) = g32p_row31_cosetRepresentatives 2463 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2463 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2463) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2463))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2463)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2463 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2463) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2463))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2463)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0153 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 153 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 153 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2448
  · exact g32p_row31_cosetWord_2449
  · exact g32p_row31_cosetWord_2450
  · exact g32p_row31_cosetWord_2451
  · exact g32p_row31_cosetWord_2452
  · exact g32p_row31_cosetWord_2453
  · exact g32p_row31_cosetWord_2454
  · exact g32p_row31_cosetWord_2455
  · exact g32p_row31_cosetWord_2456
  · exact g32p_row31_cosetWord_2457
  · exact g32p_row31_cosetWord_2458
  · exact g32p_row31_cosetWord_2459
  · exact g32p_row31_cosetWord_2460
  · exact g32p_row31_cosetWord_2461
  · exact g32p_row31_cosetWord_2462
  · exact g32p_row31_cosetWord_2463

theorem g32p_row31_cosetGeneratorBlock_0153 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 153 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 153 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 153 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2448 s
  · exact g32p_row31_cosetGeneratorStep_2449 s
  · exact g32p_row31_cosetGeneratorStep_2450 s
  · exact g32p_row31_cosetGeneratorStep_2451 s
  · exact g32p_row31_cosetGeneratorStep_2452 s
  · exact g32p_row31_cosetGeneratorStep_2453 s
  · exact g32p_row31_cosetGeneratorStep_2454 s
  · exact g32p_row31_cosetGeneratorStep_2455 s
  · exact g32p_row31_cosetGeneratorStep_2456 s
  · exact g32p_row31_cosetGeneratorStep_2457 s
  · exact g32p_row31_cosetGeneratorStep_2458 s
  · exact g32p_row31_cosetGeneratorStep_2459 s
  · exact g32p_row31_cosetGeneratorStep_2460 s
  · exact g32p_row31_cosetGeneratorStep_2461 s
  · exact g32p_row31_cosetGeneratorStep_2462 s
  · exact g32p_row31_cosetGeneratorStep_2463 s

theorem g32p_row31_cosetBranchBlock_0153 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 153 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 153 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 153 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2448 s
  · exact g32p_row31_cosetBranchStep_2449 s
  · exact g32p_row31_cosetBranchStep_2450 s
  · exact g32p_row31_cosetBranchStep_2451 s
  · exact g32p_row31_cosetBranchStep_2452 s
  · exact g32p_row31_cosetBranchStep_2453 s
  · exact g32p_row31_cosetBranchStep_2454 s
  · exact g32p_row31_cosetBranchStep_2455 s
  · exact g32p_row31_cosetBranchStep_2456 s
  · exact g32p_row31_cosetBranchStep_2457 s
  · exact g32p_row31_cosetBranchStep_2458 s
  · exact g32p_row31_cosetBranchStep_2459 s
  · exact g32p_row31_cosetBranchStep_2460 s
  · exact g32p_row31_cosetBranchStep_2461 s
  · exact g32p_row31_cosetBranchStep_2462 s
  · exact g32p_row31_cosetBranchStep_2463 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2464 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2464) = g32p_row31_cosetRepresentatives 2464 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2464 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2464) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2464))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2464)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2464 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2464) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2464))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2464)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2465 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2465) = g32p_row31_cosetRepresentatives 2465 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2465 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2465) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2465))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2465)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2465 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2465) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2465))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2465)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2466 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2466) = g32p_row31_cosetRepresentatives 2466 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2466 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2466) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2466))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2466)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2466 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2466) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2466))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2466)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2467 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2467) = g32p_row31_cosetRepresentatives 2467 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2467 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2467) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2467))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2467)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2467 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2467) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2467))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2467)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2468 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2468) = g32p_row31_cosetRepresentatives 2468 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2468 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2468) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2468))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2468)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2468 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2468) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2468))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2468)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2469 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2469) = g32p_row31_cosetRepresentatives 2469 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2469 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2469) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2469))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2469)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2469 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2469) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2469))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2469)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2470 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2470) = g32p_row31_cosetRepresentatives 2470 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2470 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2470) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2470))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2470)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2470 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2470) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2470))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2470)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2471 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2471) = g32p_row31_cosetRepresentatives 2471 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2471 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2471) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2471))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2471)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2471 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2471) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2471))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2471)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2472 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2472) = g32p_row31_cosetRepresentatives 2472 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2472 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2472) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2472))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2472)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2472 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2472) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2472))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2472)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2473 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2473) = g32p_row31_cosetRepresentatives 2473 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2473 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2473) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2473))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2473)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2473 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2473) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2473))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2473)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2474 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2474) = g32p_row31_cosetRepresentatives 2474 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2474 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2474) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2474))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2474)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2474 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2474) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2474))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2474)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2475 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2475) = g32p_row31_cosetRepresentatives 2475 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2475 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2475) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2475))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2475)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2475 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2475) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2475))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2475)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2476 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2476) = g32p_row31_cosetRepresentatives 2476 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2476 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2476) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2476))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2476)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2476 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2476) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2476))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2476)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2477 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2477) = g32p_row31_cosetRepresentatives 2477 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2477 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2477) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2477))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2477)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2477 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2477) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2477))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2477)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2478 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2478) = g32p_row31_cosetRepresentatives 2478 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2478 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2478) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2478))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2478)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2478 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2478) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2478))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2478)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2479 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2479) = g32p_row31_cosetRepresentatives 2479 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2479 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2479) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2479))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2479)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2479 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2479) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2479))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2479)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0154 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 154 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 154 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2464
  · exact g32p_row31_cosetWord_2465
  · exact g32p_row31_cosetWord_2466
  · exact g32p_row31_cosetWord_2467
  · exact g32p_row31_cosetWord_2468
  · exact g32p_row31_cosetWord_2469
  · exact g32p_row31_cosetWord_2470
  · exact g32p_row31_cosetWord_2471
  · exact g32p_row31_cosetWord_2472
  · exact g32p_row31_cosetWord_2473
  · exact g32p_row31_cosetWord_2474
  · exact g32p_row31_cosetWord_2475
  · exact g32p_row31_cosetWord_2476
  · exact g32p_row31_cosetWord_2477
  · exact g32p_row31_cosetWord_2478
  · exact g32p_row31_cosetWord_2479

theorem g32p_row31_cosetGeneratorBlock_0154 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 154 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 154 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 154 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2464 s
  · exact g32p_row31_cosetGeneratorStep_2465 s
  · exact g32p_row31_cosetGeneratorStep_2466 s
  · exact g32p_row31_cosetGeneratorStep_2467 s
  · exact g32p_row31_cosetGeneratorStep_2468 s
  · exact g32p_row31_cosetGeneratorStep_2469 s
  · exact g32p_row31_cosetGeneratorStep_2470 s
  · exact g32p_row31_cosetGeneratorStep_2471 s
  · exact g32p_row31_cosetGeneratorStep_2472 s
  · exact g32p_row31_cosetGeneratorStep_2473 s
  · exact g32p_row31_cosetGeneratorStep_2474 s
  · exact g32p_row31_cosetGeneratorStep_2475 s
  · exact g32p_row31_cosetGeneratorStep_2476 s
  · exact g32p_row31_cosetGeneratorStep_2477 s
  · exact g32p_row31_cosetGeneratorStep_2478 s
  · exact g32p_row31_cosetGeneratorStep_2479 s

theorem g32p_row31_cosetBranchBlock_0154 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 154 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 154 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 154 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2464 s
  · exact g32p_row31_cosetBranchStep_2465 s
  · exact g32p_row31_cosetBranchStep_2466 s
  · exact g32p_row31_cosetBranchStep_2467 s
  · exact g32p_row31_cosetBranchStep_2468 s
  · exact g32p_row31_cosetBranchStep_2469 s
  · exact g32p_row31_cosetBranchStep_2470 s
  · exact g32p_row31_cosetBranchStep_2471 s
  · exact g32p_row31_cosetBranchStep_2472 s
  · exact g32p_row31_cosetBranchStep_2473 s
  · exact g32p_row31_cosetBranchStep_2474 s
  · exact g32p_row31_cosetBranchStep_2475 s
  · exact g32p_row31_cosetBranchStep_2476 s
  · exact g32p_row31_cosetBranchStep_2477 s
  · exact g32p_row31_cosetBranchStep_2478 s
  · exact g32p_row31_cosetBranchStep_2479 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2480 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2480) = g32p_row31_cosetRepresentatives 2480 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2480 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2480) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2480))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2480)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2480 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2480) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2480))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2480)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2481 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2481) = g32p_row31_cosetRepresentatives 2481 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2481 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2481) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2481))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2481)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2481 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2481) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2481))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2481)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2482 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2482) = g32p_row31_cosetRepresentatives 2482 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2482 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2482) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2482))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2482)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2482 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2482) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2482))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2482)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2483 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2483) = g32p_row31_cosetRepresentatives 2483 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2483 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2483) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2483))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2483)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2483 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2483) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2483))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2483)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2484 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2484) = g32p_row31_cosetRepresentatives 2484 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2484 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2484) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2484))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2484)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2484 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2484) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2484))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2484)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2485 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2485) = g32p_row31_cosetRepresentatives 2485 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2485 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2485) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2485))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2485)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2485 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2485) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2485))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2485)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2486 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2486) = g32p_row31_cosetRepresentatives 2486 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2486 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2486) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2486))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2486)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2486 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2486) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2486))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2486)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2487 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2487) = g32p_row31_cosetRepresentatives 2487 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2487 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2487) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2487))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2487)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2487 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2487) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2487))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2487)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2488 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2488) = g32p_row31_cosetRepresentatives 2488 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2488 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2488) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2488))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2488)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2488 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2488) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2488))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2488)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2489 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2489) = g32p_row31_cosetRepresentatives 2489 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2489 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2489) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2489))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2489)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2489 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2489) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2489))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2489)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2490 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2490) = g32p_row31_cosetRepresentatives 2490 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2490 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2490) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2490))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2490)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2490 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2490) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2490))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2490)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2491 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2491) = g32p_row31_cosetRepresentatives 2491 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2491 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2491) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2491))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2491)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2491 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2491) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2491))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2491)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2492 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2492) = g32p_row31_cosetRepresentatives 2492 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2492 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2492) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2492))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2492)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2492 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2492) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2492))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2492)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2493 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2493) = g32p_row31_cosetRepresentatives 2493 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2493 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2493) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2493))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2493)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2493 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2493) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2493))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2493)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2494 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2494) = g32p_row31_cosetRepresentatives 2494 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2494 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2494) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2494))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2494)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2494 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2494) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2494))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2494)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2495 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2495) = g32p_row31_cosetRepresentatives 2495 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2495 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2495) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2495))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2495)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2495 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2495) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2495))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2495)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0155 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 155 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 155 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2480
  · exact g32p_row31_cosetWord_2481
  · exact g32p_row31_cosetWord_2482
  · exact g32p_row31_cosetWord_2483
  · exact g32p_row31_cosetWord_2484
  · exact g32p_row31_cosetWord_2485
  · exact g32p_row31_cosetWord_2486
  · exact g32p_row31_cosetWord_2487
  · exact g32p_row31_cosetWord_2488
  · exact g32p_row31_cosetWord_2489
  · exact g32p_row31_cosetWord_2490
  · exact g32p_row31_cosetWord_2491
  · exact g32p_row31_cosetWord_2492
  · exact g32p_row31_cosetWord_2493
  · exact g32p_row31_cosetWord_2494
  · exact g32p_row31_cosetWord_2495

theorem g32p_row31_cosetGeneratorBlock_0155 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 155 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 155 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 155 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2480 s
  · exact g32p_row31_cosetGeneratorStep_2481 s
  · exact g32p_row31_cosetGeneratorStep_2482 s
  · exact g32p_row31_cosetGeneratorStep_2483 s
  · exact g32p_row31_cosetGeneratorStep_2484 s
  · exact g32p_row31_cosetGeneratorStep_2485 s
  · exact g32p_row31_cosetGeneratorStep_2486 s
  · exact g32p_row31_cosetGeneratorStep_2487 s
  · exact g32p_row31_cosetGeneratorStep_2488 s
  · exact g32p_row31_cosetGeneratorStep_2489 s
  · exact g32p_row31_cosetGeneratorStep_2490 s
  · exact g32p_row31_cosetGeneratorStep_2491 s
  · exact g32p_row31_cosetGeneratorStep_2492 s
  · exact g32p_row31_cosetGeneratorStep_2493 s
  · exact g32p_row31_cosetGeneratorStep_2494 s
  · exact g32p_row31_cosetGeneratorStep_2495 s

theorem g32p_row31_cosetBranchBlock_0155 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 155 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 155 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 155 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2480 s
  · exact g32p_row31_cosetBranchStep_2481 s
  · exact g32p_row31_cosetBranchStep_2482 s
  · exact g32p_row31_cosetBranchStep_2483 s
  · exact g32p_row31_cosetBranchStep_2484 s
  · exact g32p_row31_cosetBranchStep_2485 s
  · exact g32p_row31_cosetBranchStep_2486 s
  · exact g32p_row31_cosetBranchStep_2487 s
  · exact g32p_row31_cosetBranchStep_2488 s
  · exact g32p_row31_cosetBranchStep_2489 s
  · exact g32p_row31_cosetBranchStep_2490 s
  · exact g32p_row31_cosetBranchStep_2491 s
  · exact g32p_row31_cosetBranchStep_2492 s
  · exact g32p_row31_cosetBranchStep_2493 s
  · exact g32p_row31_cosetBranchStep_2494 s
  · exact g32p_row31_cosetBranchStep_2495 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2496 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2496) = g32p_row31_cosetRepresentatives 2496 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2496 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2496) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2496))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2496)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2496 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2496) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2496))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2496)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2497 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2497) = g32p_row31_cosetRepresentatives 2497 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2497 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2497) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2497))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2497)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2497 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2497) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2497))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2497)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2498 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2498) = g32p_row31_cosetRepresentatives 2498 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2498 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2498) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2498))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2498)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2498 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2498) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2498))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2498)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2499 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2499) = g32p_row31_cosetRepresentatives 2499 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2499 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2499) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2499))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2499)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2499 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2499) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2499))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2499)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2500 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2500) = g32p_row31_cosetRepresentatives 2500 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2500 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2500) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2500))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2500)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2500 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2500) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2500))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2500)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2501 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2501) = g32p_row31_cosetRepresentatives 2501 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2501 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2501) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2501))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2501)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2501 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2501) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2501))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2501)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2502 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2502) = g32p_row31_cosetRepresentatives 2502 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2502 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2502) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2502))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2502)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2502 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2502) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2502))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2502)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2503 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2503) = g32p_row31_cosetRepresentatives 2503 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2503 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2503) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2503))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2503)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2503 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2503) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2503))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2503)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2504 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2504) = g32p_row31_cosetRepresentatives 2504 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2504 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2504) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2504))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2504)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2504 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2504) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2504))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2504)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2505 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2505) = g32p_row31_cosetRepresentatives 2505 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2505 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2505) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2505))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2505)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2505 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2505) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2505))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2505)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2506 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2506) = g32p_row31_cosetRepresentatives 2506 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2506 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2506) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2506))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2506)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2506 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2506) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2506))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2506)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2507 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2507) = g32p_row31_cosetRepresentatives 2507 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2507 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2507) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2507))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2507)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2507 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2507) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2507))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2507)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2508 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2508) = g32p_row31_cosetRepresentatives 2508 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2508 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2508) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2508))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2508)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2508 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2508) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2508))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2508)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2509 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2509) = g32p_row31_cosetRepresentatives 2509 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2509 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2509) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2509))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2509)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2509 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2509) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2509))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2509)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2510 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2510) = g32p_row31_cosetRepresentatives 2510 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2510 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2510) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2510))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2510)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2510 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2510) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2510))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2510)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2511 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2511) = g32p_row31_cosetRepresentatives 2511 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2511 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2511) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2511))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2511)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2511 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2511) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2511))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2511)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0156 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 156 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 156 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2496
  · exact g32p_row31_cosetWord_2497
  · exact g32p_row31_cosetWord_2498
  · exact g32p_row31_cosetWord_2499
  · exact g32p_row31_cosetWord_2500
  · exact g32p_row31_cosetWord_2501
  · exact g32p_row31_cosetWord_2502
  · exact g32p_row31_cosetWord_2503
  · exact g32p_row31_cosetWord_2504
  · exact g32p_row31_cosetWord_2505
  · exact g32p_row31_cosetWord_2506
  · exact g32p_row31_cosetWord_2507
  · exact g32p_row31_cosetWord_2508
  · exact g32p_row31_cosetWord_2509
  · exact g32p_row31_cosetWord_2510
  · exact g32p_row31_cosetWord_2511

theorem g32p_row31_cosetGeneratorBlock_0156 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 156 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 156 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 156 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2496 s
  · exact g32p_row31_cosetGeneratorStep_2497 s
  · exact g32p_row31_cosetGeneratorStep_2498 s
  · exact g32p_row31_cosetGeneratorStep_2499 s
  · exact g32p_row31_cosetGeneratorStep_2500 s
  · exact g32p_row31_cosetGeneratorStep_2501 s
  · exact g32p_row31_cosetGeneratorStep_2502 s
  · exact g32p_row31_cosetGeneratorStep_2503 s
  · exact g32p_row31_cosetGeneratorStep_2504 s
  · exact g32p_row31_cosetGeneratorStep_2505 s
  · exact g32p_row31_cosetGeneratorStep_2506 s
  · exact g32p_row31_cosetGeneratorStep_2507 s
  · exact g32p_row31_cosetGeneratorStep_2508 s
  · exact g32p_row31_cosetGeneratorStep_2509 s
  · exact g32p_row31_cosetGeneratorStep_2510 s
  · exact g32p_row31_cosetGeneratorStep_2511 s

theorem g32p_row31_cosetBranchBlock_0156 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 156 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 156 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 156 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2496 s
  · exact g32p_row31_cosetBranchStep_2497 s
  · exact g32p_row31_cosetBranchStep_2498 s
  · exact g32p_row31_cosetBranchStep_2499 s
  · exact g32p_row31_cosetBranchStep_2500 s
  · exact g32p_row31_cosetBranchStep_2501 s
  · exact g32p_row31_cosetBranchStep_2502 s
  · exact g32p_row31_cosetBranchStep_2503 s
  · exact g32p_row31_cosetBranchStep_2504 s
  · exact g32p_row31_cosetBranchStep_2505 s
  · exact g32p_row31_cosetBranchStep_2506 s
  · exact g32p_row31_cosetBranchStep_2507 s
  · exact g32p_row31_cosetBranchStep_2508 s
  · exact g32p_row31_cosetBranchStep_2509 s
  · exact g32p_row31_cosetBranchStep_2510 s
  · exact g32p_row31_cosetBranchStep_2511 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2512 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2512) = g32p_row31_cosetRepresentatives 2512 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2512 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2512) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2512))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2512)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2512 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2512) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2512))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2512)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2513 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2513) = g32p_row31_cosetRepresentatives 2513 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2513 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2513) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2513))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2513)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2513 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2513) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2513))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2513)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2514 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2514) = g32p_row31_cosetRepresentatives 2514 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2514 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2514) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2514))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2514)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2514 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2514) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2514))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2514)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2515 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2515) = g32p_row31_cosetRepresentatives 2515 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2515 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2515) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2515))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2515)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2515 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2515) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2515))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2515)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2516 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2516) = g32p_row31_cosetRepresentatives 2516 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2516 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2516) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2516))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2516)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2516 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2516) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2516))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2516)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2517 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2517) = g32p_row31_cosetRepresentatives 2517 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2517 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2517) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2517))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2517)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2517 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2517) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2517))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2517)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2518 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2518) = g32p_row31_cosetRepresentatives 2518 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2518 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2518) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2518))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2518)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2518 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2518) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2518))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2518)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2519 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2519) = g32p_row31_cosetRepresentatives 2519 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2519 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2519) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2519))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2519)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2519 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2519) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2519))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2519)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2520 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2520) = g32p_row31_cosetRepresentatives 2520 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2520 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2520) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2520))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2520)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2520 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2520) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2520))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2520)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2521 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2521) = g32p_row31_cosetRepresentatives 2521 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2521 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2521) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2521))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2521)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2521 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2521) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2521))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2521)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2522 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2522) = g32p_row31_cosetRepresentatives 2522 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2522 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2522) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2522))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2522)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2522 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2522) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2522))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2522)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2523 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2523) = g32p_row31_cosetRepresentatives 2523 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2523 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2523) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2523))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2523)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2523 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2523) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2523))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2523)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2524 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2524) = g32p_row31_cosetRepresentatives 2524 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2524 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2524) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2524))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2524)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2524 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2524) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2524))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2524)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2525 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2525) = g32p_row31_cosetRepresentatives 2525 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2525 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2525) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2525))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2525)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2525 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2525) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2525))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2525)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2526 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2526) = g32p_row31_cosetRepresentatives 2526 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2526 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2526) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2526))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2526)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2526 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2526) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2526))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2526)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2527 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2527) = g32p_row31_cosetRepresentatives 2527 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2527 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2527) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2527))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2527)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2527 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2527) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2527))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2527)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0157 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 157 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 157 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2512
  · exact g32p_row31_cosetWord_2513
  · exact g32p_row31_cosetWord_2514
  · exact g32p_row31_cosetWord_2515
  · exact g32p_row31_cosetWord_2516
  · exact g32p_row31_cosetWord_2517
  · exact g32p_row31_cosetWord_2518
  · exact g32p_row31_cosetWord_2519
  · exact g32p_row31_cosetWord_2520
  · exact g32p_row31_cosetWord_2521
  · exact g32p_row31_cosetWord_2522
  · exact g32p_row31_cosetWord_2523
  · exact g32p_row31_cosetWord_2524
  · exact g32p_row31_cosetWord_2525
  · exact g32p_row31_cosetWord_2526
  · exact g32p_row31_cosetWord_2527

theorem g32p_row31_cosetGeneratorBlock_0157 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 157 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 157 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 157 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2512 s
  · exact g32p_row31_cosetGeneratorStep_2513 s
  · exact g32p_row31_cosetGeneratorStep_2514 s
  · exact g32p_row31_cosetGeneratorStep_2515 s
  · exact g32p_row31_cosetGeneratorStep_2516 s
  · exact g32p_row31_cosetGeneratorStep_2517 s
  · exact g32p_row31_cosetGeneratorStep_2518 s
  · exact g32p_row31_cosetGeneratorStep_2519 s
  · exact g32p_row31_cosetGeneratorStep_2520 s
  · exact g32p_row31_cosetGeneratorStep_2521 s
  · exact g32p_row31_cosetGeneratorStep_2522 s
  · exact g32p_row31_cosetGeneratorStep_2523 s
  · exact g32p_row31_cosetGeneratorStep_2524 s
  · exact g32p_row31_cosetGeneratorStep_2525 s
  · exact g32p_row31_cosetGeneratorStep_2526 s
  · exact g32p_row31_cosetGeneratorStep_2527 s

theorem g32p_row31_cosetBranchBlock_0157 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 157 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 157 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 157 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2512 s
  · exact g32p_row31_cosetBranchStep_2513 s
  · exact g32p_row31_cosetBranchStep_2514 s
  · exact g32p_row31_cosetBranchStep_2515 s
  · exact g32p_row31_cosetBranchStep_2516 s
  · exact g32p_row31_cosetBranchStep_2517 s
  · exact g32p_row31_cosetBranchStep_2518 s
  · exact g32p_row31_cosetBranchStep_2519 s
  · exact g32p_row31_cosetBranchStep_2520 s
  · exact g32p_row31_cosetBranchStep_2521 s
  · exact g32p_row31_cosetBranchStep_2522 s
  · exact g32p_row31_cosetBranchStep_2523 s
  · exact g32p_row31_cosetBranchStep_2524 s
  · exact g32p_row31_cosetBranchStep_2525 s
  · exact g32p_row31_cosetBranchStep_2526 s
  · exact g32p_row31_cosetBranchStep_2527 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2528 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2528) = g32p_row31_cosetRepresentatives 2528 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2528 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2528) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2528))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2528)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2528 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2528) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2528))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2528)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2529 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2529) = g32p_row31_cosetRepresentatives 2529 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2529 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2529) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2529))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2529)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2529 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2529) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2529))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2529)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2530 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2530) = g32p_row31_cosetRepresentatives 2530 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2530 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2530) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2530))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2530)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2530 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2530) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2530))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2530)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2531 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2531) = g32p_row31_cosetRepresentatives 2531 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2531 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2531) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2531))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2531)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2531 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2531) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2531))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2531)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2532 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2532) = g32p_row31_cosetRepresentatives 2532 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2532 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2532) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2532))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2532)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2532 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2532) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2532))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2532)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2533 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2533) = g32p_row31_cosetRepresentatives 2533 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2533 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2533) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2533))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2533)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2533 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2533) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2533))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2533)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2534 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2534) = g32p_row31_cosetRepresentatives 2534 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2534 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2534) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2534))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2534)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2534 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2534) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2534))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2534)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2535 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2535) = g32p_row31_cosetRepresentatives 2535 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2535 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2535) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2535))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2535)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2535 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2535) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2535))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2535)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2536 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2536) = g32p_row31_cosetRepresentatives 2536 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2536 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2536) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2536))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2536)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2536 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2536) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2536))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2536)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2537 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2537) = g32p_row31_cosetRepresentatives 2537 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2537 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2537) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2537))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2537)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2537 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2537) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2537))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2537)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2538 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2538) = g32p_row31_cosetRepresentatives 2538 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2538 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2538) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2538))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2538)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2538 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2538) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2538))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2538)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2539 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2539) = g32p_row31_cosetRepresentatives 2539 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2539 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2539) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2539))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2539)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2539 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2539) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2539))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2539)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2540 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2540) = g32p_row31_cosetRepresentatives 2540 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2540 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2540) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2540))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2540)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2540 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2540) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2540))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2540)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2541 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2541) = g32p_row31_cosetRepresentatives 2541 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2541 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2541) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2541))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2541)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2541 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2541) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2541))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2541)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2542 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2542) = g32p_row31_cosetRepresentatives 2542 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2542 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2542) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2542))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2542)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2542 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2542) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2542))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2542)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2543 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2543) = g32p_row31_cosetRepresentatives 2543 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2543 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2543) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2543))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2543)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2543 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2543) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2543))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2543)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0158 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 158 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 158 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2528
  · exact g32p_row31_cosetWord_2529
  · exact g32p_row31_cosetWord_2530
  · exact g32p_row31_cosetWord_2531
  · exact g32p_row31_cosetWord_2532
  · exact g32p_row31_cosetWord_2533
  · exact g32p_row31_cosetWord_2534
  · exact g32p_row31_cosetWord_2535
  · exact g32p_row31_cosetWord_2536
  · exact g32p_row31_cosetWord_2537
  · exact g32p_row31_cosetWord_2538
  · exact g32p_row31_cosetWord_2539
  · exact g32p_row31_cosetWord_2540
  · exact g32p_row31_cosetWord_2541
  · exact g32p_row31_cosetWord_2542
  · exact g32p_row31_cosetWord_2543

theorem g32p_row31_cosetGeneratorBlock_0158 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 158 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 158 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 158 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2528 s
  · exact g32p_row31_cosetGeneratorStep_2529 s
  · exact g32p_row31_cosetGeneratorStep_2530 s
  · exact g32p_row31_cosetGeneratorStep_2531 s
  · exact g32p_row31_cosetGeneratorStep_2532 s
  · exact g32p_row31_cosetGeneratorStep_2533 s
  · exact g32p_row31_cosetGeneratorStep_2534 s
  · exact g32p_row31_cosetGeneratorStep_2535 s
  · exact g32p_row31_cosetGeneratorStep_2536 s
  · exact g32p_row31_cosetGeneratorStep_2537 s
  · exact g32p_row31_cosetGeneratorStep_2538 s
  · exact g32p_row31_cosetGeneratorStep_2539 s
  · exact g32p_row31_cosetGeneratorStep_2540 s
  · exact g32p_row31_cosetGeneratorStep_2541 s
  · exact g32p_row31_cosetGeneratorStep_2542 s
  · exact g32p_row31_cosetGeneratorStep_2543 s

theorem g32p_row31_cosetBranchBlock_0158 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 158 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 158 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 158 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2528 s
  · exact g32p_row31_cosetBranchStep_2529 s
  · exact g32p_row31_cosetBranchStep_2530 s
  · exact g32p_row31_cosetBranchStep_2531 s
  · exact g32p_row31_cosetBranchStep_2532 s
  · exact g32p_row31_cosetBranchStep_2533 s
  · exact g32p_row31_cosetBranchStep_2534 s
  · exact g32p_row31_cosetBranchStep_2535 s
  · exact g32p_row31_cosetBranchStep_2536 s
  · exact g32p_row31_cosetBranchStep_2537 s
  · exact g32p_row31_cosetBranchStep_2538 s
  · exact g32p_row31_cosetBranchStep_2539 s
  · exact g32p_row31_cosetBranchStep_2540 s
  · exact g32p_row31_cosetBranchStep_2541 s
  · exact g32p_row31_cosetBranchStep_2542 s
  · exact g32p_row31_cosetBranchStep_2543 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_2544 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2544) = g32p_row31_cosetRepresentatives 2544 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2544 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2544) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2544))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2544)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2544 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2544) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2544))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2544)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2545 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2545) = g32p_row31_cosetRepresentatives 2545 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2545 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2545) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2545))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2545)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2545 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2545) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2545))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2545)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2546 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2546) = g32p_row31_cosetRepresentatives 2546 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2546 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2546) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2546))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2546)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2546 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2546) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2546))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2546)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2547 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2547) = g32p_row31_cosetRepresentatives 2547 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2547 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2547) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2547))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2547)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2547 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2547) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2547))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2547)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2548 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2548) = g32p_row31_cosetRepresentatives 2548 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2548 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2548) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2548))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2548)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2548 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2548) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2548))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2548)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2549 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2549) = g32p_row31_cosetRepresentatives 2549 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2549 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2549) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2549))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2549)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2549 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2549) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2549))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2549)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2550 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2550) = g32p_row31_cosetRepresentatives 2550 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2550 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2550) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2550))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2550)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2550 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2550) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2550))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2550)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2551 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2551) = g32p_row31_cosetRepresentatives 2551 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2551 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2551) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2551))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2551)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2551 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2551) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2551))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2551)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2552 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2552) = g32p_row31_cosetRepresentatives 2552 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2552 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2552) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2552))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2552)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2552 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2552) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2552))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2552)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2553 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2553) = g32p_row31_cosetRepresentatives 2553 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2553 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2553) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2553))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2553)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2553 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2553) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2553))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2553)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2554 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2554) = g32p_row31_cosetRepresentatives 2554 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2554 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2554) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2554))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2554)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2554 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2554) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2554))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2554)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2555 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2555) = g32p_row31_cosetRepresentatives 2555 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2555 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2555) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2555))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2555)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2555 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2555) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2555))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2555)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2556 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2556) = g32p_row31_cosetRepresentatives 2556 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2556 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2556) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2556))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2556)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2556 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2556) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2556))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2556)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2557 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2557) = g32p_row31_cosetRepresentatives 2557 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2557 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2557) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2557))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2557)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2557 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2557) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2557))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2557)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2558 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2558) = g32p_row31_cosetRepresentatives 2558 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2558 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2558) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2558))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2558)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2558 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2558) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2558))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2558)) := by
  decide +kernel

theorem g32p_row31_cosetWord_2559 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 2559) = g32p_row31_cosetRepresentatives 2559 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_2559 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 2559) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 2559))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 2559)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_2559 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 2559) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 2559))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 2559)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0159 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 159 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 159 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_2544
  · exact g32p_row31_cosetWord_2545
  · exact g32p_row31_cosetWord_2546
  · exact g32p_row31_cosetWord_2547
  · exact g32p_row31_cosetWord_2548
  · exact g32p_row31_cosetWord_2549
  · exact g32p_row31_cosetWord_2550
  · exact g32p_row31_cosetWord_2551
  · exact g32p_row31_cosetWord_2552
  · exact g32p_row31_cosetWord_2553
  · exact g32p_row31_cosetWord_2554
  · exact g32p_row31_cosetWord_2555
  · exact g32p_row31_cosetWord_2556
  · exact g32p_row31_cosetWord_2557
  · exact g32p_row31_cosetWord_2558
  · exact g32p_row31_cosetWord_2559

theorem g32p_row31_cosetGeneratorBlock_0159 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 159 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 159 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 159 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_2544 s
  · exact g32p_row31_cosetGeneratorStep_2545 s
  · exact g32p_row31_cosetGeneratorStep_2546 s
  · exact g32p_row31_cosetGeneratorStep_2547 s
  · exact g32p_row31_cosetGeneratorStep_2548 s
  · exact g32p_row31_cosetGeneratorStep_2549 s
  · exact g32p_row31_cosetGeneratorStep_2550 s
  · exact g32p_row31_cosetGeneratorStep_2551 s
  · exact g32p_row31_cosetGeneratorStep_2552 s
  · exact g32p_row31_cosetGeneratorStep_2553 s
  · exact g32p_row31_cosetGeneratorStep_2554 s
  · exact g32p_row31_cosetGeneratorStep_2555 s
  · exact g32p_row31_cosetGeneratorStep_2556 s
  · exact g32p_row31_cosetGeneratorStep_2557 s
  · exact g32p_row31_cosetGeneratorStep_2558 s
  · exact g32p_row31_cosetGeneratorStep_2559 s

theorem g32p_row31_cosetBranchBlock_0159 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 159 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 159 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 159 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_2544 s
  · exact g32p_row31_cosetBranchStep_2545 s
  · exact g32p_row31_cosetBranchStep_2546 s
  · exact g32p_row31_cosetBranchStep_2547 s
  · exact g32p_row31_cosetBranchStep_2548 s
  · exact g32p_row31_cosetBranchStep_2549 s
  · exact g32p_row31_cosetBranchStep_2550 s
  · exact g32p_row31_cosetBranchStep_2551 s
  · exact g32p_row31_cosetBranchStep_2552 s
  · exact g32p_row31_cosetBranchStep_2553 s
  · exact g32p_row31_cosetBranchStep_2554 s
  · exact g32p_row31_cosetBranchStep_2555 s
  · exact g32p_row31_cosetBranchStep_2556 s
  · exact g32p_row31_cosetBranchStep_2557 s
  · exact g32p_row31_cosetBranchStep_2558 s
  · exact g32p_row31_cosetBranchStep_2559 s


end HodgeLean.Foundations.Program

end
