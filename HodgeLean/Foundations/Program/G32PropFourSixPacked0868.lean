import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0835

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8192 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8192) = g32p_row31_cosetRepresentatives 8192 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8192 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8192) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8192))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8192)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8192 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8192) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8192))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8192)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8193 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8193) = g32p_row31_cosetRepresentatives 8193 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8193 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8193) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8193))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8193)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8193 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8193) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8193))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8193)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8194 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8194) = g32p_row31_cosetRepresentatives 8194 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8194 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8194) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8194))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8194)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8194 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8194) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8194))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8194)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8195 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8195) = g32p_row31_cosetRepresentatives 8195 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8195 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8195) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8195))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8195)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8195 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8195) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8195))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8195)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8196 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8196) = g32p_row31_cosetRepresentatives 8196 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8196 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8196) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8196))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8196)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8196 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8196) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8196))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8196)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8197 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8197) = g32p_row31_cosetRepresentatives 8197 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8197 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8197) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8197))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8197)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8197 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8197) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8197))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8197)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8198 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8198) = g32p_row31_cosetRepresentatives 8198 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8198 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8198) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8198))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8198)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8198 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8198) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8198))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8198)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8199 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8199) = g32p_row31_cosetRepresentatives 8199 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8199 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8199) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8199))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8199)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8199 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8199) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8199))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8199)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8200 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8200) = g32p_row31_cosetRepresentatives 8200 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8200 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8200) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8200))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8200)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8200 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8200) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8200))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8200)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8201 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8201) = g32p_row31_cosetRepresentatives 8201 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8201 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8201) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8201))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8201)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8201 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8201) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8201))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8201)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8202 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8202) = g32p_row31_cosetRepresentatives 8202 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8202 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8202) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8202))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8202)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8202 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8202) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8202))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8202)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8203 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8203) = g32p_row31_cosetRepresentatives 8203 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8203 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8203) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8203))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8203)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8203 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8203) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8203))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8203)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8204 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8204) = g32p_row31_cosetRepresentatives 8204 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8204 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8204) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8204))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8204)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8204 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8204) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8204))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8204)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8205 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8205) = g32p_row31_cosetRepresentatives 8205 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8205 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8205) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8205))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8205)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8205 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8205) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8205))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8205)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8206 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8206) = g32p_row31_cosetRepresentatives 8206 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8206 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8206) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8206))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8206)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8206 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8206) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8206))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8206)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8207 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8207) = g32p_row31_cosetRepresentatives 8207 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8207 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8207) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8207))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8207)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8207 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8207) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8207))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8207)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0512 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 512 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 512 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8192
  · exact g32p_row31_cosetWord_8193
  · exact g32p_row31_cosetWord_8194
  · exact g32p_row31_cosetWord_8195
  · exact g32p_row31_cosetWord_8196
  · exact g32p_row31_cosetWord_8197
  · exact g32p_row31_cosetWord_8198
  · exact g32p_row31_cosetWord_8199
  · exact g32p_row31_cosetWord_8200
  · exact g32p_row31_cosetWord_8201
  · exact g32p_row31_cosetWord_8202
  · exact g32p_row31_cosetWord_8203
  · exact g32p_row31_cosetWord_8204
  · exact g32p_row31_cosetWord_8205
  · exact g32p_row31_cosetWord_8206
  · exact g32p_row31_cosetWord_8207

theorem g32p_row31_cosetGeneratorBlock_0512 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 512 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 512 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 512 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8192 s
  · exact g32p_row31_cosetGeneratorStep_8193 s
  · exact g32p_row31_cosetGeneratorStep_8194 s
  · exact g32p_row31_cosetGeneratorStep_8195 s
  · exact g32p_row31_cosetGeneratorStep_8196 s
  · exact g32p_row31_cosetGeneratorStep_8197 s
  · exact g32p_row31_cosetGeneratorStep_8198 s
  · exact g32p_row31_cosetGeneratorStep_8199 s
  · exact g32p_row31_cosetGeneratorStep_8200 s
  · exact g32p_row31_cosetGeneratorStep_8201 s
  · exact g32p_row31_cosetGeneratorStep_8202 s
  · exact g32p_row31_cosetGeneratorStep_8203 s
  · exact g32p_row31_cosetGeneratorStep_8204 s
  · exact g32p_row31_cosetGeneratorStep_8205 s
  · exact g32p_row31_cosetGeneratorStep_8206 s
  · exact g32p_row31_cosetGeneratorStep_8207 s

theorem g32p_row31_cosetBranchBlock_0512 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 512 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 512 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 512 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8192 s
  · exact g32p_row31_cosetBranchStep_8193 s
  · exact g32p_row31_cosetBranchStep_8194 s
  · exact g32p_row31_cosetBranchStep_8195 s
  · exact g32p_row31_cosetBranchStep_8196 s
  · exact g32p_row31_cosetBranchStep_8197 s
  · exact g32p_row31_cosetBranchStep_8198 s
  · exact g32p_row31_cosetBranchStep_8199 s
  · exact g32p_row31_cosetBranchStep_8200 s
  · exact g32p_row31_cosetBranchStep_8201 s
  · exact g32p_row31_cosetBranchStep_8202 s
  · exact g32p_row31_cosetBranchStep_8203 s
  · exact g32p_row31_cosetBranchStep_8204 s
  · exact g32p_row31_cosetBranchStep_8205 s
  · exact g32p_row31_cosetBranchStep_8206 s
  · exact g32p_row31_cosetBranchStep_8207 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8208 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8208) = g32p_row31_cosetRepresentatives 8208 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8208 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8208) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8208))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8208)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8208 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8208) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8208))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8208)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8209 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8209) = g32p_row31_cosetRepresentatives 8209 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8209 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8209) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8209))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8209)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8209 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8209) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8209))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8209)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8210 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8210) = g32p_row31_cosetRepresentatives 8210 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8210 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8210) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8210))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8210)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8210 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8210) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8210))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8210)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8211 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8211) = g32p_row31_cosetRepresentatives 8211 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8211 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8211) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8211))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8211)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8211 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8211) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8211))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8211)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8212 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8212) = g32p_row31_cosetRepresentatives 8212 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8212 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8212) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8212))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8212)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8212 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8212) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8212))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8212)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8213 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8213) = g32p_row31_cosetRepresentatives 8213 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8213 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8213) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8213))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8213)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8213 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8213) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8213))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8213)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8214 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8214) = g32p_row31_cosetRepresentatives 8214 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8214 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8214) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8214))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8214)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8214 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8214) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8214))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8214)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8215 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8215) = g32p_row31_cosetRepresentatives 8215 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8215 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8215) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8215))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8215)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8215 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8215) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8215))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8215)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8216 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8216) = g32p_row31_cosetRepresentatives 8216 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8216 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8216) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8216))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8216)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8216 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8216) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8216))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8216)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8217 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8217) = g32p_row31_cosetRepresentatives 8217 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8217 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8217) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8217))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8217)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8217 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8217) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8217))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8217)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8218 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8218) = g32p_row31_cosetRepresentatives 8218 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8218 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8218) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8218))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8218)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8218 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8218) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8218))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8218)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8219 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8219) = g32p_row31_cosetRepresentatives 8219 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8219 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8219) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8219))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8219)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8219 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8219) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8219))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8219)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8220 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8220) = g32p_row31_cosetRepresentatives 8220 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8220 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8220) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8220))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8220)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8220 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8220) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8220))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8220)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8221 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8221) = g32p_row31_cosetRepresentatives 8221 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8221 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8221) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8221))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8221)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8221 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8221) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8221))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8221)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8222 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8222) = g32p_row31_cosetRepresentatives 8222 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8222 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8222) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8222))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8222)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8222 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8222) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8222))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8222)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8223 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8223) = g32p_row31_cosetRepresentatives 8223 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8223 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8223) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8223))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8223)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8223 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8223) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8223))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8223)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0513 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 513 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 513 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8208
  · exact g32p_row31_cosetWord_8209
  · exact g32p_row31_cosetWord_8210
  · exact g32p_row31_cosetWord_8211
  · exact g32p_row31_cosetWord_8212
  · exact g32p_row31_cosetWord_8213
  · exact g32p_row31_cosetWord_8214
  · exact g32p_row31_cosetWord_8215
  · exact g32p_row31_cosetWord_8216
  · exact g32p_row31_cosetWord_8217
  · exact g32p_row31_cosetWord_8218
  · exact g32p_row31_cosetWord_8219
  · exact g32p_row31_cosetWord_8220
  · exact g32p_row31_cosetWord_8221
  · exact g32p_row31_cosetWord_8222
  · exact g32p_row31_cosetWord_8223

theorem g32p_row31_cosetGeneratorBlock_0513 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 513 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 513 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 513 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8208 s
  · exact g32p_row31_cosetGeneratorStep_8209 s
  · exact g32p_row31_cosetGeneratorStep_8210 s
  · exact g32p_row31_cosetGeneratorStep_8211 s
  · exact g32p_row31_cosetGeneratorStep_8212 s
  · exact g32p_row31_cosetGeneratorStep_8213 s
  · exact g32p_row31_cosetGeneratorStep_8214 s
  · exact g32p_row31_cosetGeneratorStep_8215 s
  · exact g32p_row31_cosetGeneratorStep_8216 s
  · exact g32p_row31_cosetGeneratorStep_8217 s
  · exact g32p_row31_cosetGeneratorStep_8218 s
  · exact g32p_row31_cosetGeneratorStep_8219 s
  · exact g32p_row31_cosetGeneratorStep_8220 s
  · exact g32p_row31_cosetGeneratorStep_8221 s
  · exact g32p_row31_cosetGeneratorStep_8222 s
  · exact g32p_row31_cosetGeneratorStep_8223 s

theorem g32p_row31_cosetBranchBlock_0513 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 513 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 513 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 513 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8208 s
  · exact g32p_row31_cosetBranchStep_8209 s
  · exact g32p_row31_cosetBranchStep_8210 s
  · exact g32p_row31_cosetBranchStep_8211 s
  · exact g32p_row31_cosetBranchStep_8212 s
  · exact g32p_row31_cosetBranchStep_8213 s
  · exact g32p_row31_cosetBranchStep_8214 s
  · exact g32p_row31_cosetBranchStep_8215 s
  · exact g32p_row31_cosetBranchStep_8216 s
  · exact g32p_row31_cosetBranchStep_8217 s
  · exact g32p_row31_cosetBranchStep_8218 s
  · exact g32p_row31_cosetBranchStep_8219 s
  · exact g32p_row31_cosetBranchStep_8220 s
  · exact g32p_row31_cosetBranchStep_8221 s
  · exact g32p_row31_cosetBranchStep_8222 s
  · exact g32p_row31_cosetBranchStep_8223 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8224 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8224) = g32p_row31_cosetRepresentatives 8224 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8224 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8224) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8224))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8224)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8224 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8224) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8224))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8224)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8225 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8225) = g32p_row31_cosetRepresentatives 8225 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8225 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8225) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8225))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8225)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8225 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8225) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8225))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8225)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8226 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8226) = g32p_row31_cosetRepresentatives 8226 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8226 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8226) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8226))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8226)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8226 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8226) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8226))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8226)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8227 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8227) = g32p_row31_cosetRepresentatives 8227 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8227 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8227) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8227))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8227)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8227 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8227) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8227))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8227)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8228 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8228) = g32p_row31_cosetRepresentatives 8228 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8228 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8228) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8228))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8228)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8228 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8228) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8228))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8228)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8229 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8229) = g32p_row31_cosetRepresentatives 8229 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8229 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8229) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8229))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8229)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8229 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8229) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8229))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8229)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8230 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8230) = g32p_row31_cosetRepresentatives 8230 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8230 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8230) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8230))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8230)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8230 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8230) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8230))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8230)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8231 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8231) = g32p_row31_cosetRepresentatives 8231 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8231 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8231) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8231))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8231)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8231 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8231) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8231))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8231)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8232 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8232) = g32p_row31_cosetRepresentatives 8232 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8232 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8232) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8232))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8232)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8232 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8232) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8232))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8232)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8233 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8233) = g32p_row31_cosetRepresentatives 8233 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8233 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8233) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8233))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8233)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8233 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8233) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8233))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8233)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8234 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8234) = g32p_row31_cosetRepresentatives 8234 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8234 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8234) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8234))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8234)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8234 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8234) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8234))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8234)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8235 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8235) = g32p_row31_cosetRepresentatives 8235 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8235 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8235) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8235))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8235)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8235 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8235) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8235))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8235)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8236 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8236) = g32p_row31_cosetRepresentatives 8236 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8236 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8236) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8236))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8236)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8236 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8236) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8236))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8236)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8237 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8237) = g32p_row31_cosetRepresentatives 8237 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8237 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8237) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8237))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8237)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8237 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8237) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8237))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8237)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8238 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8238) = g32p_row31_cosetRepresentatives 8238 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8238 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8238) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8238))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8238)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8238 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8238) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8238))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8238)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8239 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8239) = g32p_row31_cosetRepresentatives 8239 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8239 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8239) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8239))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8239)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8239 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8239) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8239))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8239)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0514 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 514 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 514 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8224
  · exact g32p_row31_cosetWord_8225
  · exact g32p_row31_cosetWord_8226
  · exact g32p_row31_cosetWord_8227
  · exact g32p_row31_cosetWord_8228
  · exact g32p_row31_cosetWord_8229
  · exact g32p_row31_cosetWord_8230
  · exact g32p_row31_cosetWord_8231
  · exact g32p_row31_cosetWord_8232
  · exact g32p_row31_cosetWord_8233
  · exact g32p_row31_cosetWord_8234
  · exact g32p_row31_cosetWord_8235
  · exact g32p_row31_cosetWord_8236
  · exact g32p_row31_cosetWord_8237
  · exact g32p_row31_cosetWord_8238
  · exact g32p_row31_cosetWord_8239

theorem g32p_row31_cosetGeneratorBlock_0514 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 514 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 514 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 514 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8224 s
  · exact g32p_row31_cosetGeneratorStep_8225 s
  · exact g32p_row31_cosetGeneratorStep_8226 s
  · exact g32p_row31_cosetGeneratorStep_8227 s
  · exact g32p_row31_cosetGeneratorStep_8228 s
  · exact g32p_row31_cosetGeneratorStep_8229 s
  · exact g32p_row31_cosetGeneratorStep_8230 s
  · exact g32p_row31_cosetGeneratorStep_8231 s
  · exact g32p_row31_cosetGeneratorStep_8232 s
  · exact g32p_row31_cosetGeneratorStep_8233 s
  · exact g32p_row31_cosetGeneratorStep_8234 s
  · exact g32p_row31_cosetGeneratorStep_8235 s
  · exact g32p_row31_cosetGeneratorStep_8236 s
  · exact g32p_row31_cosetGeneratorStep_8237 s
  · exact g32p_row31_cosetGeneratorStep_8238 s
  · exact g32p_row31_cosetGeneratorStep_8239 s

theorem g32p_row31_cosetBranchBlock_0514 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 514 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 514 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 514 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8224 s
  · exact g32p_row31_cosetBranchStep_8225 s
  · exact g32p_row31_cosetBranchStep_8226 s
  · exact g32p_row31_cosetBranchStep_8227 s
  · exact g32p_row31_cosetBranchStep_8228 s
  · exact g32p_row31_cosetBranchStep_8229 s
  · exact g32p_row31_cosetBranchStep_8230 s
  · exact g32p_row31_cosetBranchStep_8231 s
  · exact g32p_row31_cosetBranchStep_8232 s
  · exact g32p_row31_cosetBranchStep_8233 s
  · exact g32p_row31_cosetBranchStep_8234 s
  · exact g32p_row31_cosetBranchStep_8235 s
  · exact g32p_row31_cosetBranchStep_8236 s
  · exact g32p_row31_cosetBranchStep_8237 s
  · exact g32p_row31_cosetBranchStep_8238 s
  · exact g32p_row31_cosetBranchStep_8239 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8240 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8240) = g32p_row31_cosetRepresentatives 8240 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8240 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8240) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8240))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8240)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8240 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8240) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8240))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8240)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8241 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8241) = g32p_row31_cosetRepresentatives 8241 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8241 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8241) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8241))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8241)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8241 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8241) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8241))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8241)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8242 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8242) = g32p_row31_cosetRepresentatives 8242 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8242 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8242) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8242))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8242)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8242 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8242) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8242))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8242)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8243 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8243) = g32p_row31_cosetRepresentatives 8243 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8243 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8243) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8243))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8243)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8243 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8243) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8243))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8243)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8244 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8244) = g32p_row31_cosetRepresentatives 8244 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8244 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8244) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8244))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8244)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8244 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8244) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8244))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8244)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8245 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8245) = g32p_row31_cosetRepresentatives 8245 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8245 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8245) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8245))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8245)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8245 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8245) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8245))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8245)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8246 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8246) = g32p_row31_cosetRepresentatives 8246 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8246 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8246) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8246))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8246)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8246 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8246) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8246))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8246)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8247 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8247) = g32p_row31_cosetRepresentatives 8247 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8247 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8247) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8247))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8247)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8247 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8247) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8247))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8247)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8248 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8248) = g32p_row31_cosetRepresentatives 8248 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8248 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8248) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8248))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8248)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8248 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8248) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8248))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8248)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8249 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8249) = g32p_row31_cosetRepresentatives 8249 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8249 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8249) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8249))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8249)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8249 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8249) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8249))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8249)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8250 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8250) = g32p_row31_cosetRepresentatives 8250 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8250 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8250) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8250))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8250)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8250 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8250) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8250))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8250)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8251 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8251) = g32p_row31_cosetRepresentatives 8251 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8251 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8251) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8251))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8251)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8251 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8251) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8251))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8251)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8252 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8252) = g32p_row31_cosetRepresentatives 8252 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8252 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8252) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8252))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8252)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8252 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8252) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8252))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8252)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8253 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8253) = g32p_row31_cosetRepresentatives 8253 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8253 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8253) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8253))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8253)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8253 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8253) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8253))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8253)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8254 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8254) = g32p_row31_cosetRepresentatives 8254 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8254 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8254) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8254))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8254)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8254 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8254) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8254))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8254)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8255 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8255) = g32p_row31_cosetRepresentatives 8255 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8255 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8255) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8255))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8255)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8255 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8255) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8255))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8255)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0515 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 515 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 515 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8240
  · exact g32p_row31_cosetWord_8241
  · exact g32p_row31_cosetWord_8242
  · exact g32p_row31_cosetWord_8243
  · exact g32p_row31_cosetWord_8244
  · exact g32p_row31_cosetWord_8245
  · exact g32p_row31_cosetWord_8246
  · exact g32p_row31_cosetWord_8247
  · exact g32p_row31_cosetWord_8248
  · exact g32p_row31_cosetWord_8249
  · exact g32p_row31_cosetWord_8250
  · exact g32p_row31_cosetWord_8251
  · exact g32p_row31_cosetWord_8252
  · exact g32p_row31_cosetWord_8253
  · exact g32p_row31_cosetWord_8254
  · exact g32p_row31_cosetWord_8255

theorem g32p_row31_cosetGeneratorBlock_0515 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 515 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 515 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 515 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8240 s
  · exact g32p_row31_cosetGeneratorStep_8241 s
  · exact g32p_row31_cosetGeneratorStep_8242 s
  · exact g32p_row31_cosetGeneratorStep_8243 s
  · exact g32p_row31_cosetGeneratorStep_8244 s
  · exact g32p_row31_cosetGeneratorStep_8245 s
  · exact g32p_row31_cosetGeneratorStep_8246 s
  · exact g32p_row31_cosetGeneratorStep_8247 s
  · exact g32p_row31_cosetGeneratorStep_8248 s
  · exact g32p_row31_cosetGeneratorStep_8249 s
  · exact g32p_row31_cosetGeneratorStep_8250 s
  · exact g32p_row31_cosetGeneratorStep_8251 s
  · exact g32p_row31_cosetGeneratorStep_8252 s
  · exact g32p_row31_cosetGeneratorStep_8253 s
  · exact g32p_row31_cosetGeneratorStep_8254 s
  · exact g32p_row31_cosetGeneratorStep_8255 s

theorem g32p_row31_cosetBranchBlock_0515 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 515 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 515 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 515 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8240 s
  · exact g32p_row31_cosetBranchStep_8241 s
  · exact g32p_row31_cosetBranchStep_8242 s
  · exact g32p_row31_cosetBranchStep_8243 s
  · exact g32p_row31_cosetBranchStep_8244 s
  · exact g32p_row31_cosetBranchStep_8245 s
  · exact g32p_row31_cosetBranchStep_8246 s
  · exact g32p_row31_cosetBranchStep_8247 s
  · exact g32p_row31_cosetBranchStep_8248 s
  · exact g32p_row31_cosetBranchStep_8249 s
  · exact g32p_row31_cosetBranchStep_8250 s
  · exact g32p_row31_cosetBranchStep_8251 s
  · exact g32p_row31_cosetBranchStep_8252 s
  · exact g32p_row31_cosetBranchStep_8253 s
  · exact g32p_row31_cosetBranchStep_8254 s
  · exact g32p_row31_cosetBranchStep_8255 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8256 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8256) = g32p_row31_cosetRepresentatives 8256 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8256) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8256))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8256)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8256) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8256))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8256)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8257 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8257) = g32p_row31_cosetRepresentatives 8257 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8257) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8257))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8257)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8257) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8257))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8257)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8258 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8258) = g32p_row31_cosetRepresentatives 8258 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8258) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8258))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8258)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8258) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8258))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8258)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8259 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8259) = g32p_row31_cosetRepresentatives 8259 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8259) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8259))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8259)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8259) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8259))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8259)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8260 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8260) = g32p_row31_cosetRepresentatives 8260 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8260) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8260))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8260)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8260) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8260))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8260)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8261 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8261) = g32p_row31_cosetRepresentatives 8261 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8261) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8261))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8261)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8261) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8261))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8261)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8262 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8262) = g32p_row31_cosetRepresentatives 8262 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8262) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8262))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8262)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8262) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8262))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8262)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8263 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8263) = g32p_row31_cosetRepresentatives 8263 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8263) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8263))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8263)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8263) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8263))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8263)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8264 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8264) = g32p_row31_cosetRepresentatives 8264 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8264) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8264))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8264)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8264) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8264))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8264)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8265 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8265) = g32p_row31_cosetRepresentatives 8265 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8265) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8265))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8265)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8265) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8265))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8265)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8266 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8266) = g32p_row31_cosetRepresentatives 8266 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8266) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8266))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8266)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8266) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8266))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8266)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8267 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8267) = g32p_row31_cosetRepresentatives 8267 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8267) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8267))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8267)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8267) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8267))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8267)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8268 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8268) = g32p_row31_cosetRepresentatives 8268 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8268) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8268))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8268)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8268) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8268))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8268)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8269 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8269) = g32p_row31_cosetRepresentatives 8269 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8269) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8269))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8269)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8269) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8269))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8269)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8270 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8270) = g32p_row31_cosetRepresentatives 8270 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8270) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8270))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8270)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8270) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8270))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8270)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8271 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8271) = g32p_row31_cosetRepresentatives 8271 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8271) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8271))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8271)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8271) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8271))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8271)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0516 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 516 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 516 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8256
  · exact g32p_row31_cosetWord_8257
  · exact g32p_row31_cosetWord_8258
  · exact g32p_row31_cosetWord_8259
  · exact g32p_row31_cosetWord_8260
  · exact g32p_row31_cosetWord_8261
  · exact g32p_row31_cosetWord_8262
  · exact g32p_row31_cosetWord_8263
  · exact g32p_row31_cosetWord_8264
  · exact g32p_row31_cosetWord_8265
  · exact g32p_row31_cosetWord_8266
  · exact g32p_row31_cosetWord_8267
  · exact g32p_row31_cosetWord_8268
  · exact g32p_row31_cosetWord_8269
  · exact g32p_row31_cosetWord_8270
  · exact g32p_row31_cosetWord_8271

theorem g32p_row31_cosetGeneratorBlock_0516 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 516 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 516 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 516 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8256 s
  · exact g32p_row31_cosetGeneratorStep_8257 s
  · exact g32p_row31_cosetGeneratorStep_8258 s
  · exact g32p_row31_cosetGeneratorStep_8259 s
  · exact g32p_row31_cosetGeneratorStep_8260 s
  · exact g32p_row31_cosetGeneratorStep_8261 s
  · exact g32p_row31_cosetGeneratorStep_8262 s
  · exact g32p_row31_cosetGeneratorStep_8263 s
  · exact g32p_row31_cosetGeneratorStep_8264 s
  · exact g32p_row31_cosetGeneratorStep_8265 s
  · exact g32p_row31_cosetGeneratorStep_8266 s
  · exact g32p_row31_cosetGeneratorStep_8267 s
  · exact g32p_row31_cosetGeneratorStep_8268 s
  · exact g32p_row31_cosetGeneratorStep_8269 s
  · exact g32p_row31_cosetGeneratorStep_8270 s
  · exact g32p_row31_cosetGeneratorStep_8271 s

theorem g32p_row31_cosetBranchBlock_0516 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 516 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 516 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 516 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8256 s
  · exact g32p_row31_cosetBranchStep_8257 s
  · exact g32p_row31_cosetBranchStep_8258 s
  · exact g32p_row31_cosetBranchStep_8259 s
  · exact g32p_row31_cosetBranchStep_8260 s
  · exact g32p_row31_cosetBranchStep_8261 s
  · exact g32p_row31_cosetBranchStep_8262 s
  · exact g32p_row31_cosetBranchStep_8263 s
  · exact g32p_row31_cosetBranchStep_8264 s
  · exact g32p_row31_cosetBranchStep_8265 s
  · exact g32p_row31_cosetBranchStep_8266 s
  · exact g32p_row31_cosetBranchStep_8267 s
  · exact g32p_row31_cosetBranchStep_8268 s
  · exact g32p_row31_cosetBranchStep_8269 s
  · exact g32p_row31_cosetBranchStep_8270 s
  · exact g32p_row31_cosetBranchStep_8271 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8272 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8272) = g32p_row31_cosetRepresentatives 8272 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8272) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8272))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8272)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8272) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8272))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8272)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8273 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8273) = g32p_row31_cosetRepresentatives 8273 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8273) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8273))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8273)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8273) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8273))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8273)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8274 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8274) = g32p_row31_cosetRepresentatives 8274 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8274) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8274))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8274)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8274) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8274))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8274)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8275 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8275) = g32p_row31_cosetRepresentatives 8275 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8275) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8275))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8275)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8275) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8275))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8275)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8276 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8276) = g32p_row31_cosetRepresentatives 8276 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8276) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8276))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8276)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8276) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8276))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8276)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8277 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8277) = g32p_row31_cosetRepresentatives 8277 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8277) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8277))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8277)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8277) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8277))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8277)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8278 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8278) = g32p_row31_cosetRepresentatives 8278 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8278) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8278))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8278)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8278) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8278))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8278)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8279 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8279) = g32p_row31_cosetRepresentatives 8279 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8279) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8279))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8279)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8279) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8279))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8279)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8280 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8280) = g32p_row31_cosetRepresentatives 8280 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8280) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8280))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8280)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8280) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8280))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8280)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8281 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8281) = g32p_row31_cosetRepresentatives 8281 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8281) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8281))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8281)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8281) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8281))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8281)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8282 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8282) = g32p_row31_cosetRepresentatives 8282 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8282) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8282))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8282)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8282) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8282))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8282)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8283 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8283) = g32p_row31_cosetRepresentatives 8283 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8283) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8283))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8283)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8283) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8283))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8283)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8284 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8284) = g32p_row31_cosetRepresentatives 8284 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8284) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8284))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8284)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8284) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8284))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8284)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8285 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8285) = g32p_row31_cosetRepresentatives 8285 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8285) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8285))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8285)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8285) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8285))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8285)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8286 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8286) = g32p_row31_cosetRepresentatives 8286 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8286) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8286))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8286)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8286) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8286))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8286)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8287 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8287) = g32p_row31_cosetRepresentatives 8287 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8287) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8287))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8287)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8287) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8287))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8287)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0517 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 517 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 517 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8272
  · exact g32p_row31_cosetWord_8273
  · exact g32p_row31_cosetWord_8274
  · exact g32p_row31_cosetWord_8275
  · exact g32p_row31_cosetWord_8276
  · exact g32p_row31_cosetWord_8277
  · exact g32p_row31_cosetWord_8278
  · exact g32p_row31_cosetWord_8279
  · exact g32p_row31_cosetWord_8280
  · exact g32p_row31_cosetWord_8281
  · exact g32p_row31_cosetWord_8282
  · exact g32p_row31_cosetWord_8283
  · exact g32p_row31_cosetWord_8284
  · exact g32p_row31_cosetWord_8285
  · exact g32p_row31_cosetWord_8286
  · exact g32p_row31_cosetWord_8287

theorem g32p_row31_cosetGeneratorBlock_0517 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 517 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 517 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 517 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8272 s
  · exact g32p_row31_cosetGeneratorStep_8273 s
  · exact g32p_row31_cosetGeneratorStep_8274 s
  · exact g32p_row31_cosetGeneratorStep_8275 s
  · exact g32p_row31_cosetGeneratorStep_8276 s
  · exact g32p_row31_cosetGeneratorStep_8277 s
  · exact g32p_row31_cosetGeneratorStep_8278 s
  · exact g32p_row31_cosetGeneratorStep_8279 s
  · exact g32p_row31_cosetGeneratorStep_8280 s
  · exact g32p_row31_cosetGeneratorStep_8281 s
  · exact g32p_row31_cosetGeneratorStep_8282 s
  · exact g32p_row31_cosetGeneratorStep_8283 s
  · exact g32p_row31_cosetGeneratorStep_8284 s
  · exact g32p_row31_cosetGeneratorStep_8285 s
  · exact g32p_row31_cosetGeneratorStep_8286 s
  · exact g32p_row31_cosetGeneratorStep_8287 s

theorem g32p_row31_cosetBranchBlock_0517 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 517 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 517 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 517 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8272 s
  · exact g32p_row31_cosetBranchStep_8273 s
  · exact g32p_row31_cosetBranchStep_8274 s
  · exact g32p_row31_cosetBranchStep_8275 s
  · exact g32p_row31_cosetBranchStep_8276 s
  · exact g32p_row31_cosetBranchStep_8277 s
  · exact g32p_row31_cosetBranchStep_8278 s
  · exact g32p_row31_cosetBranchStep_8279 s
  · exact g32p_row31_cosetBranchStep_8280 s
  · exact g32p_row31_cosetBranchStep_8281 s
  · exact g32p_row31_cosetBranchStep_8282 s
  · exact g32p_row31_cosetBranchStep_8283 s
  · exact g32p_row31_cosetBranchStep_8284 s
  · exact g32p_row31_cosetBranchStep_8285 s
  · exact g32p_row31_cosetBranchStep_8286 s
  · exact g32p_row31_cosetBranchStep_8287 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8288 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8288) = g32p_row31_cosetRepresentatives 8288 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8288) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8288))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8288)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8288) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8288))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8288)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8289 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8289) = g32p_row31_cosetRepresentatives 8289 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8289) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8289))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8289)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8289) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8289))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8289)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8290 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8290) = g32p_row31_cosetRepresentatives 8290 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8290) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8290))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8290)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8290) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8290))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8290)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8291 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8291) = g32p_row31_cosetRepresentatives 8291 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8291) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8291))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8291)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8291) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8291))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8291)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8292 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8292) = g32p_row31_cosetRepresentatives 8292 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8292) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8292))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8292)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8292) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8292))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8292)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8293 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8293) = g32p_row31_cosetRepresentatives 8293 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8293) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8293))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8293)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8293) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8293))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8293)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8294 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8294) = g32p_row31_cosetRepresentatives 8294 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8294) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8294))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8294)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8294) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8294))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8294)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8295 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8295) = g32p_row31_cosetRepresentatives 8295 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8295) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8295))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8295)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8295) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8295))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8295)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8296 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8296) = g32p_row31_cosetRepresentatives 8296 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8296) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8296))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8296)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8296) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8296))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8296)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8297 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8297) = g32p_row31_cosetRepresentatives 8297 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8297) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8297))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8297)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8297) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8297))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8297)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8298 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8298) = g32p_row31_cosetRepresentatives 8298 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8298) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8298))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8298)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8298) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8298))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8298)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8299 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8299) = g32p_row31_cosetRepresentatives 8299 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8299) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8299))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8299)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8299) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8299))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8299)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8300 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8300) = g32p_row31_cosetRepresentatives 8300 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8300) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8300))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8300)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8300) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8300))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8300)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8301 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8301) = g32p_row31_cosetRepresentatives 8301 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8301) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8301))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8301)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8301) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8301))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8301)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8302 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8302) = g32p_row31_cosetRepresentatives 8302 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8302) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8302))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8302)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8302) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8302))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8302)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8303 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8303) = g32p_row31_cosetRepresentatives 8303 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8303) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8303))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8303)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8303) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8303))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8303)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0518 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 518 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 518 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8288
  · exact g32p_row31_cosetWord_8289
  · exact g32p_row31_cosetWord_8290
  · exact g32p_row31_cosetWord_8291
  · exact g32p_row31_cosetWord_8292
  · exact g32p_row31_cosetWord_8293
  · exact g32p_row31_cosetWord_8294
  · exact g32p_row31_cosetWord_8295
  · exact g32p_row31_cosetWord_8296
  · exact g32p_row31_cosetWord_8297
  · exact g32p_row31_cosetWord_8298
  · exact g32p_row31_cosetWord_8299
  · exact g32p_row31_cosetWord_8300
  · exact g32p_row31_cosetWord_8301
  · exact g32p_row31_cosetWord_8302
  · exact g32p_row31_cosetWord_8303

theorem g32p_row31_cosetGeneratorBlock_0518 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 518 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 518 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 518 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8288 s
  · exact g32p_row31_cosetGeneratorStep_8289 s
  · exact g32p_row31_cosetGeneratorStep_8290 s
  · exact g32p_row31_cosetGeneratorStep_8291 s
  · exact g32p_row31_cosetGeneratorStep_8292 s
  · exact g32p_row31_cosetGeneratorStep_8293 s
  · exact g32p_row31_cosetGeneratorStep_8294 s
  · exact g32p_row31_cosetGeneratorStep_8295 s
  · exact g32p_row31_cosetGeneratorStep_8296 s
  · exact g32p_row31_cosetGeneratorStep_8297 s
  · exact g32p_row31_cosetGeneratorStep_8298 s
  · exact g32p_row31_cosetGeneratorStep_8299 s
  · exact g32p_row31_cosetGeneratorStep_8300 s
  · exact g32p_row31_cosetGeneratorStep_8301 s
  · exact g32p_row31_cosetGeneratorStep_8302 s
  · exact g32p_row31_cosetGeneratorStep_8303 s

theorem g32p_row31_cosetBranchBlock_0518 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 518 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 518 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 518 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8288 s
  · exact g32p_row31_cosetBranchStep_8289 s
  · exact g32p_row31_cosetBranchStep_8290 s
  · exact g32p_row31_cosetBranchStep_8291 s
  · exact g32p_row31_cosetBranchStep_8292 s
  · exact g32p_row31_cosetBranchStep_8293 s
  · exact g32p_row31_cosetBranchStep_8294 s
  · exact g32p_row31_cosetBranchStep_8295 s
  · exact g32p_row31_cosetBranchStep_8296 s
  · exact g32p_row31_cosetBranchStep_8297 s
  · exact g32p_row31_cosetBranchStep_8298 s
  · exact g32p_row31_cosetBranchStep_8299 s
  · exact g32p_row31_cosetBranchStep_8300 s
  · exact g32p_row31_cosetBranchStep_8301 s
  · exact g32p_row31_cosetBranchStep_8302 s
  · exact g32p_row31_cosetBranchStep_8303 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8304 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8304) = g32p_row31_cosetRepresentatives 8304 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8304) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8304))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8304)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8304) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8304))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8304)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8305 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8305) = g32p_row31_cosetRepresentatives 8305 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8305) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8305))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8305)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8305) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8305))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8305)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8306 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8306) = g32p_row31_cosetRepresentatives 8306 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8306) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8306))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8306)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8306) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8306))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8306)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8307 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8307) = g32p_row31_cosetRepresentatives 8307 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8307) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8307))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8307)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8307) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8307))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8307)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8308 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8308) = g32p_row31_cosetRepresentatives 8308 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8308) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8308))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8308)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8308) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8308))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8308)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8309 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8309) = g32p_row31_cosetRepresentatives 8309 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8309) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8309))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8309)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8309) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8309))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8309)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8310 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8310) = g32p_row31_cosetRepresentatives 8310 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8310) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8310))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8310)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8310) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8310))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8310)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8311 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8311) = g32p_row31_cosetRepresentatives 8311 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8311) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8311))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8311)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8311) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8311))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8311)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8312 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8312) = g32p_row31_cosetRepresentatives 8312 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8312) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8312))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8312)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8312) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8312))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8312)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8313 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8313) = g32p_row31_cosetRepresentatives 8313 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8313) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8313))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8313)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8313) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8313))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8313)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8314 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8314) = g32p_row31_cosetRepresentatives 8314 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8314) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8314))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8314)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8314) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8314))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8314)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8315 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8315) = g32p_row31_cosetRepresentatives 8315 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8315) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8315))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8315)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8315) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8315))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8315)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8316 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8316) = g32p_row31_cosetRepresentatives 8316 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8316) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8316))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8316)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8316) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8316))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8316)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8317 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8317) = g32p_row31_cosetRepresentatives 8317 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8317) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8317))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8317)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8317) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8317))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8317)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8318 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8318) = g32p_row31_cosetRepresentatives 8318 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8318) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8318))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8318)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8318) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8318))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8318)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8319 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8319) = g32p_row31_cosetRepresentatives 8319 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8319) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8319))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8319)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8319) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8319))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8319)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0519 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 519 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 519 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8304
  · exact g32p_row31_cosetWord_8305
  · exact g32p_row31_cosetWord_8306
  · exact g32p_row31_cosetWord_8307
  · exact g32p_row31_cosetWord_8308
  · exact g32p_row31_cosetWord_8309
  · exact g32p_row31_cosetWord_8310
  · exact g32p_row31_cosetWord_8311
  · exact g32p_row31_cosetWord_8312
  · exact g32p_row31_cosetWord_8313
  · exact g32p_row31_cosetWord_8314
  · exact g32p_row31_cosetWord_8315
  · exact g32p_row31_cosetWord_8316
  · exact g32p_row31_cosetWord_8317
  · exact g32p_row31_cosetWord_8318
  · exact g32p_row31_cosetWord_8319

theorem g32p_row31_cosetGeneratorBlock_0519 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 519 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 519 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 519 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8304 s
  · exact g32p_row31_cosetGeneratorStep_8305 s
  · exact g32p_row31_cosetGeneratorStep_8306 s
  · exact g32p_row31_cosetGeneratorStep_8307 s
  · exact g32p_row31_cosetGeneratorStep_8308 s
  · exact g32p_row31_cosetGeneratorStep_8309 s
  · exact g32p_row31_cosetGeneratorStep_8310 s
  · exact g32p_row31_cosetGeneratorStep_8311 s
  · exact g32p_row31_cosetGeneratorStep_8312 s
  · exact g32p_row31_cosetGeneratorStep_8313 s
  · exact g32p_row31_cosetGeneratorStep_8314 s
  · exact g32p_row31_cosetGeneratorStep_8315 s
  · exact g32p_row31_cosetGeneratorStep_8316 s
  · exact g32p_row31_cosetGeneratorStep_8317 s
  · exact g32p_row31_cosetGeneratorStep_8318 s
  · exact g32p_row31_cosetGeneratorStep_8319 s

theorem g32p_row31_cosetBranchBlock_0519 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 519 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 519 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 519 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8304 s
  · exact g32p_row31_cosetBranchStep_8305 s
  · exact g32p_row31_cosetBranchStep_8306 s
  · exact g32p_row31_cosetBranchStep_8307 s
  · exact g32p_row31_cosetBranchStep_8308 s
  · exact g32p_row31_cosetBranchStep_8309 s
  · exact g32p_row31_cosetBranchStep_8310 s
  · exact g32p_row31_cosetBranchStep_8311 s
  · exact g32p_row31_cosetBranchStep_8312 s
  · exact g32p_row31_cosetBranchStep_8313 s
  · exact g32p_row31_cosetBranchStep_8314 s
  · exact g32p_row31_cosetBranchStep_8315 s
  · exact g32p_row31_cosetBranchStep_8316 s
  · exact g32p_row31_cosetBranchStep_8317 s
  · exact g32p_row31_cosetBranchStep_8318 s
  · exact g32p_row31_cosetBranchStep_8319 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8320 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8320) = g32p_row31_cosetRepresentatives 8320 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8320) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8320))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8320)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8320) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8320))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8320)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8321 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8321) = g32p_row31_cosetRepresentatives 8321 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8321) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8321))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8321)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8321) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8321))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8321)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8322 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8322) = g32p_row31_cosetRepresentatives 8322 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8322) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8322))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8322)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8322) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8322))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8322)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8323 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8323) = g32p_row31_cosetRepresentatives 8323 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8323) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8323))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8323)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8323) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8323))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8323)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8324 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8324) = g32p_row31_cosetRepresentatives 8324 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8324) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8324))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8324)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8324) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8324))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8324)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8325 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8325) = g32p_row31_cosetRepresentatives 8325 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8325) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8325))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8325)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8325) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8325))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8325)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8326 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8326) = g32p_row31_cosetRepresentatives 8326 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8326) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8326))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8326)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8326) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8326))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8326)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8327 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8327) = g32p_row31_cosetRepresentatives 8327 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8327) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8327))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8327)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8327) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8327))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8327)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8328 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8328) = g32p_row31_cosetRepresentatives 8328 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8328 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8328) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8328))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8328)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8328 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8328) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8328))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8328)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8329 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8329) = g32p_row31_cosetRepresentatives 8329 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8329 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8329) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8329))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8329)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8329 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8329) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8329))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8329)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8330 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8330) = g32p_row31_cosetRepresentatives 8330 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8330 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8330) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8330))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8330)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8330 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8330) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8330))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8330)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8331 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8331) = g32p_row31_cosetRepresentatives 8331 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8331 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8331) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8331))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8331)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8331 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8331) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8331))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8331)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8332 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8332) = g32p_row31_cosetRepresentatives 8332 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8332 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8332) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8332))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8332)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8332 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8332) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8332))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8332)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8333 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8333) = g32p_row31_cosetRepresentatives 8333 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8333 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8333) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8333))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8333)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8333 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8333) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8333))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8333)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8334 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8334) = g32p_row31_cosetRepresentatives 8334 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8334 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8334) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8334))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8334)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8334 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8334) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8334))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8334)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8335 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8335) = g32p_row31_cosetRepresentatives 8335 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8335 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8335) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8335))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8335)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8335 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8335) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8335))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8335)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0520 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 520 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 520 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8320
  · exact g32p_row31_cosetWord_8321
  · exact g32p_row31_cosetWord_8322
  · exact g32p_row31_cosetWord_8323
  · exact g32p_row31_cosetWord_8324
  · exact g32p_row31_cosetWord_8325
  · exact g32p_row31_cosetWord_8326
  · exact g32p_row31_cosetWord_8327
  · exact g32p_row31_cosetWord_8328
  · exact g32p_row31_cosetWord_8329
  · exact g32p_row31_cosetWord_8330
  · exact g32p_row31_cosetWord_8331
  · exact g32p_row31_cosetWord_8332
  · exact g32p_row31_cosetWord_8333
  · exact g32p_row31_cosetWord_8334
  · exact g32p_row31_cosetWord_8335

theorem g32p_row31_cosetGeneratorBlock_0520 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 520 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 520 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 520 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8320 s
  · exact g32p_row31_cosetGeneratorStep_8321 s
  · exact g32p_row31_cosetGeneratorStep_8322 s
  · exact g32p_row31_cosetGeneratorStep_8323 s
  · exact g32p_row31_cosetGeneratorStep_8324 s
  · exact g32p_row31_cosetGeneratorStep_8325 s
  · exact g32p_row31_cosetGeneratorStep_8326 s
  · exact g32p_row31_cosetGeneratorStep_8327 s
  · exact g32p_row31_cosetGeneratorStep_8328 s
  · exact g32p_row31_cosetGeneratorStep_8329 s
  · exact g32p_row31_cosetGeneratorStep_8330 s
  · exact g32p_row31_cosetGeneratorStep_8331 s
  · exact g32p_row31_cosetGeneratorStep_8332 s
  · exact g32p_row31_cosetGeneratorStep_8333 s
  · exact g32p_row31_cosetGeneratorStep_8334 s
  · exact g32p_row31_cosetGeneratorStep_8335 s

theorem g32p_row31_cosetBranchBlock_0520 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 520 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 520 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 520 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8320 s
  · exact g32p_row31_cosetBranchStep_8321 s
  · exact g32p_row31_cosetBranchStep_8322 s
  · exact g32p_row31_cosetBranchStep_8323 s
  · exact g32p_row31_cosetBranchStep_8324 s
  · exact g32p_row31_cosetBranchStep_8325 s
  · exact g32p_row31_cosetBranchStep_8326 s
  · exact g32p_row31_cosetBranchStep_8327 s
  · exact g32p_row31_cosetBranchStep_8328 s
  · exact g32p_row31_cosetBranchStep_8329 s
  · exact g32p_row31_cosetBranchStep_8330 s
  · exact g32p_row31_cosetBranchStep_8331 s
  · exact g32p_row31_cosetBranchStep_8332 s
  · exact g32p_row31_cosetBranchStep_8333 s
  · exact g32p_row31_cosetBranchStep_8334 s
  · exact g32p_row31_cosetBranchStep_8335 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8336 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8336) = g32p_row31_cosetRepresentatives 8336 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8336 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8336) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8336))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8336)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8336 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8336) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8336))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8336)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8337 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8337) = g32p_row31_cosetRepresentatives 8337 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8337 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8337) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8337))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8337)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8337 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8337) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8337))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8337)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8338 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8338) = g32p_row31_cosetRepresentatives 8338 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8338 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8338) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8338))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8338)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8338 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8338) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8338))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8338)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8339 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8339) = g32p_row31_cosetRepresentatives 8339 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8339 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8339) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8339))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8339)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8339 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8339) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8339))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8339)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8340 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8340) = g32p_row31_cosetRepresentatives 8340 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8340 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8340) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8340))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8340)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8340 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8340) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8340))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8340)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8341 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8341) = g32p_row31_cosetRepresentatives 8341 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8341 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8341) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8341))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8341)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8341 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8341) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8341))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8341)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8342 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8342) = g32p_row31_cosetRepresentatives 8342 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8342 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8342) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8342))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8342)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8342 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8342) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8342))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8342)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8343 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8343) = g32p_row31_cosetRepresentatives 8343 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8343 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8343) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8343))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8343)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8343 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8343) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8343))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8343)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8344 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8344) = g32p_row31_cosetRepresentatives 8344 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8344 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8344) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8344))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8344)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8344 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8344) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8344))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8344)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8345 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8345) = g32p_row31_cosetRepresentatives 8345 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8345 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8345) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8345))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8345)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8345 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8345) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8345))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8345)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8346 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8346) = g32p_row31_cosetRepresentatives 8346 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8346 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8346) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8346))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8346)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8346 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8346) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8346))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8346)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8347 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8347) = g32p_row31_cosetRepresentatives 8347 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8347 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8347) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8347))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8347)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8347 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8347) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8347))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8347)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8348 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8348) = g32p_row31_cosetRepresentatives 8348 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8348 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8348) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8348))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8348)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8348 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8348) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8348))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8348)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8349 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8349) = g32p_row31_cosetRepresentatives 8349 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8349 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8349) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8349))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8349)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8349 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8349) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8349))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8349)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8350 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8350) = g32p_row31_cosetRepresentatives 8350 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8350 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8350) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8350))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8350)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8350 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8350) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8350))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8350)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8351 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8351) = g32p_row31_cosetRepresentatives 8351 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8351 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8351) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8351))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8351)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8351 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8351) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8351))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8351)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0521 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 521 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 521 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8336
  · exact g32p_row31_cosetWord_8337
  · exact g32p_row31_cosetWord_8338
  · exact g32p_row31_cosetWord_8339
  · exact g32p_row31_cosetWord_8340
  · exact g32p_row31_cosetWord_8341
  · exact g32p_row31_cosetWord_8342
  · exact g32p_row31_cosetWord_8343
  · exact g32p_row31_cosetWord_8344
  · exact g32p_row31_cosetWord_8345
  · exact g32p_row31_cosetWord_8346
  · exact g32p_row31_cosetWord_8347
  · exact g32p_row31_cosetWord_8348
  · exact g32p_row31_cosetWord_8349
  · exact g32p_row31_cosetWord_8350
  · exact g32p_row31_cosetWord_8351

theorem g32p_row31_cosetGeneratorBlock_0521 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 521 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 521 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 521 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8336 s
  · exact g32p_row31_cosetGeneratorStep_8337 s
  · exact g32p_row31_cosetGeneratorStep_8338 s
  · exact g32p_row31_cosetGeneratorStep_8339 s
  · exact g32p_row31_cosetGeneratorStep_8340 s
  · exact g32p_row31_cosetGeneratorStep_8341 s
  · exact g32p_row31_cosetGeneratorStep_8342 s
  · exact g32p_row31_cosetGeneratorStep_8343 s
  · exact g32p_row31_cosetGeneratorStep_8344 s
  · exact g32p_row31_cosetGeneratorStep_8345 s
  · exact g32p_row31_cosetGeneratorStep_8346 s
  · exact g32p_row31_cosetGeneratorStep_8347 s
  · exact g32p_row31_cosetGeneratorStep_8348 s
  · exact g32p_row31_cosetGeneratorStep_8349 s
  · exact g32p_row31_cosetGeneratorStep_8350 s
  · exact g32p_row31_cosetGeneratorStep_8351 s

theorem g32p_row31_cosetBranchBlock_0521 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 521 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 521 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 521 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8336 s
  · exact g32p_row31_cosetBranchStep_8337 s
  · exact g32p_row31_cosetBranchStep_8338 s
  · exact g32p_row31_cosetBranchStep_8339 s
  · exact g32p_row31_cosetBranchStep_8340 s
  · exact g32p_row31_cosetBranchStep_8341 s
  · exact g32p_row31_cosetBranchStep_8342 s
  · exact g32p_row31_cosetBranchStep_8343 s
  · exact g32p_row31_cosetBranchStep_8344 s
  · exact g32p_row31_cosetBranchStep_8345 s
  · exact g32p_row31_cosetBranchStep_8346 s
  · exact g32p_row31_cosetBranchStep_8347 s
  · exact g32p_row31_cosetBranchStep_8348 s
  · exact g32p_row31_cosetBranchStep_8349 s
  · exact g32p_row31_cosetBranchStep_8350 s
  · exact g32p_row31_cosetBranchStep_8351 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8352 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8352) = g32p_row31_cosetRepresentatives 8352 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8352 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8352) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8352))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8352)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8352 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8352) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8352))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8352)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8353 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8353) = g32p_row31_cosetRepresentatives 8353 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8353 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8353) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8353))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8353)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8353 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8353) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8353))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8353)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8354 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8354) = g32p_row31_cosetRepresentatives 8354 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8354 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8354) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8354))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8354)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8354 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8354) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8354))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8354)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8355 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8355) = g32p_row31_cosetRepresentatives 8355 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8355 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8355) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8355))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8355)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8355 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8355) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8355))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8355)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8356 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8356) = g32p_row31_cosetRepresentatives 8356 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8356 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8356) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8356))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8356)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8356 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8356) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8356))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8356)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8357 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8357) = g32p_row31_cosetRepresentatives 8357 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8357 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8357) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8357))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8357)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8357 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8357) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8357))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8357)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8358 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8358) = g32p_row31_cosetRepresentatives 8358 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8358 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8358) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8358))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8358)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8358 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8358) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8358))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8358)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8359 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8359) = g32p_row31_cosetRepresentatives 8359 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8359 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8359) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8359))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8359)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8359 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8359) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8359))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8359)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8360 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8360) = g32p_row31_cosetRepresentatives 8360 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8360 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8360) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8360))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8360)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8360 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8360) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8360))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8360)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8361 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8361) = g32p_row31_cosetRepresentatives 8361 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8361 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8361) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8361))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8361)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8361 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8361) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8361))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8361)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8362 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8362) = g32p_row31_cosetRepresentatives 8362 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8362 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8362) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8362))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8362)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8362 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8362) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8362))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8362)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8363 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8363) = g32p_row31_cosetRepresentatives 8363 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8363 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8363) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8363))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8363)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8363 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8363) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8363))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8363)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8364 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8364) = g32p_row31_cosetRepresentatives 8364 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8364 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8364) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8364))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8364)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8364 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8364) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8364))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8364)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8365 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8365) = g32p_row31_cosetRepresentatives 8365 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8365 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8365) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8365))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8365)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8365 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8365) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8365))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8365)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8366 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8366) = g32p_row31_cosetRepresentatives 8366 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8366 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8366) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8366))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8366)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8366 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8366) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8366))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8366)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8367 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8367) = g32p_row31_cosetRepresentatives 8367 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8367 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8367) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8367))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8367)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8367 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8367) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8367))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8367)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0522 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 522 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 522 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8352
  · exact g32p_row31_cosetWord_8353
  · exact g32p_row31_cosetWord_8354
  · exact g32p_row31_cosetWord_8355
  · exact g32p_row31_cosetWord_8356
  · exact g32p_row31_cosetWord_8357
  · exact g32p_row31_cosetWord_8358
  · exact g32p_row31_cosetWord_8359
  · exact g32p_row31_cosetWord_8360
  · exact g32p_row31_cosetWord_8361
  · exact g32p_row31_cosetWord_8362
  · exact g32p_row31_cosetWord_8363
  · exact g32p_row31_cosetWord_8364
  · exact g32p_row31_cosetWord_8365
  · exact g32p_row31_cosetWord_8366
  · exact g32p_row31_cosetWord_8367

theorem g32p_row31_cosetGeneratorBlock_0522 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 522 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 522 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 522 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8352 s
  · exact g32p_row31_cosetGeneratorStep_8353 s
  · exact g32p_row31_cosetGeneratorStep_8354 s
  · exact g32p_row31_cosetGeneratorStep_8355 s
  · exact g32p_row31_cosetGeneratorStep_8356 s
  · exact g32p_row31_cosetGeneratorStep_8357 s
  · exact g32p_row31_cosetGeneratorStep_8358 s
  · exact g32p_row31_cosetGeneratorStep_8359 s
  · exact g32p_row31_cosetGeneratorStep_8360 s
  · exact g32p_row31_cosetGeneratorStep_8361 s
  · exact g32p_row31_cosetGeneratorStep_8362 s
  · exact g32p_row31_cosetGeneratorStep_8363 s
  · exact g32p_row31_cosetGeneratorStep_8364 s
  · exact g32p_row31_cosetGeneratorStep_8365 s
  · exact g32p_row31_cosetGeneratorStep_8366 s
  · exact g32p_row31_cosetGeneratorStep_8367 s

theorem g32p_row31_cosetBranchBlock_0522 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 522 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 522 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 522 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8352 s
  · exact g32p_row31_cosetBranchStep_8353 s
  · exact g32p_row31_cosetBranchStep_8354 s
  · exact g32p_row31_cosetBranchStep_8355 s
  · exact g32p_row31_cosetBranchStep_8356 s
  · exact g32p_row31_cosetBranchStep_8357 s
  · exact g32p_row31_cosetBranchStep_8358 s
  · exact g32p_row31_cosetBranchStep_8359 s
  · exact g32p_row31_cosetBranchStep_8360 s
  · exact g32p_row31_cosetBranchStep_8361 s
  · exact g32p_row31_cosetBranchStep_8362 s
  · exact g32p_row31_cosetBranchStep_8363 s
  · exact g32p_row31_cosetBranchStep_8364 s
  · exact g32p_row31_cosetBranchStep_8365 s
  · exact g32p_row31_cosetBranchStep_8366 s
  · exact g32p_row31_cosetBranchStep_8367 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8368 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8368) = g32p_row31_cosetRepresentatives 8368 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8368 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8368) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8368))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8368)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8368 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8368) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8368))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8368)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8369 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8369) = g32p_row31_cosetRepresentatives 8369 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8369 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8369) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8369))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8369)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8369 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8369) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8369))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8369)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8370 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8370) = g32p_row31_cosetRepresentatives 8370 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8370 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8370) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8370))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8370)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8370 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8370) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8370))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8370)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8371 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8371) = g32p_row31_cosetRepresentatives 8371 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8371 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8371) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8371))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8371)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8371 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8371) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8371))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8371)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8372 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8372) = g32p_row31_cosetRepresentatives 8372 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8372 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8372) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8372))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8372)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8372 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8372) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8372))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8372)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8373 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8373) = g32p_row31_cosetRepresentatives 8373 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8373 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8373) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8373))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8373)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8373 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8373) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8373))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8373)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8374 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8374) = g32p_row31_cosetRepresentatives 8374 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8374 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8374) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8374))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8374)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8374 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8374) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8374))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8374)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8375 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8375) = g32p_row31_cosetRepresentatives 8375 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8375 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8375) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8375))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8375)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8375 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8375) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8375))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8375)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8376 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8376) = g32p_row31_cosetRepresentatives 8376 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8376 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8376) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8376))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8376)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8376 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8376) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8376))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8376)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8377 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8377) = g32p_row31_cosetRepresentatives 8377 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8377 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8377) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8377))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8377)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8377 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8377) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8377))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8377)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8378 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8378) = g32p_row31_cosetRepresentatives 8378 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8378 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8378) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8378))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8378)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8378 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8378) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8378))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8378)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8379 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8379) = g32p_row31_cosetRepresentatives 8379 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8379 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8379) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8379))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8379)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8379 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8379) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8379))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8379)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8380 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8380) = g32p_row31_cosetRepresentatives 8380 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8380 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8380) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8380))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8380)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8380 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8380) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8380))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8380)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8381 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8381) = g32p_row31_cosetRepresentatives 8381 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8381 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8381) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8381))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8381)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8381 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8381) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8381))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8381)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8382 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8382) = g32p_row31_cosetRepresentatives 8382 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8382 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8382) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8382))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8382)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8382 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8382) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8382))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8382)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8383 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8383) = g32p_row31_cosetRepresentatives 8383 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8383 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8383) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8383))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8383)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8383 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8383) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8383))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8383)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0523 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 523 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 523 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8368
  · exact g32p_row31_cosetWord_8369
  · exact g32p_row31_cosetWord_8370
  · exact g32p_row31_cosetWord_8371
  · exact g32p_row31_cosetWord_8372
  · exact g32p_row31_cosetWord_8373
  · exact g32p_row31_cosetWord_8374
  · exact g32p_row31_cosetWord_8375
  · exact g32p_row31_cosetWord_8376
  · exact g32p_row31_cosetWord_8377
  · exact g32p_row31_cosetWord_8378
  · exact g32p_row31_cosetWord_8379
  · exact g32p_row31_cosetWord_8380
  · exact g32p_row31_cosetWord_8381
  · exact g32p_row31_cosetWord_8382
  · exact g32p_row31_cosetWord_8383

theorem g32p_row31_cosetGeneratorBlock_0523 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 523 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 523 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 523 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8368 s
  · exact g32p_row31_cosetGeneratorStep_8369 s
  · exact g32p_row31_cosetGeneratorStep_8370 s
  · exact g32p_row31_cosetGeneratorStep_8371 s
  · exact g32p_row31_cosetGeneratorStep_8372 s
  · exact g32p_row31_cosetGeneratorStep_8373 s
  · exact g32p_row31_cosetGeneratorStep_8374 s
  · exact g32p_row31_cosetGeneratorStep_8375 s
  · exact g32p_row31_cosetGeneratorStep_8376 s
  · exact g32p_row31_cosetGeneratorStep_8377 s
  · exact g32p_row31_cosetGeneratorStep_8378 s
  · exact g32p_row31_cosetGeneratorStep_8379 s
  · exact g32p_row31_cosetGeneratorStep_8380 s
  · exact g32p_row31_cosetGeneratorStep_8381 s
  · exact g32p_row31_cosetGeneratorStep_8382 s
  · exact g32p_row31_cosetGeneratorStep_8383 s

theorem g32p_row31_cosetBranchBlock_0523 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 523 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 523 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 523 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8368 s
  · exact g32p_row31_cosetBranchStep_8369 s
  · exact g32p_row31_cosetBranchStep_8370 s
  · exact g32p_row31_cosetBranchStep_8371 s
  · exact g32p_row31_cosetBranchStep_8372 s
  · exact g32p_row31_cosetBranchStep_8373 s
  · exact g32p_row31_cosetBranchStep_8374 s
  · exact g32p_row31_cosetBranchStep_8375 s
  · exact g32p_row31_cosetBranchStep_8376 s
  · exact g32p_row31_cosetBranchStep_8377 s
  · exact g32p_row31_cosetBranchStep_8378 s
  · exact g32p_row31_cosetBranchStep_8379 s
  · exact g32p_row31_cosetBranchStep_8380 s
  · exact g32p_row31_cosetBranchStep_8381 s
  · exact g32p_row31_cosetBranchStep_8382 s
  · exact g32p_row31_cosetBranchStep_8383 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8384 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8384) = g32p_row31_cosetRepresentatives 8384 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8384 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8384) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8384))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8384)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8384 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8384) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8384))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8384)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8385 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8385) = g32p_row31_cosetRepresentatives 8385 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8385 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8385) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8385))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8385)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8385 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8385) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8385))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8385)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8386 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8386) = g32p_row31_cosetRepresentatives 8386 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8386 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8386) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8386))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8386)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8386 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8386) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8386))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8386)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8387 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8387) = g32p_row31_cosetRepresentatives 8387 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8387 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8387) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8387))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8387)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8387 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8387) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8387))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8387)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8388 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8388) = g32p_row31_cosetRepresentatives 8388 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8388 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8388) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8388))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8388)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8388 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8388) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8388))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8388)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8389 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8389) = g32p_row31_cosetRepresentatives 8389 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8389 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8389) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8389))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8389)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8389 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8389) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8389))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8389)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8390 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8390) = g32p_row31_cosetRepresentatives 8390 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8390 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8390) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8390))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8390)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8390 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8390) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8390))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8390)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8391 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8391) = g32p_row31_cosetRepresentatives 8391 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8391 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8391) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8391))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8391)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8391 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8391) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8391))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8391)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8392 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8392) = g32p_row31_cosetRepresentatives 8392 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8392 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8392) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8392))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8392)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8392 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8392) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8392))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8392)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8393 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8393) = g32p_row31_cosetRepresentatives 8393 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8393 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8393) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8393))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8393)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8393 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8393) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8393))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8393)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8394 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8394) = g32p_row31_cosetRepresentatives 8394 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8394 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8394) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8394))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8394)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8394 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8394) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8394))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8394)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8395 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8395) = g32p_row31_cosetRepresentatives 8395 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8395 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8395) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8395))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8395)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8395 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8395) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8395))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8395)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8396 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8396) = g32p_row31_cosetRepresentatives 8396 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8396 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8396) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8396))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8396)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8396 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8396) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8396))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8396)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8397 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8397) = g32p_row31_cosetRepresentatives 8397 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8397 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8397) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8397))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8397)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8397 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8397) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8397))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8397)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8398 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8398) = g32p_row31_cosetRepresentatives 8398 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8398 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8398) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8398))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8398)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8398 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8398) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8398))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8398)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8399 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8399) = g32p_row31_cosetRepresentatives 8399 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8399 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8399) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8399))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8399)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8399 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8399) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8399))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8399)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0524 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 524 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 524 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8384
  · exact g32p_row31_cosetWord_8385
  · exact g32p_row31_cosetWord_8386
  · exact g32p_row31_cosetWord_8387
  · exact g32p_row31_cosetWord_8388
  · exact g32p_row31_cosetWord_8389
  · exact g32p_row31_cosetWord_8390
  · exact g32p_row31_cosetWord_8391
  · exact g32p_row31_cosetWord_8392
  · exact g32p_row31_cosetWord_8393
  · exact g32p_row31_cosetWord_8394
  · exact g32p_row31_cosetWord_8395
  · exact g32p_row31_cosetWord_8396
  · exact g32p_row31_cosetWord_8397
  · exact g32p_row31_cosetWord_8398
  · exact g32p_row31_cosetWord_8399

theorem g32p_row31_cosetGeneratorBlock_0524 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 524 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 524 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 524 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8384 s
  · exact g32p_row31_cosetGeneratorStep_8385 s
  · exact g32p_row31_cosetGeneratorStep_8386 s
  · exact g32p_row31_cosetGeneratorStep_8387 s
  · exact g32p_row31_cosetGeneratorStep_8388 s
  · exact g32p_row31_cosetGeneratorStep_8389 s
  · exact g32p_row31_cosetGeneratorStep_8390 s
  · exact g32p_row31_cosetGeneratorStep_8391 s
  · exact g32p_row31_cosetGeneratorStep_8392 s
  · exact g32p_row31_cosetGeneratorStep_8393 s
  · exact g32p_row31_cosetGeneratorStep_8394 s
  · exact g32p_row31_cosetGeneratorStep_8395 s
  · exact g32p_row31_cosetGeneratorStep_8396 s
  · exact g32p_row31_cosetGeneratorStep_8397 s
  · exact g32p_row31_cosetGeneratorStep_8398 s
  · exact g32p_row31_cosetGeneratorStep_8399 s

theorem g32p_row31_cosetBranchBlock_0524 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 524 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 524 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 524 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8384 s
  · exact g32p_row31_cosetBranchStep_8385 s
  · exact g32p_row31_cosetBranchStep_8386 s
  · exact g32p_row31_cosetBranchStep_8387 s
  · exact g32p_row31_cosetBranchStep_8388 s
  · exact g32p_row31_cosetBranchStep_8389 s
  · exact g32p_row31_cosetBranchStep_8390 s
  · exact g32p_row31_cosetBranchStep_8391 s
  · exact g32p_row31_cosetBranchStep_8392 s
  · exact g32p_row31_cosetBranchStep_8393 s
  · exact g32p_row31_cosetBranchStep_8394 s
  · exact g32p_row31_cosetBranchStep_8395 s
  · exact g32p_row31_cosetBranchStep_8396 s
  · exact g32p_row31_cosetBranchStep_8397 s
  · exact g32p_row31_cosetBranchStep_8398 s
  · exact g32p_row31_cosetBranchStep_8399 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8400 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8400) = g32p_row31_cosetRepresentatives 8400 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8400 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8400) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8400))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8400)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8400 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8400) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8400))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8400)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8401 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8401) = g32p_row31_cosetRepresentatives 8401 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8401 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8401) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8401))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8401)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8401 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8401) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8401))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8401)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8402 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8402) = g32p_row31_cosetRepresentatives 8402 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8402 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8402) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8402))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8402)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8402 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8402) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8402))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8402)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8403 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8403) = g32p_row31_cosetRepresentatives 8403 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8403 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8403) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8403))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8403)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8403 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8403) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8403))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8403)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8404 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8404) = g32p_row31_cosetRepresentatives 8404 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8404 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8404) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8404))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8404)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8404 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8404) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8404))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8404)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8405 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8405) = g32p_row31_cosetRepresentatives 8405 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8405 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8405) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8405))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8405)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8405 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8405) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8405))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8405)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8406 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8406) = g32p_row31_cosetRepresentatives 8406 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8406 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8406) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8406))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8406)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8406 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8406) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8406))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8406)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8407 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8407) = g32p_row31_cosetRepresentatives 8407 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8407 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8407) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8407))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8407)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8407 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8407) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8407))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8407)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8408 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8408) = g32p_row31_cosetRepresentatives 8408 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8408 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8408) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8408))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8408)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8408 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8408) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8408))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8408)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8409 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8409) = g32p_row31_cosetRepresentatives 8409 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8409 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8409) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8409))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8409)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8409 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8409) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8409))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8409)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8410 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8410) = g32p_row31_cosetRepresentatives 8410 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8410 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8410) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8410))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8410)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8410 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8410) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8410))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8410)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8411 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8411) = g32p_row31_cosetRepresentatives 8411 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8411 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8411) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8411))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8411)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8411 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8411) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8411))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8411)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8412 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8412) = g32p_row31_cosetRepresentatives 8412 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8412 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8412) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8412))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8412)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8412 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8412) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8412))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8412)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8413 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8413) = g32p_row31_cosetRepresentatives 8413 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8413 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8413) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8413))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8413)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8413 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8413) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8413))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8413)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8414 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8414) = g32p_row31_cosetRepresentatives 8414 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8414 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8414) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8414))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8414)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8414 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8414) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8414))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8414)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8415 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8415) = g32p_row31_cosetRepresentatives 8415 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8415 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8415) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8415))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8415)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8415 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8415) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8415))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8415)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0525 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 525 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 525 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8400
  · exact g32p_row31_cosetWord_8401
  · exact g32p_row31_cosetWord_8402
  · exact g32p_row31_cosetWord_8403
  · exact g32p_row31_cosetWord_8404
  · exact g32p_row31_cosetWord_8405
  · exact g32p_row31_cosetWord_8406
  · exact g32p_row31_cosetWord_8407
  · exact g32p_row31_cosetWord_8408
  · exact g32p_row31_cosetWord_8409
  · exact g32p_row31_cosetWord_8410
  · exact g32p_row31_cosetWord_8411
  · exact g32p_row31_cosetWord_8412
  · exact g32p_row31_cosetWord_8413
  · exact g32p_row31_cosetWord_8414
  · exact g32p_row31_cosetWord_8415

theorem g32p_row31_cosetGeneratorBlock_0525 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 525 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 525 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 525 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8400 s
  · exact g32p_row31_cosetGeneratorStep_8401 s
  · exact g32p_row31_cosetGeneratorStep_8402 s
  · exact g32p_row31_cosetGeneratorStep_8403 s
  · exact g32p_row31_cosetGeneratorStep_8404 s
  · exact g32p_row31_cosetGeneratorStep_8405 s
  · exact g32p_row31_cosetGeneratorStep_8406 s
  · exact g32p_row31_cosetGeneratorStep_8407 s
  · exact g32p_row31_cosetGeneratorStep_8408 s
  · exact g32p_row31_cosetGeneratorStep_8409 s
  · exact g32p_row31_cosetGeneratorStep_8410 s
  · exact g32p_row31_cosetGeneratorStep_8411 s
  · exact g32p_row31_cosetGeneratorStep_8412 s
  · exact g32p_row31_cosetGeneratorStep_8413 s
  · exact g32p_row31_cosetGeneratorStep_8414 s
  · exact g32p_row31_cosetGeneratorStep_8415 s

theorem g32p_row31_cosetBranchBlock_0525 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 525 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 525 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 525 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8400 s
  · exact g32p_row31_cosetBranchStep_8401 s
  · exact g32p_row31_cosetBranchStep_8402 s
  · exact g32p_row31_cosetBranchStep_8403 s
  · exact g32p_row31_cosetBranchStep_8404 s
  · exact g32p_row31_cosetBranchStep_8405 s
  · exact g32p_row31_cosetBranchStep_8406 s
  · exact g32p_row31_cosetBranchStep_8407 s
  · exact g32p_row31_cosetBranchStep_8408 s
  · exact g32p_row31_cosetBranchStep_8409 s
  · exact g32p_row31_cosetBranchStep_8410 s
  · exact g32p_row31_cosetBranchStep_8411 s
  · exact g32p_row31_cosetBranchStep_8412 s
  · exact g32p_row31_cosetBranchStep_8413 s
  · exact g32p_row31_cosetBranchStep_8414 s
  · exact g32p_row31_cosetBranchStep_8415 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8416 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8416) = g32p_row31_cosetRepresentatives 8416 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8416 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8416) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8416))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8416)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8416 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8416) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8416))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8416)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8417 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8417) = g32p_row31_cosetRepresentatives 8417 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8417 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8417) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8417))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8417)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8417 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8417) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8417))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8417)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8418 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8418) = g32p_row31_cosetRepresentatives 8418 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8418 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8418) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8418))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8418)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8418 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8418) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8418))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8418)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8419 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8419) = g32p_row31_cosetRepresentatives 8419 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8419 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8419) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8419))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8419)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8419 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8419) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8419))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8419)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8420 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8420) = g32p_row31_cosetRepresentatives 8420 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8420 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8420) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8420))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8420)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8420 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8420) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8420))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8420)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8421 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8421) = g32p_row31_cosetRepresentatives 8421 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8421 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8421) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8421))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8421)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8421 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8421) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8421))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8421)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8422 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8422) = g32p_row31_cosetRepresentatives 8422 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8422 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8422) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8422))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8422)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8422 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8422) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8422))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8422)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8423 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8423) = g32p_row31_cosetRepresentatives 8423 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8423 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8423) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8423))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8423)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8423 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8423) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8423))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8423)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8424 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8424) = g32p_row31_cosetRepresentatives 8424 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8424 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8424) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8424))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8424)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8424 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8424) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8424))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8424)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8425 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8425) = g32p_row31_cosetRepresentatives 8425 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8425 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8425) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8425))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8425)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8425 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8425) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8425))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8425)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8426 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8426) = g32p_row31_cosetRepresentatives 8426 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8426 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8426) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8426))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8426)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8426 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8426) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8426))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8426)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8427 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8427) = g32p_row31_cosetRepresentatives 8427 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8427 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8427) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8427))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8427)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8427 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8427) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8427))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8427)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8428 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8428) = g32p_row31_cosetRepresentatives 8428 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8428 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8428) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8428))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8428)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8428 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8428) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8428))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8428)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8429 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8429) = g32p_row31_cosetRepresentatives 8429 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8429 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8429) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8429))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8429)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8429 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8429) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8429))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8429)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8430 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8430) = g32p_row31_cosetRepresentatives 8430 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8430 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8430) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8430))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8430)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8430 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8430) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8430))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8430)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8431 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8431) = g32p_row31_cosetRepresentatives 8431 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8431 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8431) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8431))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8431)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8431 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8431) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8431))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8431)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0526 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 526 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 526 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8416
  · exact g32p_row31_cosetWord_8417
  · exact g32p_row31_cosetWord_8418
  · exact g32p_row31_cosetWord_8419
  · exact g32p_row31_cosetWord_8420
  · exact g32p_row31_cosetWord_8421
  · exact g32p_row31_cosetWord_8422
  · exact g32p_row31_cosetWord_8423
  · exact g32p_row31_cosetWord_8424
  · exact g32p_row31_cosetWord_8425
  · exact g32p_row31_cosetWord_8426
  · exact g32p_row31_cosetWord_8427
  · exact g32p_row31_cosetWord_8428
  · exact g32p_row31_cosetWord_8429
  · exact g32p_row31_cosetWord_8430
  · exact g32p_row31_cosetWord_8431

theorem g32p_row31_cosetGeneratorBlock_0526 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 526 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 526 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 526 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8416 s
  · exact g32p_row31_cosetGeneratorStep_8417 s
  · exact g32p_row31_cosetGeneratorStep_8418 s
  · exact g32p_row31_cosetGeneratorStep_8419 s
  · exact g32p_row31_cosetGeneratorStep_8420 s
  · exact g32p_row31_cosetGeneratorStep_8421 s
  · exact g32p_row31_cosetGeneratorStep_8422 s
  · exact g32p_row31_cosetGeneratorStep_8423 s
  · exact g32p_row31_cosetGeneratorStep_8424 s
  · exact g32p_row31_cosetGeneratorStep_8425 s
  · exact g32p_row31_cosetGeneratorStep_8426 s
  · exact g32p_row31_cosetGeneratorStep_8427 s
  · exact g32p_row31_cosetGeneratorStep_8428 s
  · exact g32p_row31_cosetGeneratorStep_8429 s
  · exact g32p_row31_cosetGeneratorStep_8430 s
  · exact g32p_row31_cosetGeneratorStep_8431 s

theorem g32p_row31_cosetBranchBlock_0526 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 526 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 526 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 526 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8416 s
  · exact g32p_row31_cosetBranchStep_8417 s
  · exact g32p_row31_cosetBranchStep_8418 s
  · exact g32p_row31_cosetBranchStep_8419 s
  · exact g32p_row31_cosetBranchStep_8420 s
  · exact g32p_row31_cosetBranchStep_8421 s
  · exact g32p_row31_cosetBranchStep_8422 s
  · exact g32p_row31_cosetBranchStep_8423 s
  · exact g32p_row31_cosetBranchStep_8424 s
  · exact g32p_row31_cosetBranchStep_8425 s
  · exact g32p_row31_cosetBranchStep_8426 s
  · exact g32p_row31_cosetBranchStep_8427 s
  · exact g32p_row31_cosetBranchStep_8428 s
  · exact g32p_row31_cosetBranchStep_8429 s
  · exact g32p_row31_cosetBranchStep_8430 s
  · exact g32p_row31_cosetBranchStep_8431 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_8432 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8432) = g32p_row31_cosetRepresentatives 8432 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8432 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8432) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8432))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8432)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8432 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8432) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8432))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8432)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8433 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8433) = g32p_row31_cosetRepresentatives 8433 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8433 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8433) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8433))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8433)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8433 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8433) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8433))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8433)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8434 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8434) = g32p_row31_cosetRepresentatives 8434 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8434 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8434) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8434))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8434)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8434 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8434) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8434))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8434)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8435 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8435) = g32p_row31_cosetRepresentatives 8435 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8435 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8435) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8435))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8435)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8435 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8435) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8435))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8435)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8436 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8436) = g32p_row31_cosetRepresentatives 8436 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8436 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8436) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8436))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8436)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8436 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8436) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8436))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8436)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8437 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8437) = g32p_row31_cosetRepresentatives 8437 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8437 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8437) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8437))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8437)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8437 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8437) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8437))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8437)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8438 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8438) = g32p_row31_cosetRepresentatives 8438 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8438 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8438) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8438))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8438)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8438 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8438) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8438))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8438)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8439 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8439) = g32p_row31_cosetRepresentatives 8439 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8439 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8439) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8439))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8439)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8439 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8439) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8439))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8439)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8440 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8440) = g32p_row31_cosetRepresentatives 8440 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8440 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8440) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8440))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8440)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8440 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8440) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8440))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8440)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8441 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8441) = g32p_row31_cosetRepresentatives 8441 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8441 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8441) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8441))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8441)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8441 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8441) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8441))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8441)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8442 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8442) = g32p_row31_cosetRepresentatives 8442 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8442 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8442) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8442))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8442)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8442 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8442) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8442))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8442)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8443 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8443) = g32p_row31_cosetRepresentatives 8443 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8443 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8443) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8443))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8443)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8443 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8443) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8443))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8443)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8444 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8444) = g32p_row31_cosetRepresentatives 8444 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8444 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8444) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8444))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8444)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8444 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8444) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8444))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8444)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8445 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8445) = g32p_row31_cosetRepresentatives 8445 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8445 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8445) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8445))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8445)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8445 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8445) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8445))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8445)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8446 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8446) = g32p_row31_cosetRepresentatives 8446 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8446 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8446) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8446))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8446)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8446 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8446) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8446))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8446)) := by
  decide +kernel

theorem g32p_row31_cosetWord_8447 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 8447) = g32p_row31_cosetRepresentatives 8447 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_8447 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 8447) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 8447))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 8447)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_8447 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 8447) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 8447))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 8447)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0527 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 527 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 527 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_8432
  · exact g32p_row31_cosetWord_8433
  · exact g32p_row31_cosetWord_8434
  · exact g32p_row31_cosetWord_8435
  · exact g32p_row31_cosetWord_8436
  · exact g32p_row31_cosetWord_8437
  · exact g32p_row31_cosetWord_8438
  · exact g32p_row31_cosetWord_8439
  · exact g32p_row31_cosetWord_8440
  · exact g32p_row31_cosetWord_8441
  · exact g32p_row31_cosetWord_8442
  · exact g32p_row31_cosetWord_8443
  · exact g32p_row31_cosetWord_8444
  · exact g32p_row31_cosetWord_8445
  · exact g32p_row31_cosetWord_8446
  · exact g32p_row31_cosetWord_8447

theorem g32p_row31_cosetGeneratorBlock_0527 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 527 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 527 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 527 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_8432 s
  · exact g32p_row31_cosetGeneratorStep_8433 s
  · exact g32p_row31_cosetGeneratorStep_8434 s
  · exact g32p_row31_cosetGeneratorStep_8435 s
  · exact g32p_row31_cosetGeneratorStep_8436 s
  · exact g32p_row31_cosetGeneratorStep_8437 s
  · exact g32p_row31_cosetGeneratorStep_8438 s
  · exact g32p_row31_cosetGeneratorStep_8439 s
  · exact g32p_row31_cosetGeneratorStep_8440 s
  · exact g32p_row31_cosetGeneratorStep_8441 s
  · exact g32p_row31_cosetGeneratorStep_8442 s
  · exact g32p_row31_cosetGeneratorStep_8443 s
  · exact g32p_row31_cosetGeneratorStep_8444 s
  · exact g32p_row31_cosetGeneratorStep_8445 s
  · exact g32p_row31_cosetGeneratorStep_8446 s
  · exact g32p_row31_cosetGeneratorStep_8447 s

theorem g32p_row31_cosetBranchBlock_0527 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 527 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 527 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 527 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_8432 s
  · exact g32p_row31_cosetBranchStep_8433 s
  · exact g32p_row31_cosetBranchStep_8434 s
  · exact g32p_row31_cosetBranchStep_8435 s
  · exact g32p_row31_cosetBranchStep_8436 s
  · exact g32p_row31_cosetBranchStep_8437 s
  · exact g32p_row31_cosetBranchStep_8438 s
  · exact g32p_row31_cosetBranchStep_8439 s
  · exact g32p_row31_cosetBranchStep_8440 s
  · exact g32p_row31_cosetBranchStep_8441 s
  · exact g32p_row31_cosetBranchStep_8442 s
  · exact g32p_row31_cosetBranchStep_8443 s
  · exact g32p_row31_cosetBranchStep_8444 s
  · exact g32p_row31_cosetBranchStep_8445 s
  · exact g32p_row31_cosetBranchStep_8446 s
  · exact g32p_row31_cosetBranchStep_8447 s


end HodgeLean.Foundations.Program

end
