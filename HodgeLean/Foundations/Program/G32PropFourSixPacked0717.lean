import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0704

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3072 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3072) = g32p_row18_cosetRepresentatives 3072 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3072 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3072) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3072))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3072)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3072 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3072) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3072))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3072)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3073 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3073) = g32p_row18_cosetRepresentatives 3073 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3073 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3073) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3073))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3073)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3073 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3073) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3073))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3073)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3074 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3074) = g32p_row18_cosetRepresentatives 3074 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3074 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3074) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3074))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3074)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3074 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3074) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3074))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3074)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3075 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3075) = g32p_row18_cosetRepresentatives 3075 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3075 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3075) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3075))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3075)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3075 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3075) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3075))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3075)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3076 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3076) = g32p_row18_cosetRepresentatives 3076 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3076 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3076) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3076))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3076)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3076 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3076) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3076))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3076)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3077 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3077) = g32p_row18_cosetRepresentatives 3077 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3077 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3077) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3077))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3077)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3077 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3077) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3077))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3077)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3078 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3078) = g32p_row18_cosetRepresentatives 3078 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3078 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3078) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3078))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3078)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3078 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3078) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3078))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3078)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3079 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3079) = g32p_row18_cosetRepresentatives 3079 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3079 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3079) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3079))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3079)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3079 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3079) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3079))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3079)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3080 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3080) = g32p_row18_cosetRepresentatives 3080 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3080 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3080) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3080))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3080)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3080 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3080) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3080))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3080)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3081 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3081) = g32p_row18_cosetRepresentatives 3081 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3081 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3081) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3081))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3081)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3081 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3081) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3081))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3081)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3082 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3082) = g32p_row18_cosetRepresentatives 3082 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3082 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3082) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3082))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3082)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3082 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3082) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3082))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3082)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3083 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3083) = g32p_row18_cosetRepresentatives 3083 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3083 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3083) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3083))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3083)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3083 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3083) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3083))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3083)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3084 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3084) = g32p_row18_cosetRepresentatives 3084 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3084 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3084) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3084))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3084)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3084 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3084) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3084))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3084)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3085 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3085) = g32p_row18_cosetRepresentatives 3085 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3085 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3085) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3085))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3085)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3085 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3085) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3085))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3085)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3086 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3086) = g32p_row18_cosetRepresentatives 3086 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3086 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3086) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3086))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3086)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3086 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3086) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3086))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3086)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3087 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3087) = g32p_row18_cosetRepresentatives 3087 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3087 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3087) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3087))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3087)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3087 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3087) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3087))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3087)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0192 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 192 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 192 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3072
  · exact g32p_row18_cosetWord_3073
  · exact g32p_row18_cosetWord_3074
  · exact g32p_row18_cosetWord_3075
  · exact g32p_row18_cosetWord_3076
  · exact g32p_row18_cosetWord_3077
  · exact g32p_row18_cosetWord_3078
  · exact g32p_row18_cosetWord_3079
  · exact g32p_row18_cosetWord_3080
  · exact g32p_row18_cosetWord_3081
  · exact g32p_row18_cosetWord_3082
  · exact g32p_row18_cosetWord_3083
  · exact g32p_row18_cosetWord_3084
  · exact g32p_row18_cosetWord_3085
  · exact g32p_row18_cosetWord_3086
  · exact g32p_row18_cosetWord_3087

theorem g32p_row18_cosetGeneratorBlock_0192 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 192 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 192 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 192 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3072 s
  · exact g32p_row18_cosetGeneratorStep_3073 s
  · exact g32p_row18_cosetGeneratorStep_3074 s
  · exact g32p_row18_cosetGeneratorStep_3075 s
  · exact g32p_row18_cosetGeneratorStep_3076 s
  · exact g32p_row18_cosetGeneratorStep_3077 s
  · exact g32p_row18_cosetGeneratorStep_3078 s
  · exact g32p_row18_cosetGeneratorStep_3079 s
  · exact g32p_row18_cosetGeneratorStep_3080 s
  · exact g32p_row18_cosetGeneratorStep_3081 s
  · exact g32p_row18_cosetGeneratorStep_3082 s
  · exact g32p_row18_cosetGeneratorStep_3083 s
  · exact g32p_row18_cosetGeneratorStep_3084 s
  · exact g32p_row18_cosetGeneratorStep_3085 s
  · exact g32p_row18_cosetGeneratorStep_3086 s
  · exact g32p_row18_cosetGeneratorStep_3087 s

theorem g32p_row18_cosetBranchBlock_0192 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 192 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 192 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 192 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3072 s
  · exact g32p_row18_cosetBranchStep_3073 s
  · exact g32p_row18_cosetBranchStep_3074 s
  · exact g32p_row18_cosetBranchStep_3075 s
  · exact g32p_row18_cosetBranchStep_3076 s
  · exact g32p_row18_cosetBranchStep_3077 s
  · exact g32p_row18_cosetBranchStep_3078 s
  · exact g32p_row18_cosetBranchStep_3079 s
  · exact g32p_row18_cosetBranchStep_3080 s
  · exact g32p_row18_cosetBranchStep_3081 s
  · exact g32p_row18_cosetBranchStep_3082 s
  · exact g32p_row18_cosetBranchStep_3083 s
  · exact g32p_row18_cosetBranchStep_3084 s
  · exact g32p_row18_cosetBranchStep_3085 s
  · exact g32p_row18_cosetBranchStep_3086 s
  · exact g32p_row18_cosetBranchStep_3087 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3088 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3088) = g32p_row18_cosetRepresentatives 3088 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3088 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3088) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3088))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3088)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3088 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3088) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3088))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3088)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3089 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3089) = g32p_row18_cosetRepresentatives 3089 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3089 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3089) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3089))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3089)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3089 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3089) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3089))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3089)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3090 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3090) = g32p_row18_cosetRepresentatives 3090 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3090 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3090) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3090))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3090)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3090 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3090) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3090))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3090)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3091 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3091) = g32p_row18_cosetRepresentatives 3091 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3091 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3091) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3091))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3091)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3091 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3091) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3091))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3091)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3092 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3092) = g32p_row18_cosetRepresentatives 3092 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3092 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3092) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3092))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3092)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3092 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3092) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3092))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3092)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3093 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3093) = g32p_row18_cosetRepresentatives 3093 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3093 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3093) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3093))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3093)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3093 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3093) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3093))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3093)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3094 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3094) = g32p_row18_cosetRepresentatives 3094 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3094 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3094) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3094))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3094)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3094 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3094) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3094))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3094)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3095 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3095) = g32p_row18_cosetRepresentatives 3095 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3095 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3095) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3095))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3095)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3095 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3095) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3095))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3095)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3096 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3096) = g32p_row18_cosetRepresentatives 3096 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3096 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3096) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3096))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3096)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3096 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3096) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3096))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3096)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3097 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3097) = g32p_row18_cosetRepresentatives 3097 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3097 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3097) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3097))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3097)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3097 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3097) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3097))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3097)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3098 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3098) = g32p_row18_cosetRepresentatives 3098 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3098 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3098) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3098))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3098)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3098 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3098) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3098))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3098)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3099 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3099) = g32p_row18_cosetRepresentatives 3099 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3099 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3099) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3099))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3099)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3099 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3099) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3099))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3099)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3100 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3100) = g32p_row18_cosetRepresentatives 3100 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3100 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3100) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3100))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3100)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3100 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3100) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3100))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3100)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3101 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3101) = g32p_row18_cosetRepresentatives 3101 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3101 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3101) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3101))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3101)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3101 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3101) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3101))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3101)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3102 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3102) = g32p_row18_cosetRepresentatives 3102 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3102 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3102) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3102))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3102)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3102 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3102) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3102))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3102)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3103 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3103) = g32p_row18_cosetRepresentatives 3103 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3103 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3103) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3103))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3103)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3103 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3103) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3103))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3103)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0193 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 193 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 193 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3088
  · exact g32p_row18_cosetWord_3089
  · exact g32p_row18_cosetWord_3090
  · exact g32p_row18_cosetWord_3091
  · exact g32p_row18_cosetWord_3092
  · exact g32p_row18_cosetWord_3093
  · exact g32p_row18_cosetWord_3094
  · exact g32p_row18_cosetWord_3095
  · exact g32p_row18_cosetWord_3096
  · exact g32p_row18_cosetWord_3097
  · exact g32p_row18_cosetWord_3098
  · exact g32p_row18_cosetWord_3099
  · exact g32p_row18_cosetWord_3100
  · exact g32p_row18_cosetWord_3101
  · exact g32p_row18_cosetWord_3102
  · exact g32p_row18_cosetWord_3103

theorem g32p_row18_cosetGeneratorBlock_0193 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 193 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 193 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 193 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3088 s
  · exact g32p_row18_cosetGeneratorStep_3089 s
  · exact g32p_row18_cosetGeneratorStep_3090 s
  · exact g32p_row18_cosetGeneratorStep_3091 s
  · exact g32p_row18_cosetGeneratorStep_3092 s
  · exact g32p_row18_cosetGeneratorStep_3093 s
  · exact g32p_row18_cosetGeneratorStep_3094 s
  · exact g32p_row18_cosetGeneratorStep_3095 s
  · exact g32p_row18_cosetGeneratorStep_3096 s
  · exact g32p_row18_cosetGeneratorStep_3097 s
  · exact g32p_row18_cosetGeneratorStep_3098 s
  · exact g32p_row18_cosetGeneratorStep_3099 s
  · exact g32p_row18_cosetGeneratorStep_3100 s
  · exact g32p_row18_cosetGeneratorStep_3101 s
  · exact g32p_row18_cosetGeneratorStep_3102 s
  · exact g32p_row18_cosetGeneratorStep_3103 s

theorem g32p_row18_cosetBranchBlock_0193 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 193 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 193 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 193 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3088 s
  · exact g32p_row18_cosetBranchStep_3089 s
  · exact g32p_row18_cosetBranchStep_3090 s
  · exact g32p_row18_cosetBranchStep_3091 s
  · exact g32p_row18_cosetBranchStep_3092 s
  · exact g32p_row18_cosetBranchStep_3093 s
  · exact g32p_row18_cosetBranchStep_3094 s
  · exact g32p_row18_cosetBranchStep_3095 s
  · exact g32p_row18_cosetBranchStep_3096 s
  · exact g32p_row18_cosetBranchStep_3097 s
  · exact g32p_row18_cosetBranchStep_3098 s
  · exact g32p_row18_cosetBranchStep_3099 s
  · exact g32p_row18_cosetBranchStep_3100 s
  · exact g32p_row18_cosetBranchStep_3101 s
  · exact g32p_row18_cosetBranchStep_3102 s
  · exact g32p_row18_cosetBranchStep_3103 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3104 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3104) = g32p_row18_cosetRepresentatives 3104 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3104 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3104) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3104))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3104)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3104 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3104) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3104))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3104)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3105 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3105) = g32p_row18_cosetRepresentatives 3105 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3105 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3105) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3105))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3105)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3105 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3105) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3105))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3105)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3106 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3106) = g32p_row18_cosetRepresentatives 3106 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3106 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3106) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3106))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3106)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3106 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3106) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3106))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3106)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3107 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3107) = g32p_row18_cosetRepresentatives 3107 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3107 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3107) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3107))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3107)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3107 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3107) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3107))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3107)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3108 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3108) = g32p_row18_cosetRepresentatives 3108 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3108 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3108) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3108))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3108)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3108 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3108) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3108))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3108)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3109 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3109) = g32p_row18_cosetRepresentatives 3109 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3109 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3109) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3109))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3109)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3109 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3109) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3109))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3109)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3110 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3110) = g32p_row18_cosetRepresentatives 3110 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3110 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3110) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3110))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3110)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3110 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3110) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3110))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3110)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3111 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3111) = g32p_row18_cosetRepresentatives 3111 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3111 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3111) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3111))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3111)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3111 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3111) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3111))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3111)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3112 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3112) = g32p_row18_cosetRepresentatives 3112 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3112 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3112) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3112))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3112)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3112 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3112) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3112))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3112)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3113 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3113) = g32p_row18_cosetRepresentatives 3113 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3113 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3113) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3113))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3113)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3113 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3113) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3113))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3113)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3114 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3114) = g32p_row18_cosetRepresentatives 3114 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3114 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3114) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3114))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3114)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3114 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3114) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3114))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3114)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3115 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3115) = g32p_row18_cosetRepresentatives 3115 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3115 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3115) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3115))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3115)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3115 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3115) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3115))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3115)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3116 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3116) = g32p_row18_cosetRepresentatives 3116 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3116 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3116) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3116))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3116)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3116 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3116) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3116))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3116)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3117 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3117) = g32p_row18_cosetRepresentatives 3117 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3117 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3117) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3117))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3117)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3117 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3117) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3117))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3117)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3118 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3118) = g32p_row18_cosetRepresentatives 3118 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3118 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3118) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3118))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3118)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3118 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3118) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3118))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3118)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3119 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3119) = g32p_row18_cosetRepresentatives 3119 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3119 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3119) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3119))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3119)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3119 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3119) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3119))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3119)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0194 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 194 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 194 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3104
  · exact g32p_row18_cosetWord_3105
  · exact g32p_row18_cosetWord_3106
  · exact g32p_row18_cosetWord_3107
  · exact g32p_row18_cosetWord_3108
  · exact g32p_row18_cosetWord_3109
  · exact g32p_row18_cosetWord_3110
  · exact g32p_row18_cosetWord_3111
  · exact g32p_row18_cosetWord_3112
  · exact g32p_row18_cosetWord_3113
  · exact g32p_row18_cosetWord_3114
  · exact g32p_row18_cosetWord_3115
  · exact g32p_row18_cosetWord_3116
  · exact g32p_row18_cosetWord_3117
  · exact g32p_row18_cosetWord_3118
  · exact g32p_row18_cosetWord_3119

theorem g32p_row18_cosetGeneratorBlock_0194 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 194 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 194 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 194 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3104 s
  · exact g32p_row18_cosetGeneratorStep_3105 s
  · exact g32p_row18_cosetGeneratorStep_3106 s
  · exact g32p_row18_cosetGeneratorStep_3107 s
  · exact g32p_row18_cosetGeneratorStep_3108 s
  · exact g32p_row18_cosetGeneratorStep_3109 s
  · exact g32p_row18_cosetGeneratorStep_3110 s
  · exact g32p_row18_cosetGeneratorStep_3111 s
  · exact g32p_row18_cosetGeneratorStep_3112 s
  · exact g32p_row18_cosetGeneratorStep_3113 s
  · exact g32p_row18_cosetGeneratorStep_3114 s
  · exact g32p_row18_cosetGeneratorStep_3115 s
  · exact g32p_row18_cosetGeneratorStep_3116 s
  · exact g32p_row18_cosetGeneratorStep_3117 s
  · exact g32p_row18_cosetGeneratorStep_3118 s
  · exact g32p_row18_cosetGeneratorStep_3119 s

theorem g32p_row18_cosetBranchBlock_0194 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 194 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 194 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 194 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3104 s
  · exact g32p_row18_cosetBranchStep_3105 s
  · exact g32p_row18_cosetBranchStep_3106 s
  · exact g32p_row18_cosetBranchStep_3107 s
  · exact g32p_row18_cosetBranchStep_3108 s
  · exact g32p_row18_cosetBranchStep_3109 s
  · exact g32p_row18_cosetBranchStep_3110 s
  · exact g32p_row18_cosetBranchStep_3111 s
  · exact g32p_row18_cosetBranchStep_3112 s
  · exact g32p_row18_cosetBranchStep_3113 s
  · exact g32p_row18_cosetBranchStep_3114 s
  · exact g32p_row18_cosetBranchStep_3115 s
  · exact g32p_row18_cosetBranchStep_3116 s
  · exact g32p_row18_cosetBranchStep_3117 s
  · exact g32p_row18_cosetBranchStep_3118 s
  · exact g32p_row18_cosetBranchStep_3119 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3120 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3120) = g32p_row18_cosetRepresentatives 3120 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3120 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3120) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3120))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3120)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3120 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3120) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3120))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3120)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3121 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3121) = g32p_row18_cosetRepresentatives 3121 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3121 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3121) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3121))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3121)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3121 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3121) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3121))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3121)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3122 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3122) = g32p_row18_cosetRepresentatives 3122 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3122 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3122) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3122))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3122)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3122 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3122) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3122))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3122)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3123 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3123) = g32p_row18_cosetRepresentatives 3123 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3123 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3123) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3123))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3123)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3123 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3123) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3123))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3123)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3124 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3124) = g32p_row18_cosetRepresentatives 3124 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3124 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3124) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3124))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3124)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3124 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3124) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3124))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3124)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3125 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3125) = g32p_row18_cosetRepresentatives 3125 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3125 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3125) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3125))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3125)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3125 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3125) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3125))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3125)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3126 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3126) = g32p_row18_cosetRepresentatives 3126 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3126 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3126) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3126))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3126)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3126 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3126) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3126))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3126)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3127 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3127) = g32p_row18_cosetRepresentatives 3127 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3127 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3127) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3127))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3127)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3127 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3127) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3127))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3127)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3128 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3128) = g32p_row18_cosetRepresentatives 3128 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3128 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3128) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3128))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3128)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3128 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3128) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3128))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3128)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3129 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3129) = g32p_row18_cosetRepresentatives 3129 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3129 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3129) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3129))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3129)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3129 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3129) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3129))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3129)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3130 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3130) = g32p_row18_cosetRepresentatives 3130 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3130 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3130) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3130))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3130)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3130 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3130) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3130))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3130)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3131 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3131) = g32p_row18_cosetRepresentatives 3131 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3131 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3131) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3131))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3131)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3131 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3131) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3131))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3131)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3132 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3132) = g32p_row18_cosetRepresentatives 3132 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3132 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3132) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3132))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3132)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3132 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3132) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3132))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3132)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3133 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3133) = g32p_row18_cosetRepresentatives 3133 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3133 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3133) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3133))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3133)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3133 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3133) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3133))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3133)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3134 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3134) = g32p_row18_cosetRepresentatives 3134 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3134 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3134) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3134))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3134)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3134 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3134) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3134))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3134)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3135 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3135) = g32p_row18_cosetRepresentatives 3135 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3135 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3135) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3135))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3135)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3135 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3135) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3135))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3135)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0195 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 195 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 195 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3120
  · exact g32p_row18_cosetWord_3121
  · exact g32p_row18_cosetWord_3122
  · exact g32p_row18_cosetWord_3123
  · exact g32p_row18_cosetWord_3124
  · exact g32p_row18_cosetWord_3125
  · exact g32p_row18_cosetWord_3126
  · exact g32p_row18_cosetWord_3127
  · exact g32p_row18_cosetWord_3128
  · exact g32p_row18_cosetWord_3129
  · exact g32p_row18_cosetWord_3130
  · exact g32p_row18_cosetWord_3131
  · exact g32p_row18_cosetWord_3132
  · exact g32p_row18_cosetWord_3133
  · exact g32p_row18_cosetWord_3134
  · exact g32p_row18_cosetWord_3135

theorem g32p_row18_cosetGeneratorBlock_0195 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 195 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 195 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 195 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3120 s
  · exact g32p_row18_cosetGeneratorStep_3121 s
  · exact g32p_row18_cosetGeneratorStep_3122 s
  · exact g32p_row18_cosetGeneratorStep_3123 s
  · exact g32p_row18_cosetGeneratorStep_3124 s
  · exact g32p_row18_cosetGeneratorStep_3125 s
  · exact g32p_row18_cosetGeneratorStep_3126 s
  · exact g32p_row18_cosetGeneratorStep_3127 s
  · exact g32p_row18_cosetGeneratorStep_3128 s
  · exact g32p_row18_cosetGeneratorStep_3129 s
  · exact g32p_row18_cosetGeneratorStep_3130 s
  · exact g32p_row18_cosetGeneratorStep_3131 s
  · exact g32p_row18_cosetGeneratorStep_3132 s
  · exact g32p_row18_cosetGeneratorStep_3133 s
  · exact g32p_row18_cosetGeneratorStep_3134 s
  · exact g32p_row18_cosetGeneratorStep_3135 s

theorem g32p_row18_cosetBranchBlock_0195 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 195 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 195 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 195 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3120 s
  · exact g32p_row18_cosetBranchStep_3121 s
  · exact g32p_row18_cosetBranchStep_3122 s
  · exact g32p_row18_cosetBranchStep_3123 s
  · exact g32p_row18_cosetBranchStep_3124 s
  · exact g32p_row18_cosetBranchStep_3125 s
  · exact g32p_row18_cosetBranchStep_3126 s
  · exact g32p_row18_cosetBranchStep_3127 s
  · exact g32p_row18_cosetBranchStep_3128 s
  · exact g32p_row18_cosetBranchStep_3129 s
  · exact g32p_row18_cosetBranchStep_3130 s
  · exact g32p_row18_cosetBranchStep_3131 s
  · exact g32p_row18_cosetBranchStep_3132 s
  · exact g32p_row18_cosetBranchStep_3133 s
  · exact g32p_row18_cosetBranchStep_3134 s
  · exact g32p_row18_cosetBranchStep_3135 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3136 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3136) = g32p_row18_cosetRepresentatives 3136 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3136 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3136) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3136))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3136)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3136 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3136) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3136))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3136)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3137 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3137) = g32p_row18_cosetRepresentatives 3137 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3137 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3137) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3137))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3137)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3137 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3137) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3137))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3137)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3138 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3138) = g32p_row18_cosetRepresentatives 3138 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3138 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3138) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3138))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3138)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3138 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3138) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3138))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3138)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3139 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3139) = g32p_row18_cosetRepresentatives 3139 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3139 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3139) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3139))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3139)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3139 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3139) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3139))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3139)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3140 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3140) = g32p_row18_cosetRepresentatives 3140 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3140 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3140) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3140))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3140)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3140 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3140) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3140))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3140)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3141 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3141) = g32p_row18_cosetRepresentatives 3141 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3141 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3141) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3141))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3141)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3141 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3141) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3141))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3141)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3142 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3142) = g32p_row18_cosetRepresentatives 3142 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3142 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3142) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3142))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3142)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3142 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3142) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3142))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3142)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3143 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3143) = g32p_row18_cosetRepresentatives 3143 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3143 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3143) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3143))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3143)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3143 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3143) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3143))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3143)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3144 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3144) = g32p_row18_cosetRepresentatives 3144 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3144 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3144) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3144))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3144)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3144 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3144) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3144))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3144)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3145 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3145) = g32p_row18_cosetRepresentatives 3145 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3145 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3145) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3145))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3145)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3145 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3145) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3145))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3145)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3146 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3146) = g32p_row18_cosetRepresentatives 3146 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3146 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3146) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3146))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3146)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3146 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3146) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3146))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3146)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3147 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3147) = g32p_row18_cosetRepresentatives 3147 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3147 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3147) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3147))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3147)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3147 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3147) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3147))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3147)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3148 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3148) = g32p_row18_cosetRepresentatives 3148 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3148 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3148) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3148))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3148)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3148 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3148) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3148))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3148)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3149 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3149) = g32p_row18_cosetRepresentatives 3149 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3149 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3149) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3149))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3149)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3149 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3149) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3149))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3149)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3150 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3150) = g32p_row18_cosetRepresentatives 3150 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3150 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3150) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3150))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3150)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3150 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3150) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3150))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3150)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3151 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3151) = g32p_row18_cosetRepresentatives 3151 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3151 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3151) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3151))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3151)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3151 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3151) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3151))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3151)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0196 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 196 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 196 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3136
  · exact g32p_row18_cosetWord_3137
  · exact g32p_row18_cosetWord_3138
  · exact g32p_row18_cosetWord_3139
  · exact g32p_row18_cosetWord_3140
  · exact g32p_row18_cosetWord_3141
  · exact g32p_row18_cosetWord_3142
  · exact g32p_row18_cosetWord_3143
  · exact g32p_row18_cosetWord_3144
  · exact g32p_row18_cosetWord_3145
  · exact g32p_row18_cosetWord_3146
  · exact g32p_row18_cosetWord_3147
  · exact g32p_row18_cosetWord_3148
  · exact g32p_row18_cosetWord_3149
  · exact g32p_row18_cosetWord_3150
  · exact g32p_row18_cosetWord_3151

theorem g32p_row18_cosetGeneratorBlock_0196 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 196 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 196 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 196 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3136 s
  · exact g32p_row18_cosetGeneratorStep_3137 s
  · exact g32p_row18_cosetGeneratorStep_3138 s
  · exact g32p_row18_cosetGeneratorStep_3139 s
  · exact g32p_row18_cosetGeneratorStep_3140 s
  · exact g32p_row18_cosetGeneratorStep_3141 s
  · exact g32p_row18_cosetGeneratorStep_3142 s
  · exact g32p_row18_cosetGeneratorStep_3143 s
  · exact g32p_row18_cosetGeneratorStep_3144 s
  · exact g32p_row18_cosetGeneratorStep_3145 s
  · exact g32p_row18_cosetGeneratorStep_3146 s
  · exact g32p_row18_cosetGeneratorStep_3147 s
  · exact g32p_row18_cosetGeneratorStep_3148 s
  · exact g32p_row18_cosetGeneratorStep_3149 s
  · exact g32p_row18_cosetGeneratorStep_3150 s
  · exact g32p_row18_cosetGeneratorStep_3151 s

theorem g32p_row18_cosetBranchBlock_0196 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 196 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 196 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 196 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3136 s
  · exact g32p_row18_cosetBranchStep_3137 s
  · exact g32p_row18_cosetBranchStep_3138 s
  · exact g32p_row18_cosetBranchStep_3139 s
  · exact g32p_row18_cosetBranchStep_3140 s
  · exact g32p_row18_cosetBranchStep_3141 s
  · exact g32p_row18_cosetBranchStep_3142 s
  · exact g32p_row18_cosetBranchStep_3143 s
  · exact g32p_row18_cosetBranchStep_3144 s
  · exact g32p_row18_cosetBranchStep_3145 s
  · exact g32p_row18_cosetBranchStep_3146 s
  · exact g32p_row18_cosetBranchStep_3147 s
  · exact g32p_row18_cosetBranchStep_3148 s
  · exact g32p_row18_cosetBranchStep_3149 s
  · exact g32p_row18_cosetBranchStep_3150 s
  · exact g32p_row18_cosetBranchStep_3151 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3152 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3152) = g32p_row18_cosetRepresentatives 3152 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3152 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3152) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3152))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3152)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3152 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3152) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3152))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3152)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3153 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3153) = g32p_row18_cosetRepresentatives 3153 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3153 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3153) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3153))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3153)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3153 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3153) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3153))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3153)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3154 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3154) = g32p_row18_cosetRepresentatives 3154 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3154 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3154) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3154))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3154)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3154 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3154) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3154))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3154)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3155 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3155) = g32p_row18_cosetRepresentatives 3155 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3155 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3155) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3155))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3155)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3155 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3155) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3155))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3155)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3156 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3156) = g32p_row18_cosetRepresentatives 3156 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3156 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3156) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3156))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3156)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3156 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3156) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3156))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3156)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3157 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3157) = g32p_row18_cosetRepresentatives 3157 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3157 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3157) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3157))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3157)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3157 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3157) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3157))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3157)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3158 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3158) = g32p_row18_cosetRepresentatives 3158 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3158 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3158) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3158))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3158)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3158 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3158) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3158))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3158)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3159 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3159) = g32p_row18_cosetRepresentatives 3159 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3159 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3159) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3159))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3159)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3159 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3159) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3159))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3159)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3160 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3160) = g32p_row18_cosetRepresentatives 3160 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3160 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3160) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3160))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3160)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3160 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3160) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3160))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3160)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3161 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3161) = g32p_row18_cosetRepresentatives 3161 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3161 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3161) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3161))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3161)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3161 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3161) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3161))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3161)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3162 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3162) = g32p_row18_cosetRepresentatives 3162 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3162 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3162) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3162))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3162)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3162 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3162) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3162))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3162)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3163 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3163) = g32p_row18_cosetRepresentatives 3163 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3163 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3163) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3163))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3163)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3163 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3163) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3163))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3163)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3164 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3164) = g32p_row18_cosetRepresentatives 3164 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3164 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3164) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3164))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3164)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3164 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3164) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3164))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3164)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3165 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3165) = g32p_row18_cosetRepresentatives 3165 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3165 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3165) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3165))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3165)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3165 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3165) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3165))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3165)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3166 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3166) = g32p_row18_cosetRepresentatives 3166 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3166 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3166) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3166))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3166)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3166 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3166) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3166))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3166)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3167 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3167) = g32p_row18_cosetRepresentatives 3167 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3167 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3167) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3167))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3167)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3167 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3167) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3167))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3167)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0197 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 197 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 197 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3152
  · exact g32p_row18_cosetWord_3153
  · exact g32p_row18_cosetWord_3154
  · exact g32p_row18_cosetWord_3155
  · exact g32p_row18_cosetWord_3156
  · exact g32p_row18_cosetWord_3157
  · exact g32p_row18_cosetWord_3158
  · exact g32p_row18_cosetWord_3159
  · exact g32p_row18_cosetWord_3160
  · exact g32p_row18_cosetWord_3161
  · exact g32p_row18_cosetWord_3162
  · exact g32p_row18_cosetWord_3163
  · exact g32p_row18_cosetWord_3164
  · exact g32p_row18_cosetWord_3165
  · exact g32p_row18_cosetWord_3166
  · exact g32p_row18_cosetWord_3167

theorem g32p_row18_cosetGeneratorBlock_0197 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 197 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 197 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 197 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3152 s
  · exact g32p_row18_cosetGeneratorStep_3153 s
  · exact g32p_row18_cosetGeneratorStep_3154 s
  · exact g32p_row18_cosetGeneratorStep_3155 s
  · exact g32p_row18_cosetGeneratorStep_3156 s
  · exact g32p_row18_cosetGeneratorStep_3157 s
  · exact g32p_row18_cosetGeneratorStep_3158 s
  · exact g32p_row18_cosetGeneratorStep_3159 s
  · exact g32p_row18_cosetGeneratorStep_3160 s
  · exact g32p_row18_cosetGeneratorStep_3161 s
  · exact g32p_row18_cosetGeneratorStep_3162 s
  · exact g32p_row18_cosetGeneratorStep_3163 s
  · exact g32p_row18_cosetGeneratorStep_3164 s
  · exact g32p_row18_cosetGeneratorStep_3165 s
  · exact g32p_row18_cosetGeneratorStep_3166 s
  · exact g32p_row18_cosetGeneratorStep_3167 s

theorem g32p_row18_cosetBranchBlock_0197 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 197 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 197 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 197 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3152 s
  · exact g32p_row18_cosetBranchStep_3153 s
  · exact g32p_row18_cosetBranchStep_3154 s
  · exact g32p_row18_cosetBranchStep_3155 s
  · exact g32p_row18_cosetBranchStep_3156 s
  · exact g32p_row18_cosetBranchStep_3157 s
  · exact g32p_row18_cosetBranchStep_3158 s
  · exact g32p_row18_cosetBranchStep_3159 s
  · exact g32p_row18_cosetBranchStep_3160 s
  · exact g32p_row18_cosetBranchStep_3161 s
  · exact g32p_row18_cosetBranchStep_3162 s
  · exact g32p_row18_cosetBranchStep_3163 s
  · exact g32p_row18_cosetBranchStep_3164 s
  · exact g32p_row18_cosetBranchStep_3165 s
  · exact g32p_row18_cosetBranchStep_3166 s
  · exact g32p_row18_cosetBranchStep_3167 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3168 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3168) = g32p_row18_cosetRepresentatives 3168 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3168 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3168) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3168))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3168)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3168 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3168) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3168))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3168)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3169 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3169) = g32p_row18_cosetRepresentatives 3169 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3169 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3169) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3169))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3169)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3169 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3169) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3169))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3169)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3170 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3170) = g32p_row18_cosetRepresentatives 3170 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3170 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3170) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3170))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3170)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3170 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3170) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3170))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3170)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3171 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3171) = g32p_row18_cosetRepresentatives 3171 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3171 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3171) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3171))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3171)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3171 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3171) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3171))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3171)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3172 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3172) = g32p_row18_cosetRepresentatives 3172 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3172 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3172) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3172))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3172)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3172 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3172) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3172))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3172)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3173 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3173) = g32p_row18_cosetRepresentatives 3173 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3173 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3173) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3173))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3173)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3173 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3173) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3173))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3173)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3174 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3174) = g32p_row18_cosetRepresentatives 3174 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3174 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3174) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3174))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3174)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3174 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3174) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3174))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3174)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3175 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3175) = g32p_row18_cosetRepresentatives 3175 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3175 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3175) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3175))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3175)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3175 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3175) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3175))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3175)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3176 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3176) = g32p_row18_cosetRepresentatives 3176 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3176 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3176) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3176))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3176)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3176 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3176) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3176))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3176)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3177 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3177) = g32p_row18_cosetRepresentatives 3177 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3177 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3177) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3177))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3177)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3177 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3177) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3177))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3177)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3178 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3178) = g32p_row18_cosetRepresentatives 3178 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3178 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3178) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3178))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3178)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3178 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3178) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3178))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3178)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3179 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3179) = g32p_row18_cosetRepresentatives 3179 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3179 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3179) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3179))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3179)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3179 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3179) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3179))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3179)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3180 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3180) = g32p_row18_cosetRepresentatives 3180 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3180 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3180) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3180))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3180)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3180 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3180) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3180))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3180)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3181 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3181) = g32p_row18_cosetRepresentatives 3181 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3181 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3181) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3181))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3181)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3181 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3181) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3181))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3181)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3182 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3182) = g32p_row18_cosetRepresentatives 3182 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3182 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3182) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3182))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3182)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3182 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3182) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3182))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3182)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3183 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3183) = g32p_row18_cosetRepresentatives 3183 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3183 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3183) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3183))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3183)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3183 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3183) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3183))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3183)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0198 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 198 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 198 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3168
  · exact g32p_row18_cosetWord_3169
  · exact g32p_row18_cosetWord_3170
  · exact g32p_row18_cosetWord_3171
  · exact g32p_row18_cosetWord_3172
  · exact g32p_row18_cosetWord_3173
  · exact g32p_row18_cosetWord_3174
  · exact g32p_row18_cosetWord_3175
  · exact g32p_row18_cosetWord_3176
  · exact g32p_row18_cosetWord_3177
  · exact g32p_row18_cosetWord_3178
  · exact g32p_row18_cosetWord_3179
  · exact g32p_row18_cosetWord_3180
  · exact g32p_row18_cosetWord_3181
  · exact g32p_row18_cosetWord_3182
  · exact g32p_row18_cosetWord_3183

theorem g32p_row18_cosetGeneratorBlock_0198 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 198 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 198 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 198 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3168 s
  · exact g32p_row18_cosetGeneratorStep_3169 s
  · exact g32p_row18_cosetGeneratorStep_3170 s
  · exact g32p_row18_cosetGeneratorStep_3171 s
  · exact g32p_row18_cosetGeneratorStep_3172 s
  · exact g32p_row18_cosetGeneratorStep_3173 s
  · exact g32p_row18_cosetGeneratorStep_3174 s
  · exact g32p_row18_cosetGeneratorStep_3175 s
  · exact g32p_row18_cosetGeneratorStep_3176 s
  · exact g32p_row18_cosetGeneratorStep_3177 s
  · exact g32p_row18_cosetGeneratorStep_3178 s
  · exact g32p_row18_cosetGeneratorStep_3179 s
  · exact g32p_row18_cosetGeneratorStep_3180 s
  · exact g32p_row18_cosetGeneratorStep_3181 s
  · exact g32p_row18_cosetGeneratorStep_3182 s
  · exact g32p_row18_cosetGeneratorStep_3183 s

theorem g32p_row18_cosetBranchBlock_0198 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 198 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 198 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 198 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3168 s
  · exact g32p_row18_cosetBranchStep_3169 s
  · exact g32p_row18_cosetBranchStep_3170 s
  · exact g32p_row18_cosetBranchStep_3171 s
  · exact g32p_row18_cosetBranchStep_3172 s
  · exact g32p_row18_cosetBranchStep_3173 s
  · exact g32p_row18_cosetBranchStep_3174 s
  · exact g32p_row18_cosetBranchStep_3175 s
  · exact g32p_row18_cosetBranchStep_3176 s
  · exact g32p_row18_cosetBranchStep_3177 s
  · exact g32p_row18_cosetBranchStep_3178 s
  · exact g32p_row18_cosetBranchStep_3179 s
  · exact g32p_row18_cosetBranchStep_3180 s
  · exact g32p_row18_cosetBranchStep_3181 s
  · exact g32p_row18_cosetBranchStep_3182 s
  · exact g32p_row18_cosetBranchStep_3183 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3184 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3184) = g32p_row18_cosetRepresentatives 3184 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3184 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3184) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3184))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3184)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3184 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3184) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3184))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3184)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3185 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3185) = g32p_row18_cosetRepresentatives 3185 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3185 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3185) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3185))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3185)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3185 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3185) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3185))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3185)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3186 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3186) = g32p_row18_cosetRepresentatives 3186 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3186 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3186) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3186))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3186)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3186 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3186) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3186))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3186)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3187 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3187) = g32p_row18_cosetRepresentatives 3187 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3187 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3187) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3187))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3187)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3187 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3187) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3187))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3187)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3188 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3188) = g32p_row18_cosetRepresentatives 3188 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3188 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3188) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3188))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3188)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3188 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3188) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3188))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3188)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3189 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3189) = g32p_row18_cosetRepresentatives 3189 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3189 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3189) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3189))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3189)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3189 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3189) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3189))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3189)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3190 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3190) = g32p_row18_cosetRepresentatives 3190 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3190 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3190) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3190))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3190)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3190 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3190) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3190))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3190)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3191 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3191) = g32p_row18_cosetRepresentatives 3191 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3191 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3191) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3191))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3191)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3191 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3191) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3191))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3191)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3192 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3192) = g32p_row18_cosetRepresentatives 3192 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3192 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3192) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3192))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3192)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3192 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3192) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3192))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3192)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3193 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3193) = g32p_row18_cosetRepresentatives 3193 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3193 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3193) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3193))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3193)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3193 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3193) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3193))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3193)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3194 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3194) = g32p_row18_cosetRepresentatives 3194 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3194 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3194) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3194))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3194)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3194 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3194) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3194))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3194)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3195 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3195) = g32p_row18_cosetRepresentatives 3195 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3195 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3195) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3195))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3195)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3195 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3195) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3195))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3195)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3196 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3196) = g32p_row18_cosetRepresentatives 3196 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3196 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3196) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3196))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3196)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3196 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3196) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3196))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3196)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3197 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3197) = g32p_row18_cosetRepresentatives 3197 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3197 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3197) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3197))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3197)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3197 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3197) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3197))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3197)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3198 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3198) = g32p_row18_cosetRepresentatives 3198 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3198 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3198) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3198))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3198)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3198 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3198) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3198))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3198)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3199 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3199) = g32p_row18_cosetRepresentatives 3199 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3199 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3199) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3199))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3199)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3199 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3199) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3199))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3199)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0199 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 199 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 199 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3184
  · exact g32p_row18_cosetWord_3185
  · exact g32p_row18_cosetWord_3186
  · exact g32p_row18_cosetWord_3187
  · exact g32p_row18_cosetWord_3188
  · exact g32p_row18_cosetWord_3189
  · exact g32p_row18_cosetWord_3190
  · exact g32p_row18_cosetWord_3191
  · exact g32p_row18_cosetWord_3192
  · exact g32p_row18_cosetWord_3193
  · exact g32p_row18_cosetWord_3194
  · exact g32p_row18_cosetWord_3195
  · exact g32p_row18_cosetWord_3196
  · exact g32p_row18_cosetWord_3197
  · exact g32p_row18_cosetWord_3198
  · exact g32p_row18_cosetWord_3199

theorem g32p_row18_cosetGeneratorBlock_0199 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 199 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 199 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 199 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3184 s
  · exact g32p_row18_cosetGeneratorStep_3185 s
  · exact g32p_row18_cosetGeneratorStep_3186 s
  · exact g32p_row18_cosetGeneratorStep_3187 s
  · exact g32p_row18_cosetGeneratorStep_3188 s
  · exact g32p_row18_cosetGeneratorStep_3189 s
  · exact g32p_row18_cosetGeneratorStep_3190 s
  · exact g32p_row18_cosetGeneratorStep_3191 s
  · exact g32p_row18_cosetGeneratorStep_3192 s
  · exact g32p_row18_cosetGeneratorStep_3193 s
  · exact g32p_row18_cosetGeneratorStep_3194 s
  · exact g32p_row18_cosetGeneratorStep_3195 s
  · exact g32p_row18_cosetGeneratorStep_3196 s
  · exact g32p_row18_cosetGeneratorStep_3197 s
  · exact g32p_row18_cosetGeneratorStep_3198 s
  · exact g32p_row18_cosetGeneratorStep_3199 s

theorem g32p_row18_cosetBranchBlock_0199 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 199 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 199 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 199 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3184 s
  · exact g32p_row18_cosetBranchStep_3185 s
  · exact g32p_row18_cosetBranchStep_3186 s
  · exact g32p_row18_cosetBranchStep_3187 s
  · exact g32p_row18_cosetBranchStep_3188 s
  · exact g32p_row18_cosetBranchStep_3189 s
  · exact g32p_row18_cosetBranchStep_3190 s
  · exact g32p_row18_cosetBranchStep_3191 s
  · exact g32p_row18_cosetBranchStep_3192 s
  · exact g32p_row18_cosetBranchStep_3193 s
  · exact g32p_row18_cosetBranchStep_3194 s
  · exact g32p_row18_cosetBranchStep_3195 s
  · exact g32p_row18_cosetBranchStep_3196 s
  · exact g32p_row18_cosetBranchStep_3197 s
  · exact g32p_row18_cosetBranchStep_3198 s
  · exact g32p_row18_cosetBranchStep_3199 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3200 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3200) = g32p_row18_cosetRepresentatives 3200 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3200 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3200) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3200))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3200)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3200 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3200) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3200))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3200)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3201 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3201) = g32p_row18_cosetRepresentatives 3201 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3201 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3201) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3201))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3201)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3201 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3201) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3201))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3201)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3202 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3202) = g32p_row18_cosetRepresentatives 3202 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3202 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3202) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3202))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3202)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3202 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3202) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3202))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3202)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3203 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3203) = g32p_row18_cosetRepresentatives 3203 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3203 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3203) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3203))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3203)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3203 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3203) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3203))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3203)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3204 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3204) = g32p_row18_cosetRepresentatives 3204 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3204 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3204) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3204))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3204)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3204 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3204) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3204))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3204)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3205 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3205) = g32p_row18_cosetRepresentatives 3205 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3205 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3205) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3205))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3205)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3205 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3205) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3205))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3205)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3206 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3206) = g32p_row18_cosetRepresentatives 3206 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3206 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3206) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3206))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3206)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3206 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3206) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3206))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3206)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3207 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3207) = g32p_row18_cosetRepresentatives 3207 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3207 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3207) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3207))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3207)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3207 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3207) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3207))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3207)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3208 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3208) = g32p_row18_cosetRepresentatives 3208 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3208 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3208) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3208))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3208)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3208 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3208) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3208))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3208)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3209 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3209) = g32p_row18_cosetRepresentatives 3209 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3209 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3209) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3209))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3209)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3209 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3209) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3209))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3209)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3210 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3210) = g32p_row18_cosetRepresentatives 3210 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3210 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3210) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3210))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3210)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3210 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3210) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3210))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3210)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3211 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3211) = g32p_row18_cosetRepresentatives 3211 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3211 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3211) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3211))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3211)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3211 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3211) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3211))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3211)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3212 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3212) = g32p_row18_cosetRepresentatives 3212 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3212 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3212) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3212))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3212)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3212 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3212) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3212))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3212)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3213 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3213) = g32p_row18_cosetRepresentatives 3213 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3213 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3213) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3213))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3213)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3213 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3213) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3213))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3213)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3214 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3214) = g32p_row18_cosetRepresentatives 3214 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3214 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3214) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3214))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3214)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3214 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3214) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3214))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3214)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3215 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3215) = g32p_row18_cosetRepresentatives 3215 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3215 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3215) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3215))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3215)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3215 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3215) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3215))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3215)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0200 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 200 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 200 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3200
  · exact g32p_row18_cosetWord_3201
  · exact g32p_row18_cosetWord_3202
  · exact g32p_row18_cosetWord_3203
  · exact g32p_row18_cosetWord_3204
  · exact g32p_row18_cosetWord_3205
  · exact g32p_row18_cosetWord_3206
  · exact g32p_row18_cosetWord_3207
  · exact g32p_row18_cosetWord_3208
  · exact g32p_row18_cosetWord_3209
  · exact g32p_row18_cosetWord_3210
  · exact g32p_row18_cosetWord_3211
  · exact g32p_row18_cosetWord_3212
  · exact g32p_row18_cosetWord_3213
  · exact g32p_row18_cosetWord_3214
  · exact g32p_row18_cosetWord_3215

theorem g32p_row18_cosetGeneratorBlock_0200 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 200 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 200 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 200 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3200 s
  · exact g32p_row18_cosetGeneratorStep_3201 s
  · exact g32p_row18_cosetGeneratorStep_3202 s
  · exact g32p_row18_cosetGeneratorStep_3203 s
  · exact g32p_row18_cosetGeneratorStep_3204 s
  · exact g32p_row18_cosetGeneratorStep_3205 s
  · exact g32p_row18_cosetGeneratorStep_3206 s
  · exact g32p_row18_cosetGeneratorStep_3207 s
  · exact g32p_row18_cosetGeneratorStep_3208 s
  · exact g32p_row18_cosetGeneratorStep_3209 s
  · exact g32p_row18_cosetGeneratorStep_3210 s
  · exact g32p_row18_cosetGeneratorStep_3211 s
  · exact g32p_row18_cosetGeneratorStep_3212 s
  · exact g32p_row18_cosetGeneratorStep_3213 s
  · exact g32p_row18_cosetGeneratorStep_3214 s
  · exact g32p_row18_cosetGeneratorStep_3215 s

theorem g32p_row18_cosetBranchBlock_0200 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 200 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 200 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 200 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3200 s
  · exact g32p_row18_cosetBranchStep_3201 s
  · exact g32p_row18_cosetBranchStep_3202 s
  · exact g32p_row18_cosetBranchStep_3203 s
  · exact g32p_row18_cosetBranchStep_3204 s
  · exact g32p_row18_cosetBranchStep_3205 s
  · exact g32p_row18_cosetBranchStep_3206 s
  · exact g32p_row18_cosetBranchStep_3207 s
  · exact g32p_row18_cosetBranchStep_3208 s
  · exact g32p_row18_cosetBranchStep_3209 s
  · exact g32p_row18_cosetBranchStep_3210 s
  · exact g32p_row18_cosetBranchStep_3211 s
  · exact g32p_row18_cosetBranchStep_3212 s
  · exact g32p_row18_cosetBranchStep_3213 s
  · exact g32p_row18_cosetBranchStep_3214 s
  · exact g32p_row18_cosetBranchStep_3215 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3216 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3216) = g32p_row18_cosetRepresentatives 3216 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3216 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3216) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3216))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3216)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3216 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3216) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3216))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3216)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3217 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3217) = g32p_row18_cosetRepresentatives 3217 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3217 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3217) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3217))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3217)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3217 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3217) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3217))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3217)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3218 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3218) = g32p_row18_cosetRepresentatives 3218 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3218 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3218) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3218))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3218)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3218 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3218) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3218))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3218)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3219 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3219) = g32p_row18_cosetRepresentatives 3219 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3219 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3219) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3219))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3219)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3219 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3219) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3219))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3219)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3220 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3220) = g32p_row18_cosetRepresentatives 3220 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3220 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3220) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3220))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3220)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3220 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3220) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3220))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3220)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3221 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3221) = g32p_row18_cosetRepresentatives 3221 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3221 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3221) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3221))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3221)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3221 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3221) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3221))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3221)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3222 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3222) = g32p_row18_cosetRepresentatives 3222 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3222 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3222) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3222))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3222)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3222 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3222) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3222))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3222)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3223 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3223) = g32p_row18_cosetRepresentatives 3223 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3223 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3223) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3223))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3223)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3223 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3223) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3223))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3223)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3224 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3224) = g32p_row18_cosetRepresentatives 3224 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3224 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3224) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3224))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3224)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3224 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3224) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3224))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3224)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3225 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3225) = g32p_row18_cosetRepresentatives 3225 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3225 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3225) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3225))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3225)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3225 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3225) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3225))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3225)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3226 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3226) = g32p_row18_cosetRepresentatives 3226 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3226 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3226) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3226))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3226)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3226 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3226) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3226))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3226)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3227 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3227) = g32p_row18_cosetRepresentatives 3227 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3227 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3227) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3227))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3227)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3227 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3227) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3227))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3227)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3228 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3228) = g32p_row18_cosetRepresentatives 3228 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3228 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3228) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3228))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3228)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3228 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3228) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3228))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3228)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3229 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3229) = g32p_row18_cosetRepresentatives 3229 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3229 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3229) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3229))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3229)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3229 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3229) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3229))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3229)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3230 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3230) = g32p_row18_cosetRepresentatives 3230 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3230 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3230) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3230))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3230)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3230 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3230) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3230))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3230)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3231 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3231) = g32p_row18_cosetRepresentatives 3231 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3231 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3231) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3231))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3231)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3231 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3231) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3231))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3231)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0201 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 201 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 201 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3216
  · exact g32p_row18_cosetWord_3217
  · exact g32p_row18_cosetWord_3218
  · exact g32p_row18_cosetWord_3219
  · exact g32p_row18_cosetWord_3220
  · exact g32p_row18_cosetWord_3221
  · exact g32p_row18_cosetWord_3222
  · exact g32p_row18_cosetWord_3223
  · exact g32p_row18_cosetWord_3224
  · exact g32p_row18_cosetWord_3225
  · exact g32p_row18_cosetWord_3226
  · exact g32p_row18_cosetWord_3227
  · exact g32p_row18_cosetWord_3228
  · exact g32p_row18_cosetWord_3229
  · exact g32p_row18_cosetWord_3230
  · exact g32p_row18_cosetWord_3231

theorem g32p_row18_cosetGeneratorBlock_0201 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 201 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 201 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 201 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3216 s
  · exact g32p_row18_cosetGeneratorStep_3217 s
  · exact g32p_row18_cosetGeneratorStep_3218 s
  · exact g32p_row18_cosetGeneratorStep_3219 s
  · exact g32p_row18_cosetGeneratorStep_3220 s
  · exact g32p_row18_cosetGeneratorStep_3221 s
  · exact g32p_row18_cosetGeneratorStep_3222 s
  · exact g32p_row18_cosetGeneratorStep_3223 s
  · exact g32p_row18_cosetGeneratorStep_3224 s
  · exact g32p_row18_cosetGeneratorStep_3225 s
  · exact g32p_row18_cosetGeneratorStep_3226 s
  · exact g32p_row18_cosetGeneratorStep_3227 s
  · exact g32p_row18_cosetGeneratorStep_3228 s
  · exact g32p_row18_cosetGeneratorStep_3229 s
  · exact g32p_row18_cosetGeneratorStep_3230 s
  · exact g32p_row18_cosetGeneratorStep_3231 s

theorem g32p_row18_cosetBranchBlock_0201 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 201 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 201 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 201 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3216 s
  · exact g32p_row18_cosetBranchStep_3217 s
  · exact g32p_row18_cosetBranchStep_3218 s
  · exact g32p_row18_cosetBranchStep_3219 s
  · exact g32p_row18_cosetBranchStep_3220 s
  · exact g32p_row18_cosetBranchStep_3221 s
  · exact g32p_row18_cosetBranchStep_3222 s
  · exact g32p_row18_cosetBranchStep_3223 s
  · exact g32p_row18_cosetBranchStep_3224 s
  · exact g32p_row18_cosetBranchStep_3225 s
  · exact g32p_row18_cosetBranchStep_3226 s
  · exact g32p_row18_cosetBranchStep_3227 s
  · exact g32p_row18_cosetBranchStep_3228 s
  · exact g32p_row18_cosetBranchStep_3229 s
  · exact g32p_row18_cosetBranchStep_3230 s
  · exact g32p_row18_cosetBranchStep_3231 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3232 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3232) = g32p_row18_cosetRepresentatives 3232 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3232 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3232) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3232))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3232)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3232 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3232) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3232))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3232)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3233 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3233) = g32p_row18_cosetRepresentatives 3233 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3233 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3233) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3233))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3233)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3233 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3233) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3233))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3233)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3234 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3234) = g32p_row18_cosetRepresentatives 3234 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3234 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3234) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3234))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3234)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3234 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3234) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3234))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3234)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3235 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3235) = g32p_row18_cosetRepresentatives 3235 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3235 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3235) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3235))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3235)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3235 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3235) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3235))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3235)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3236 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3236) = g32p_row18_cosetRepresentatives 3236 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3236 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3236) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3236))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3236)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3236 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3236) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3236))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3236)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3237 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3237) = g32p_row18_cosetRepresentatives 3237 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3237 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3237) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3237))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3237)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3237 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3237) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3237))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3237)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3238 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3238) = g32p_row18_cosetRepresentatives 3238 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3238 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3238) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3238))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3238)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3238 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3238) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3238))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3238)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3239 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3239) = g32p_row18_cosetRepresentatives 3239 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3239 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3239) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3239))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3239)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3239 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3239) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3239))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3239)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3240 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3240) = g32p_row18_cosetRepresentatives 3240 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3240 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3240) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3240))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3240)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3240 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3240) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3240))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3240)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3241 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3241) = g32p_row18_cosetRepresentatives 3241 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3241 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3241) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3241))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3241)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3241 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3241) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3241))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3241)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3242 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3242) = g32p_row18_cosetRepresentatives 3242 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3242 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3242) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3242))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3242)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3242 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3242) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3242))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3242)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3243 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3243) = g32p_row18_cosetRepresentatives 3243 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3243 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3243) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3243))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3243)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3243 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3243) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3243))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3243)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3244 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3244) = g32p_row18_cosetRepresentatives 3244 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3244 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3244) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3244))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3244)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3244 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3244) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3244))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3244)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3245 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3245) = g32p_row18_cosetRepresentatives 3245 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3245 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3245) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3245))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3245)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3245 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3245) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3245))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3245)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3246 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3246) = g32p_row18_cosetRepresentatives 3246 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3246 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3246) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3246))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3246)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3246 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3246) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3246))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3246)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3247 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3247) = g32p_row18_cosetRepresentatives 3247 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3247 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3247) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3247))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3247)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3247 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3247) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3247))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3247)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0202 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 202 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 202 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3232
  · exact g32p_row18_cosetWord_3233
  · exact g32p_row18_cosetWord_3234
  · exact g32p_row18_cosetWord_3235
  · exact g32p_row18_cosetWord_3236
  · exact g32p_row18_cosetWord_3237
  · exact g32p_row18_cosetWord_3238
  · exact g32p_row18_cosetWord_3239
  · exact g32p_row18_cosetWord_3240
  · exact g32p_row18_cosetWord_3241
  · exact g32p_row18_cosetWord_3242
  · exact g32p_row18_cosetWord_3243
  · exact g32p_row18_cosetWord_3244
  · exact g32p_row18_cosetWord_3245
  · exact g32p_row18_cosetWord_3246
  · exact g32p_row18_cosetWord_3247

theorem g32p_row18_cosetGeneratorBlock_0202 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 202 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 202 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 202 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3232 s
  · exact g32p_row18_cosetGeneratorStep_3233 s
  · exact g32p_row18_cosetGeneratorStep_3234 s
  · exact g32p_row18_cosetGeneratorStep_3235 s
  · exact g32p_row18_cosetGeneratorStep_3236 s
  · exact g32p_row18_cosetGeneratorStep_3237 s
  · exact g32p_row18_cosetGeneratorStep_3238 s
  · exact g32p_row18_cosetGeneratorStep_3239 s
  · exact g32p_row18_cosetGeneratorStep_3240 s
  · exact g32p_row18_cosetGeneratorStep_3241 s
  · exact g32p_row18_cosetGeneratorStep_3242 s
  · exact g32p_row18_cosetGeneratorStep_3243 s
  · exact g32p_row18_cosetGeneratorStep_3244 s
  · exact g32p_row18_cosetGeneratorStep_3245 s
  · exact g32p_row18_cosetGeneratorStep_3246 s
  · exact g32p_row18_cosetGeneratorStep_3247 s

theorem g32p_row18_cosetBranchBlock_0202 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 202 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 202 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 202 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3232 s
  · exact g32p_row18_cosetBranchStep_3233 s
  · exact g32p_row18_cosetBranchStep_3234 s
  · exact g32p_row18_cosetBranchStep_3235 s
  · exact g32p_row18_cosetBranchStep_3236 s
  · exact g32p_row18_cosetBranchStep_3237 s
  · exact g32p_row18_cosetBranchStep_3238 s
  · exact g32p_row18_cosetBranchStep_3239 s
  · exact g32p_row18_cosetBranchStep_3240 s
  · exact g32p_row18_cosetBranchStep_3241 s
  · exact g32p_row18_cosetBranchStep_3242 s
  · exact g32p_row18_cosetBranchStep_3243 s
  · exact g32p_row18_cosetBranchStep_3244 s
  · exact g32p_row18_cosetBranchStep_3245 s
  · exact g32p_row18_cosetBranchStep_3246 s
  · exact g32p_row18_cosetBranchStep_3247 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3248 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3248) = g32p_row18_cosetRepresentatives 3248 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3248 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3248) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3248))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3248)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3248 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3248) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3248))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3248)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3249 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3249) = g32p_row18_cosetRepresentatives 3249 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3249 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3249) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3249))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3249)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3249 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3249) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3249))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3249)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3250 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3250) = g32p_row18_cosetRepresentatives 3250 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3250 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3250) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3250))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3250)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3250 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3250) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3250))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3250)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3251 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3251) = g32p_row18_cosetRepresentatives 3251 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3251 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3251) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3251))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3251)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3251 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3251) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3251))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3251)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3252 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3252) = g32p_row18_cosetRepresentatives 3252 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3252 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3252) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3252))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3252)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3252 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3252) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3252))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3252)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3253 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3253) = g32p_row18_cosetRepresentatives 3253 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3253 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3253) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3253))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3253)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3253 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3253) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3253))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3253)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3254 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3254) = g32p_row18_cosetRepresentatives 3254 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3254 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3254) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3254))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3254)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3254 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3254) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3254))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3254)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3255 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3255) = g32p_row18_cosetRepresentatives 3255 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3255 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3255) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3255))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3255)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3255 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3255) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3255))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3255)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3256 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3256) = g32p_row18_cosetRepresentatives 3256 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3256) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3256))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3256)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3256) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3256))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3256)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3257 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3257) = g32p_row18_cosetRepresentatives 3257 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3257) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3257))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3257)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3257) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3257))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3257)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3258 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3258) = g32p_row18_cosetRepresentatives 3258 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3258) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3258))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3258)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3258) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3258))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3258)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3259 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3259) = g32p_row18_cosetRepresentatives 3259 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3259) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3259))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3259)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3259) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3259))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3259)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3260 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3260) = g32p_row18_cosetRepresentatives 3260 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3260) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3260))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3260)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3260) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3260))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3260)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3261 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3261) = g32p_row18_cosetRepresentatives 3261 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3261) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3261))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3261)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3261) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3261))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3261)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3262 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3262) = g32p_row18_cosetRepresentatives 3262 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3262) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3262))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3262)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3262) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3262))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3262)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3263 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3263) = g32p_row18_cosetRepresentatives 3263 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3263) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3263))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3263)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3263) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3263))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3263)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0203 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 203 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 203 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3248
  · exact g32p_row18_cosetWord_3249
  · exact g32p_row18_cosetWord_3250
  · exact g32p_row18_cosetWord_3251
  · exact g32p_row18_cosetWord_3252
  · exact g32p_row18_cosetWord_3253
  · exact g32p_row18_cosetWord_3254
  · exact g32p_row18_cosetWord_3255
  · exact g32p_row18_cosetWord_3256
  · exact g32p_row18_cosetWord_3257
  · exact g32p_row18_cosetWord_3258
  · exact g32p_row18_cosetWord_3259
  · exact g32p_row18_cosetWord_3260
  · exact g32p_row18_cosetWord_3261
  · exact g32p_row18_cosetWord_3262
  · exact g32p_row18_cosetWord_3263

theorem g32p_row18_cosetGeneratorBlock_0203 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 203 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 203 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 203 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3248 s
  · exact g32p_row18_cosetGeneratorStep_3249 s
  · exact g32p_row18_cosetGeneratorStep_3250 s
  · exact g32p_row18_cosetGeneratorStep_3251 s
  · exact g32p_row18_cosetGeneratorStep_3252 s
  · exact g32p_row18_cosetGeneratorStep_3253 s
  · exact g32p_row18_cosetGeneratorStep_3254 s
  · exact g32p_row18_cosetGeneratorStep_3255 s
  · exact g32p_row18_cosetGeneratorStep_3256 s
  · exact g32p_row18_cosetGeneratorStep_3257 s
  · exact g32p_row18_cosetGeneratorStep_3258 s
  · exact g32p_row18_cosetGeneratorStep_3259 s
  · exact g32p_row18_cosetGeneratorStep_3260 s
  · exact g32p_row18_cosetGeneratorStep_3261 s
  · exact g32p_row18_cosetGeneratorStep_3262 s
  · exact g32p_row18_cosetGeneratorStep_3263 s

theorem g32p_row18_cosetBranchBlock_0203 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 203 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 203 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 203 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3248 s
  · exact g32p_row18_cosetBranchStep_3249 s
  · exact g32p_row18_cosetBranchStep_3250 s
  · exact g32p_row18_cosetBranchStep_3251 s
  · exact g32p_row18_cosetBranchStep_3252 s
  · exact g32p_row18_cosetBranchStep_3253 s
  · exact g32p_row18_cosetBranchStep_3254 s
  · exact g32p_row18_cosetBranchStep_3255 s
  · exact g32p_row18_cosetBranchStep_3256 s
  · exact g32p_row18_cosetBranchStep_3257 s
  · exact g32p_row18_cosetBranchStep_3258 s
  · exact g32p_row18_cosetBranchStep_3259 s
  · exact g32p_row18_cosetBranchStep_3260 s
  · exact g32p_row18_cosetBranchStep_3261 s
  · exact g32p_row18_cosetBranchStep_3262 s
  · exact g32p_row18_cosetBranchStep_3263 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3264 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3264) = g32p_row18_cosetRepresentatives 3264 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3264) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3264))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3264)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3264) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3264))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3264)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3265 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3265) = g32p_row18_cosetRepresentatives 3265 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3265) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3265))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3265)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3265) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3265))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3265)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3266 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3266) = g32p_row18_cosetRepresentatives 3266 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3266) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3266))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3266)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3266) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3266))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3266)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3267 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3267) = g32p_row18_cosetRepresentatives 3267 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3267) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3267))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3267)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3267) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3267))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3267)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3268 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3268) = g32p_row18_cosetRepresentatives 3268 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3268) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3268))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3268)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3268) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3268))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3268)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3269 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3269) = g32p_row18_cosetRepresentatives 3269 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3269) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3269))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3269)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3269) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3269))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3269)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3270 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3270) = g32p_row18_cosetRepresentatives 3270 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3270) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3270))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3270)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3270) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3270))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3270)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3271 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3271) = g32p_row18_cosetRepresentatives 3271 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3271) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3271))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3271)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3271) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3271))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3271)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3272 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3272) = g32p_row18_cosetRepresentatives 3272 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3272) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3272))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3272)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3272) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3272))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3272)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3273 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3273) = g32p_row18_cosetRepresentatives 3273 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3273) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3273))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3273)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3273) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3273))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3273)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3274 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3274) = g32p_row18_cosetRepresentatives 3274 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3274) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3274))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3274)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3274) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3274))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3274)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3275 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3275) = g32p_row18_cosetRepresentatives 3275 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3275) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3275))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3275)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3275) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3275))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3275)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3276 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3276) = g32p_row18_cosetRepresentatives 3276 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3276) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3276))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3276)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3276) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3276))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3276)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3277 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3277) = g32p_row18_cosetRepresentatives 3277 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3277) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3277))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3277)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3277) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3277))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3277)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3278 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3278) = g32p_row18_cosetRepresentatives 3278 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3278) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3278))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3278)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3278) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3278))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3278)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3279 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3279) = g32p_row18_cosetRepresentatives 3279 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3279) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3279))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3279)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3279) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3279))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3279)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0204 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 204 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 204 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3264
  · exact g32p_row18_cosetWord_3265
  · exact g32p_row18_cosetWord_3266
  · exact g32p_row18_cosetWord_3267
  · exact g32p_row18_cosetWord_3268
  · exact g32p_row18_cosetWord_3269
  · exact g32p_row18_cosetWord_3270
  · exact g32p_row18_cosetWord_3271
  · exact g32p_row18_cosetWord_3272
  · exact g32p_row18_cosetWord_3273
  · exact g32p_row18_cosetWord_3274
  · exact g32p_row18_cosetWord_3275
  · exact g32p_row18_cosetWord_3276
  · exact g32p_row18_cosetWord_3277
  · exact g32p_row18_cosetWord_3278
  · exact g32p_row18_cosetWord_3279

theorem g32p_row18_cosetGeneratorBlock_0204 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 204 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 204 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 204 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3264 s
  · exact g32p_row18_cosetGeneratorStep_3265 s
  · exact g32p_row18_cosetGeneratorStep_3266 s
  · exact g32p_row18_cosetGeneratorStep_3267 s
  · exact g32p_row18_cosetGeneratorStep_3268 s
  · exact g32p_row18_cosetGeneratorStep_3269 s
  · exact g32p_row18_cosetGeneratorStep_3270 s
  · exact g32p_row18_cosetGeneratorStep_3271 s
  · exact g32p_row18_cosetGeneratorStep_3272 s
  · exact g32p_row18_cosetGeneratorStep_3273 s
  · exact g32p_row18_cosetGeneratorStep_3274 s
  · exact g32p_row18_cosetGeneratorStep_3275 s
  · exact g32p_row18_cosetGeneratorStep_3276 s
  · exact g32p_row18_cosetGeneratorStep_3277 s
  · exact g32p_row18_cosetGeneratorStep_3278 s
  · exact g32p_row18_cosetGeneratorStep_3279 s

theorem g32p_row18_cosetBranchBlock_0204 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 204 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 204 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 204 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3264 s
  · exact g32p_row18_cosetBranchStep_3265 s
  · exact g32p_row18_cosetBranchStep_3266 s
  · exact g32p_row18_cosetBranchStep_3267 s
  · exact g32p_row18_cosetBranchStep_3268 s
  · exact g32p_row18_cosetBranchStep_3269 s
  · exact g32p_row18_cosetBranchStep_3270 s
  · exact g32p_row18_cosetBranchStep_3271 s
  · exact g32p_row18_cosetBranchStep_3272 s
  · exact g32p_row18_cosetBranchStep_3273 s
  · exact g32p_row18_cosetBranchStep_3274 s
  · exact g32p_row18_cosetBranchStep_3275 s
  · exact g32p_row18_cosetBranchStep_3276 s
  · exact g32p_row18_cosetBranchStep_3277 s
  · exact g32p_row18_cosetBranchStep_3278 s
  · exact g32p_row18_cosetBranchStep_3279 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3280 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3280) = g32p_row18_cosetRepresentatives 3280 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3280) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3280))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3280)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3280) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3280))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3280)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3281 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3281) = g32p_row18_cosetRepresentatives 3281 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3281) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3281))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3281)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3281) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3281))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3281)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3282 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3282) = g32p_row18_cosetRepresentatives 3282 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3282) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3282))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3282)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3282) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3282))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3282)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3283 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3283) = g32p_row18_cosetRepresentatives 3283 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3283) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3283))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3283)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3283) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3283))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3283)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3284 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3284) = g32p_row18_cosetRepresentatives 3284 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3284) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3284))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3284)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3284) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3284))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3284)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3285 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3285) = g32p_row18_cosetRepresentatives 3285 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3285) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3285))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3285)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3285) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3285))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3285)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3286 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3286) = g32p_row18_cosetRepresentatives 3286 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3286) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3286))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3286)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3286) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3286))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3286)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3287 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3287) = g32p_row18_cosetRepresentatives 3287 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3287) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3287))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3287)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3287) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3287))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3287)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3288 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3288) = g32p_row18_cosetRepresentatives 3288 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3288) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3288))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3288)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3288) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3288))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3288)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3289 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3289) = g32p_row18_cosetRepresentatives 3289 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3289) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3289))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3289)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3289) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3289))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3289)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3290 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3290) = g32p_row18_cosetRepresentatives 3290 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3290) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3290))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3290)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3290) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3290))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3290)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3291 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3291) = g32p_row18_cosetRepresentatives 3291 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3291) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3291))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3291)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3291) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3291))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3291)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3292 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3292) = g32p_row18_cosetRepresentatives 3292 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3292) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3292))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3292)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3292) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3292))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3292)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3293 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3293) = g32p_row18_cosetRepresentatives 3293 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3293) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3293))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3293)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3293) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3293))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3293)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3294 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3294) = g32p_row18_cosetRepresentatives 3294 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3294) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3294))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3294)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3294) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3294))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3294)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3295 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3295) = g32p_row18_cosetRepresentatives 3295 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3295) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3295))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3295)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3295) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3295))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3295)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0205 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 205 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 205 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3280
  · exact g32p_row18_cosetWord_3281
  · exact g32p_row18_cosetWord_3282
  · exact g32p_row18_cosetWord_3283
  · exact g32p_row18_cosetWord_3284
  · exact g32p_row18_cosetWord_3285
  · exact g32p_row18_cosetWord_3286
  · exact g32p_row18_cosetWord_3287
  · exact g32p_row18_cosetWord_3288
  · exact g32p_row18_cosetWord_3289
  · exact g32p_row18_cosetWord_3290
  · exact g32p_row18_cosetWord_3291
  · exact g32p_row18_cosetWord_3292
  · exact g32p_row18_cosetWord_3293
  · exact g32p_row18_cosetWord_3294
  · exact g32p_row18_cosetWord_3295

theorem g32p_row18_cosetGeneratorBlock_0205 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 205 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 205 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 205 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3280 s
  · exact g32p_row18_cosetGeneratorStep_3281 s
  · exact g32p_row18_cosetGeneratorStep_3282 s
  · exact g32p_row18_cosetGeneratorStep_3283 s
  · exact g32p_row18_cosetGeneratorStep_3284 s
  · exact g32p_row18_cosetGeneratorStep_3285 s
  · exact g32p_row18_cosetGeneratorStep_3286 s
  · exact g32p_row18_cosetGeneratorStep_3287 s
  · exact g32p_row18_cosetGeneratorStep_3288 s
  · exact g32p_row18_cosetGeneratorStep_3289 s
  · exact g32p_row18_cosetGeneratorStep_3290 s
  · exact g32p_row18_cosetGeneratorStep_3291 s
  · exact g32p_row18_cosetGeneratorStep_3292 s
  · exact g32p_row18_cosetGeneratorStep_3293 s
  · exact g32p_row18_cosetGeneratorStep_3294 s
  · exact g32p_row18_cosetGeneratorStep_3295 s

theorem g32p_row18_cosetBranchBlock_0205 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 205 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 205 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 205 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3280 s
  · exact g32p_row18_cosetBranchStep_3281 s
  · exact g32p_row18_cosetBranchStep_3282 s
  · exact g32p_row18_cosetBranchStep_3283 s
  · exact g32p_row18_cosetBranchStep_3284 s
  · exact g32p_row18_cosetBranchStep_3285 s
  · exact g32p_row18_cosetBranchStep_3286 s
  · exact g32p_row18_cosetBranchStep_3287 s
  · exact g32p_row18_cosetBranchStep_3288 s
  · exact g32p_row18_cosetBranchStep_3289 s
  · exact g32p_row18_cosetBranchStep_3290 s
  · exact g32p_row18_cosetBranchStep_3291 s
  · exact g32p_row18_cosetBranchStep_3292 s
  · exact g32p_row18_cosetBranchStep_3293 s
  · exact g32p_row18_cosetBranchStep_3294 s
  · exact g32p_row18_cosetBranchStep_3295 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3296 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3296) = g32p_row18_cosetRepresentatives 3296 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3296) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3296))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3296)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3296) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3296))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3296)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3297 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3297) = g32p_row18_cosetRepresentatives 3297 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3297) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3297))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3297)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3297) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3297))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3297)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3298 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3298) = g32p_row18_cosetRepresentatives 3298 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3298) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3298))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3298)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3298) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3298))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3298)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3299 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3299) = g32p_row18_cosetRepresentatives 3299 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3299) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3299))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3299)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3299) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3299))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3299)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3300 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3300) = g32p_row18_cosetRepresentatives 3300 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3300) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3300))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3300)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3300) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3300))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3300)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3301 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3301) = g32p_row18_cosetRepresentatives 3301 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3301) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3301))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3301)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3301) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3301))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3301)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3302 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3302) = g32p_row18_cosetRepresentatives 3302 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3302) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3302))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3302)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3302) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3302))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3302)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3303 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3303) = g32p_row18_cosetRepresentatives 3303 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3303) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3303))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3303)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3303) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3303))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3303)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3304 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3304) = g32p_row18_cosetRepresentatives 3304 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3304) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3304))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3304)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3304) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3304))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3304)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3305 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3305) = g32p_row18_cosetRepresentatives 3305 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3305) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3305))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3305)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3305) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3305))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3305)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3306 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3306) = g32p_row18_cosetRepresentatives 3306 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3306) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3306))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3306)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3306) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3306))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3306)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3307 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3307) = g32p_row18_cosetRepresentatives 3307 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3307) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3307))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3307)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3307) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3307))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3307)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3308 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3308) = g32p_row18_cosetRepresentatives 3308 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3308) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3308))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3308)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3308) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3308))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3308)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3309 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3309) = g32p_row18_cosetRepresentatives 3309 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3309) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3309))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3309)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3309) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3309))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3309)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3310 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3310) = g32p_row18_cosetRepresentatives 3310 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3310) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3310))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3310)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3310) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3310))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3310)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3311 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3311) = g32p_row18_cosetRepresentatives 3311 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3311) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3311))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3311)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3311) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3311))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3311)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0206 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 206 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 206 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3296
  · exact g32p_row18_cosetWord_3297
  · exact g32p_row18_cosetWord_3298
  · exact g32p_row18_cosetWord_3299
  · exact g32p_row18_cosetWord_3300
  · exact g32p_row18_cosetWord_3301
  · exact g32p_row18_cosetWord_3302
  · exact g32p_row18_cosetWord_3303
  · exact g32p_row18_cosetWord_3304
  · exact g32p_row18_cosetWord_3305
  · exact g32p_row18_cosetWord_3306
  · exact g32p_row18_cosetWord_3307
  · exact g32p_row18_cosetWord_3308
  · exact g32p_row18_cosetWord_3309
  · exact g32p_row18_cosetWord_3310
  · exact g32p_row18_cosetWord_3311

theorem g32p_row18_cosetGeneratorBlock_0206 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 206 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 206 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 206 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3296 s
  · exact g32p_row18_cosetGeneratorStep_3297 s
  · exact g32p_row18_cosetGeneratorStep_3298 s
  · exact g32p_row18_cosetGeneratorStep_3299 s
  · exact g32p_row18_cosetGeneratorStep_3300 s
  · exact g32p_row18_cosetGeneratorStep_3301 s
  · exact g32p_row18_cosetGeneratorStep_3302 s
  · exact g32p_row18_cosetGeneratorStep_3303 s
  · exact g32p_row18_cosetGeneratorStep_3304 s
  · exact g32p_row18_cosetGeneratorStep_3305 s
  · exact g32p_row18_cosetGeneratorStep_3306 s
  · exact g32p_row18_cosetGeneratorStep_3307 s
  · exact g32p_row18_cosetGeneratorStep_3308 s
  · exact g32p_row18_cosetGeneratorStep_3309 s
  · exact g32p_row18_cosetGeneratorStep_3310 s
  · exact g32p_row18_cosetGeneratorStep_3311 s

theorem g32p_row18_cosetBranchBlock_0206 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 206 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 206 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 206 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3296 s
  · exact g32p_row18_cosetBranchStep_3297 s
  · exact g32p_row18_cosetBranchStep_3298 s
  · exact g32p_row18_cosetBranchStep_3299 s
  · exact g32p_row18_cosetBranchStep_3300 s
  · exact g32p_row18_cosetBranchStep_3301 s
  · exact g32p_row18_cosetBranchStep_3302 s
  · exact g32p_row18_cosetBranchStep_3303 s
  · exact g32p_row18_cosetBranchStep_3304 s
  · exact g32p_row18_cosetBranchStep_3305 s
  · exact g32p_row18_cosetBranchStep_3306 s
  · exact g32p_row18_cosetBranchStep_3307 s
  · exact g32p_row18_cosetBranchStep_3308 s
  · exact g32p_row18_cosetBranchStep_3309 s
  · exact g32p_row18_cosetBranchStep_3310 s
  · exact g32p_row18_cosetBranchStep_3311 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row18_cosetWord_3312 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3312) = g32p_row18_cosetRepresentatives 3312 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3312) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3312))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3312)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3312) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3312))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3312)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3313 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3313) = g32p_row18_cosetRepresentatives 3313 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3313) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3313))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3313)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3313) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3313))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3313)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3314 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3314) = g32p_row18_cosetRepresentatives 3314 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3314) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3314))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3314)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3314) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3314))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3314)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3315 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3315) = g32p_row18_cosetRepresentatives 3315 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3315) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3315))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3315)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3315) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3315))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3315)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3316 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3316) = g32p_row18_cosetRepresentatives 3316 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3316) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3316))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3316)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3316) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3316))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3316)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3317 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3317) = g32p_row18_cosetRepresentatives 3317 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3317) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3317))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3317)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3317) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3317))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3317)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3318 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3318) = g32p_row18_cosetRepresentatives 3318 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3318) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3318))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3318)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3318) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3318))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3318)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3319 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3319) = g32p_row18_cosetRepresentatives 3319 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3319) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3319))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3319)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3319) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3319))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3319)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3320 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3320) = g32p_row18_cosetRepresentatives 3320 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3320) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3320))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3320)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3320) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3320))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3320)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3321 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3321) = g32p_row18_cosetRepresentatives 3321 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3321) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3321))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3321)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3321) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3321))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3321)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3322 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3322) = g32p_row18_cosetRepresentatives 3322 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3322) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3322))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3322)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3322) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3322))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3322)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3323 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3323) = g32p_row18_cosetRepresentatives 3323 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3323) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3323))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3323)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3323) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3323))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3323)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3324 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3324) = g32p_row18_cosetRepresentatives 3324 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3324) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3324))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3324)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3324) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3324))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3324)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3325 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3325) = g32p_row18_cosetRepresentatives 3325 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3325) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3325))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3325)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3325) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3325))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3325)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3326 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3326) = g32p_row18_cosetRepresentatives 3326 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3326) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3326))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3326)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3326) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3326))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3326)) := by
  decide +kernel

theorem g32p_row18_cosetWord_3327 :
    g32p_archiveIntegralWord (g32p_row18_cosetWords 3327) = g32p_row18_cosetRepresentatives 3327 := by
  decide +kernel

theorem g32p_row18_cosetGeneratorStep_3327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives 3327) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s 3327))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s 3327)) := by
  decide +kernel

theorem g32p_row18_cosetBranchStep_3327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives 3327) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s 3327))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s 3327)) := by
  decide +kernel

theorem g32p_row18_cosetWordBlock_0207 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row18_cosetWords (g32p_finBlockIndex 4320 207 r)) = g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 207 r) := by
  fin_cases r
  · exact g32p_row18_cosetWord_3312
  · exact g32p_row18_cosetWord_3313
  · exact g32p_row18_cosetWord_3314
  · exact g32p_row18_cosetWord_3315
  · exact g32p_row18_cosetWord_3316
  · exact g32p_row18_cosetWord_3317
  · exact g32p_row18_cosetWord_3318
  · exact g32p_row18_cosetWord_3319
  · exact g32p_row18_cosetWord_3320
  · exact g32p_row18_cosetWord_3321
  · exact g32p_row18_cosetWord_3322
  · exact g32p_row18_cosetWord_3323
  · exact g32p_row18_cosetWord_3324
  · exact g32p_row18_cosetWord_3325
  · exact g32p_row18_cosetWord_3326
  · exact g32p_row18_cosetWord_3327

theorem g32p_row18_cosetGeneratorBlock_0207 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 207 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetGeneratorNext s (g32p_finBlockIndex 4320 207 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetGeneratorFactor s (g32p_finBlockIndex 4320 207 r))) := by
  fin_cases r
  · exact g32p_row18_cosetGeneratorStep_3312 s
  · exact g32p_row18_cosetGeneratorStep_3313 s
  · exact g32p_row18_cosetGeneratorStep_3314 s
  · exact g32p_row18_cosetGeneratorStep_3315 s
  · exact g32p_row18_cosetGeneratorStep_3316 s
  · exact g32p_row18_cosetGeneratorStep_3317 s
  · exact g32p_row18_cosetGeneratorStep_3318 s
  · exact g32p_row18_cosetGeneratorStep_3319 s
  · exact g32p_row18_cosetGeneratorStep_3320 s
  · exact g32p_row18_cosetGeneratorStep_3321 s
  · exact g32p_row18_cosetGeneratorStep_3322 s
  · exact g32p_row18_cosetGeneratorStep_3323 s
  · exact g32p_row18_cosetGeneratorStep_3324 s
  · exact g32p_row18_cosetGeneratorStep_3325 s
  · exact g32p_row18_cosetGeneratorStep_3326 s
  · exact g32p_row18_cosetGeneratorStep_3327 s

theorem g32p_row18_cosetBranchBlock_0207 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row18_cosetBranchMatrices s) (g32p_row18_cosetRepresentatives (g32p_finBlockIndex 4320 207 r)) =
      HurwitzPrymRex_mmul (g32p_row18_cosetRepresentatives (g32p_row18_cosetBranchNext s (g32p_finBlockIndex 4320 207 r)))
        (g32p_row18_groupNodes (g32p_row18_cosetBranchFactor s (g32p_finBlockIndex 4320 207 r))) := by
  fin_cases r
  · exact g32p_row18_cosetBranchStep_3312 s
  · exact g32p_row18_cosetBranchStep_3313 s
  · exact g32p_row18_cosetBranchStep_3314 s
  · exact g32p_row18_cosetBranchStep_3315 s
  · exact g32p_row18_cosetBranchStep_3316 s
  · exact g32p_row18_cosetBranchStep_3317 s
  · exact g32p_row18_cosetBranchStep_3318 s
  · exact g32p_row18_cosetBranchStep_3319 s
  · exact g32p_row18_cosetBranchStep_3320 s
  · exact g32p_row18_cosetBranchStep_3321 s
  · exact g32p_row18_cosetBranchStep_3322 s
  · exact g32p_row18_cosetBranchStep_3323 s
  · exact g32p_row18_cosetBranchStep_3324 s
  · exact g32p_row18_cosetBranchStep_3325 s
  · exact g32p_row18_cosetBranchStep_3326 s
  · exact g32p_row18_cosetBranchStep_3327 s


end HodgeLean.Foundations.Program

end
