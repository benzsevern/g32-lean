import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness23CosetData

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1024 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1024) = g32p_row23_cosetRepresentatives 1024 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1024 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1024) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1024))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1024)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1024 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1024) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1024))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1024)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1025 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1025) = g32p_row23_cosetRepresentatives 1025 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1025 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1025) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1025))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1025)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1025 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1025) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1025))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1025)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1026 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1026) = g32p_row23_cosetRepresentatives 1026 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1026 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1026) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1026))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1026)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1026 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1026) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1026))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1026)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1027 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1027) = g32p_row23_cosetRepresentatives 1027 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1027 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1027) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1027))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1027)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1027 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1027) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1027))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1027)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1028 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1028) = g32p_row23_cosetRepresentatives 1028 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1028 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1028) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1028))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1028)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1028 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1028) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1028))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1028)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1029 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1029) = g32p_row23_cosetRepresentatives 1029 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1029 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1029) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1029))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1029)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1029 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1029) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1029))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1029)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1030 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1030) = g32p_row23_cosetRepresentatives 1030 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1030 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1030) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1030))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1030)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1030 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1030) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1030))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1030)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1031 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1031) = g32p_row23_cosetRepresentatives 1031 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1031 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1031) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1031))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1031)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1031 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1031) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1031))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1031)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1032 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1032) = g32p_row23_cosetRepresentatives 1032 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1032 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1032) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1032))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1032)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1032 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1032) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1032))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1032)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1033 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1033) = g32p_row23_cosetRepresentatives 1033 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1033 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1033) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1033))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1033)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1033 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1033) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1033))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1033)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1034 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1034) = g32p_row23_cosetRepresentatives 1034 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1034 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1034) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1034))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1034)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1034 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1034) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1034))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1034)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1035 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1035) = g32p_row23_cosetRepresentatives 1035 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1035 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1035) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1035))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1035)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1035 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1035) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1035))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1035)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1036 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1036) = g32p_row23_cosetRepresentatives 1036 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1036 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1036) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1036))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1036)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1036 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1036) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1036))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1036)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1037 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1037) = g32p_row23_cosetRepresentatives 1037 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1037 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1037) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1037))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1037)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1037 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1037) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1037))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1037)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1038 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1038) = g32p_row23_cosetRepresentatives 1038 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1038 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1038) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1038))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1038)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1038 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1038) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1038))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1038)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1039 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1039) = g32p_row23_cosetRepresentatives 1039 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1039 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1039) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1039))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1039)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1039 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1039) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1039))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1039)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0064 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 64 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 64 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1024
  · exact g32p_row23_cosetWord_1025
  · exact g32p_row23_cosetWord_1026
  · exact g32p_row23_cosetWord_1027
  · exact g32p_row23_cosetWord_1028
  · exact g32p_row23_cosetWord_1029
  · exact g32p_row23_cosetWord_1030
  · exact g32p_row23_cosetWord_1031
  · exact g32p_row23_cosetWord_1032
  · exact g32p_row23_cosetWord_1033
  · exact g32p_row23_cosetWord_1034
  · exact g32p_row23_cosetWord_1035
  · exact g32p_row23_cosetWord_1036
  · exact g32p_row23_cosetWord_1037
  · exact g32p_row23_cosetWord_1038
  · exact g32p_row23_cosetWord_1039

theorem g32p_row23_cosetGeneratorBlock_0064 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 64 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 64 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 64 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1024 s
  · exact g32p_row23_cosetGeneratorStep_1025 s
  · exact g32p_row23_cosetGeneratorStep_1026 s
  · exact g32p_row23_cosetGeneratorStep_1027 s
  · exact g32p_row23_cosetGeneratorStep_1028 s
  · exact g32p_row23_cosetGeneratorStep_1029 s
  · exact g32p_row23_cosetGeneratorStep_1030 s
  · exact g32p_row23_cosetGeneratorStep_1031 s
  · exact g32p_row23_cosetGeneratorStep_1032 s
  · exact g32p_row23_cosetGeneratorStep_1033 s
  · exact g32p_row23_cosetGeneratorStep_1034 s
  · exact g32p_row23_cosetGeneratorStep_1035 s
  · exact g32p_row23_cosetGeneratorStep_1036 s
  · exact g32p_row23_cosetGeneratorStep_1037 s
  · exact g32p_row23_cosetGeneratorStep_1038 s
  · exact g32p_row23_cosetGeneratorStep_1039 s

theorem g32p_row23_cosetBranchBlock_0064 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 64 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 64 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 64 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1024 s
  · exact g32p_row23_cosetBranchStep_1025 s
  · exact g32p_row23_cosetBranchStep_1026 s
  · exact g32p_row23_cosetBranchStep_1027 s
  · exact g32p_row23_cosetBranchStep_1028 s
  · exact g32p_row23_cosetBranchStep_1029 s
  · exact g32p_row23_cosetBranchStep_1030 s
  · exact g32p_row23_cosetBranchStep_1031 s
  · exact g32p_row23_cosetBranchStep_1032 s
  · exact g32p_row23_cosetBranchStep_1033 s
  · exact g32p_row23_cosetBranchStep_1034 s
  · exact g32p_row23_cosetBranchStep_1035 s
  · exact g32p_row23_cosetBranchStep_1036 s
  · exact g32p_row23_cosetBranchStep_1037 s
  · exact g32p_row23_cosetBranchStep_1038 s
  · exact g32p_row23_cosetBranchStep_1039 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1040 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1040) = g32p_row23_cosetRepresentatives 1040 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1040 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1040) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1040))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1040)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1040 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1040) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1040))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1040)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1041 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1041) = g32p_row23_cosetRepresentatives 1041 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1041 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1041) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1041))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1041)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1041 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1041) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1041))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1041)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1042 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1042) = g32p_row23_cosetRepresentatives 1042 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1042 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1042) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1042))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1042)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1042 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1042) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1042))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1042)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1043 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1043) = g32p_row23_cosetRepresentatives 1043 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1043 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1043) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1043))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1043)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1043 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1043) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1043))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1043)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1044 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1044) = g32p_row23_cosetRepresentatives 1044 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1044 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1044) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1044))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1044)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1044 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1044) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1044))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1044)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1045 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1045) = g32p_row23_cosetRepresentatives 1045 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1045 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1045) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1045))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1045)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1045 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1045) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1045))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1045)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1046 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1046) = g32p_row23_cosetRepresentatives 1046 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1046 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1046) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1046))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1046)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1046 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1046) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1046))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1046)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1047 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1047) = g32p_row23_cosetRepresentatives 1047 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1047 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1047) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1047))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1047)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1047 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1047) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1047))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1047)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1048 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1048) = g32p_row23_cosetRepresentatives 1048 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1048 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1048) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1048))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1048)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1048 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1048) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1048))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1048)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1049 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1049) = g32p_row23_cosetRepresentatives 1049 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1049 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1049) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1049))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1049)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1049 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1049) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1049))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1049)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1050 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1050) = g32p_row23_cosetRepresentatives 1050 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1050 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1050) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1050))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1050)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1050 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1050) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1050))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1050)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1051 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1051) = g32p_row23_cosetRepresentatives 1051 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1051 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1051) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1051))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1051)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1051 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1051) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1051))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1051)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1052 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1052) = g32p_row23_cosetRepresentatives 1052 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1052 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1052) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1052))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1052)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1052 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1052) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1052))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1052)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1053 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1053) = g32p_row23_cosetRepresentatives 1053 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1053 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1053) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1053))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1053)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1053 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1053) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1053))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1053)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1054 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1054) = g32p_row23_cosetRepresentatives 1054 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1054 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1054) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1054))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1054)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1054 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1054) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1054))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1054)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1055 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1055) = g32p_row23_cosetRepresentatives 1055 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1055 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1055) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1055))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1055)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1055 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1055) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1055))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1055)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0065 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 65 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 65 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1040
  · exact g32p_row23_cosetWord_1041
  · exact g32p_row23_cosetWord_1042
  · exact g32p_row23_cosetWord_1043
  · exact g32p_row23_cosetWord_1044
  · exact g32p_row23_cosetWord_1045
  · exact g32p_row23_cosetWord_1046
  · exact g32p_row23_cosetWord_1047
  · exact g32p_row23_cosetWord_1048
  · exact g32p_row23_cosetWord_1049
  · exact g32p_row23_cosetWord_1050
  · exact g32p_row23_cosetWord_1051
  · exact g32p_row23_cosetWord_1052
  · exact g32p_row23_cosetWord_1053
  · exact g32p_row23_cosetWord_1054
  · exact g32p_row23_cosetWord_1055

theorem g32p_row23_cosetGeneratorBlock_0065 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 65 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 65 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 65 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1040 s
  · exact g32p_row23_cosetGeneratorStep_1041 s
  · exact g32p_row23_cosetGeneratorStep_1042 s
  · exact g32p_row23_cosetGeneratorStep_1043 s
  · exact g32p_row23_cosetGeneratorStep_1044 s
  · exact g32p_row23_cosetGeneratorStep_1045 s
  · exact g32p_row23_cosetGeneratorStep_1046 s
  · exact g32p_row23_cosetGeneratorStep_1047 s
  · exact g32p_row23_cosetGeneratorStep_1048 s
  · exact g32p_row23_cosetGeneratorStep_1049 s
  · exact g32p_row23_cosetGeneratorStep_1050 s
  · exact g32p_row23_cosetGeneratorStep_1051 s
  · exact g32p_row23_cosetGeneratorStep_1052 s
  · exact g32p_row23_cosetGeneratorStep_1053 s
  · exact g32p_row23_cosetGeneratorStep_1054 s
  · exact g32p_row23_cosetGeneratorStep_1055 s

theorem g32p_row23_cosetBranchBlock_0065 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 65 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 65 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 65 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1040 s
  · exact g32p_row23_cosetBranchStep_1041 s
  · exact g32p_row23_cosetBranchStep_1042 s
  · exact g32p_row23_cosetBranchStep_1043 s
  · exact g32p_row23_cosetBranchStep_1044 s
  · exact g32p_row23_cosetBranchStep_1045 s
  · exact g32p_row23_cosetBranchStep_1046 s
  · exact g32p_row23_cosetBranchStep_1047 s
  · exact g32p_row23_cosetBranchStep_1048 s
  · exact g32p_row23_cosetBranchStep_1049 s
  · exact g32p_row23_cosetBranchStep_1050 s
  · exact g32p_row23_cosetBranchStep_1051 s
  · exact g32p_row23_cosetBranchStep_1052 s
  · exact g32p_row23_cosetBranchStep_1053 s
  · exact g32p_row23_cosetBranchStep_1054 s
  · exact g32p_row23_cosetBranchStep_1055 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1056 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1056) = g32p_row23_cosetRepresentatives 1056 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1056 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1056) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1056))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1056)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1056 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1056) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1056))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1056)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1057 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1057) = g32p_row23_cosetRepresentatives 1057 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1057 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1057) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1057))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1057)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1057 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1057) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1057))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1057)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1058 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1058) = g32p_row23_cosetRepresentatives 1058 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1058 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1058) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1058))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1058)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1058 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1058) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1058))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1058)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1059 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1059) = g32p_row23_cosetRepresentatives 1059 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1059 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1059) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1059))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1059)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1059 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1059) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1059))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1059)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1060 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1060) = g32p_row23_cosetRepresentatives 1060 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1060 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1060) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1060))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1060)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1060 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1060) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1060))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1060)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1061 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1061) = g32p_row23_cosetRepresentatives 1061 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1061 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1061) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1061))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1061)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1061 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1061) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1061))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1061)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1062 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1062) = g32p_row23_cosetRepresentatives 1062 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1062 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1062) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1062))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1062)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1062 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1062) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1062))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1062)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1063 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1063) = g32p_row23_cosetRepresentatives 1063 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1063 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1063) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1063))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1063)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1063 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1063) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1063))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1063)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1064 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1064) = g32p_row23_cosetRepresentatives 1064 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1064 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1064) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1064))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1064)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1064 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1064) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1064))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1064)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1065 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1065) = g32p_row23_cosetRepresentatives 1065 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1065 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1065) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1065))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1065)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1065 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1065) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1065))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1065)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1066 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1066) = g32p_row23_cosetRepresentatives 1066 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1066 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1066) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1066))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1066)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1066 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1066) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1066))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1066)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1067 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1067) = g32p_row23_cosetRepresentatives 1067 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1067 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1067) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1067))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1067)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1067 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1067) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1067))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1067)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1068 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1068) = g32p_row23_cosetRepresentatives 1068 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1068 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1068) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1068))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1068)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1068 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1068) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1068))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1068)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1069 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1069) = g32p_row23_cosetRepresentatives 1069 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1069 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1069) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1069))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1069)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1069 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1069) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1069))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1069)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1070 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1070) = g32p_row23_cosetRepresentatives 1070 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1070 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1070) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1070))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1070)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1070 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1070) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1070))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1070)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1071 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1071) = g32p_row23_cosetRepresentatives 1071 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1071 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1071) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1071))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1071)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1071 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1071) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1071))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1071)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0066 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 66 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 66 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1056
  · exact g32p_row23_cosetWord_1057
  · exact g32p_row23_cosetWord_1058
  · exact g32p_row23_cosetWord_1059
  · exact g32p_row23_cosetWord_1060
  · exact g32p_row23_cosetWord_1061
  · exact g32p_row23_cosetWord_1062
  · exact g32p_row23_cosetWord_1063
  · exact g32p_row23_cosetWord_1064
  · exact g32p_row23_cosetWord_1065
  · exact g32p_row23_cosetWord_1066
  · exact g32p_row23_cosetWord_1067
  · exact g32p_row23_cosetWord_1068
  · exact g32p_row23_cosetWord_1069
  · exact g32p_row23_cosetWord_1070
  · exact g32p_row23_cosetWord_1071

theorem g32p_row23_cosetGeneratorBlock_0066 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 66 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 66 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 66 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1056 s
  · exact g32p_row23_cosetGeneratorStep_1057 s
  · exact g32p_row23_cosetGeneratorStep_1058 s
  · exact g32p_row23_cosetGeneratorStep_1059 s
  · exact g32p_row23_cosetGeneratorStep_1060 s
  · exact g32p_row23_cosetGeneratorStep_1061 s
  · exact g32p_row23_cosetGeneratorStep_1062 s
  · exact g32p_row23_cosetGeneratorStep_1063 s
  · exact g32p_row23_cosetGeneratorStep_1064 s
  · exact g32p_row23_cosetGeneratorStep_1065 s
  · exact g32p_row23_cosetGeneratorStep_1066 s
  · exact g32p_row23_cosetGeneratorStep_1067 s
  · exact g32p_row23_cosetGeneratorStep_1068 s
  · exact g32p_row23_cosetGeneratorStep_1069 s
  · exact g32p_row23_cosetGeneratorStep_1070 s
  · exact g32p_row23_cosetGeneratorStep_1071 s

theorem g32p_row23_cosetBranchBlock_0066 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 66 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 66 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 66 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1056 s
  · exact g32p_row23_cosetBranchStep_1057 s
  · exact g32p_row23_cosetBranchStep_1058 s
  · exact g32p_row23_cosetBranchStep_1059 s
  · exact g32p_row23_cosetBranchStep_1060 s
  · exact g32p_row23_cosetBranchStep_1061 s
  · exact g32p_row23_cosetBranchStep_1062 s
  · exact g32p_row23_cosetBranchStep_1063 s
  · exact g32p_row23_cosetBranchStep_1064 s
  · exact g32p_row23_cosetBranchStep_1065 s
  · exact g32p_row23_cosetBranchStep_1066 s
  · exact g32p_row23_cosetBranchStep_1067 s
  · exact g32p_row23_cosetBranchStep_1068 s
  · exact g32p_row23_cosetBranchStep_1069 s
  · exact g32p_row23_cosetBranchStep_1070 s
  · exact g32p_row23_cosetBranchStep_1071 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1072 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1072) = g32p_row23_cosetRepresentatives 1072 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1072 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1072) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1072))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1072)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1072 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1072) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1072))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1072)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1073 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1073) = g32p_row23_cosetRepresentatives 1073 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1073 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1073) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1073))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1073)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1073 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1073) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1073))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1073)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1074 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1074) = g32p_row23_cosetRepresentatives 1074 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1074 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1074) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1074))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1074)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1074 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1074) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1074))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1074)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1075 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1075) = g32p_row23_cosetRepresentatives 1075 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1075 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1075) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1075))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1075)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1075 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1075) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1075))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1075)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1076 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1076) = g32p_row23_cosetRepresentatives 1076 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1076 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1076) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1076))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1076)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1076 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1076) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1076))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1076)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1077 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1077) = g32p_row23_cosetRepresentatives 1077 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1077 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1077) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1077))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1077)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1077 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1077) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1077))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1077)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1078 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1078) = g32p_row23_cosetRepresentatives 1078 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1078 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1078) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1078))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1078)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1078 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1078) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1078))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1078)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1079 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1079) = g32p_row23_cosetRepresentatives 1079 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1079 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1079) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1079))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1079)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1079 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1079) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1079))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1079)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1080 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1080) = g32p_row23_cosetRepresentatives 1080 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1080 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1080) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1080))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1080)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1080 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1080) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1080))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1080)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1081 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1081) = g32p_row23_cosetRepresentatives 1081 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1081 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1081) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1081))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1081)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1081 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1081) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1081))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1081)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1082 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1082) = g32p_row23_cosetRepresentatives 1082 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1082 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1082) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1082))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1082)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1082 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1082) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1082))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1082)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1083 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1083) = g32p_row23_cosetRepresentatives 1083 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1083 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1083) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1083))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1083)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1083 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1083) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1083))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1083)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1084 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1084) = g32p_row23_cosetRepresentatives 1084 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1084 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1084) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1084))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1084)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1084 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1084) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1084))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1084)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1085 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1085) = g32p_row23_cosetRepresentatives 1085 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1085 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1085) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1085))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1085)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1085 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1085) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1085))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1085)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1086 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1086) = g32p_row23_cosetRepresentatives 1086 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1086 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1086) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1086))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1086)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1086 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1086) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1086))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1086)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1087 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1087) = g32p_row23_cosetRepresentatives 1087 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1087 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1087) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1087))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1087)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1087 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1087) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1087))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1087)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0067 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 67 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 67 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1072
  · exact g32p_row23_cosetWord_1073
  · exact g32p_row23_cosetWord_1074
  · exact g32p_row23_cosetWord_1075
  · exact g32p_row23_cosetWord_1076
  · exact g32p_row23_cosetWord_1077
  · exact g32p_row23_cosetWord_1078
  · exact g32p_row23_cosetWord_1079
  · exact g32p_row23_cosetWord_1080
  · exact g32p_row23_cosetWord_1081
  · exact g32p_row23_cosetWord_1082
  · exact g32p_row23_cosetWord_1083
  · exact g32p_row23_cosetWord_1084
  · exact g32p_row23_cosetWord_1085
  · exact g32p_row23_cosetWord_1086
  · exact g32p_row23_cosetWord_1087

theorem g32p_row23_cosetGeneratorBlock_0067 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 67 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 67 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 67 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1072 s
  · exact g32p_row23_cosetGeneratorStep_1073 s
  · exact g32p_row23_cosetGeneratorStep_1074 s
  · exact g32p_row23_cosetGeneratorStep_1075 s
  · exact g32p_row23_cosetGeneratorStep_1076 s
  · exact g32p_row23_cosetGeneratorStep_1077 s
  · exact g32p_row23_cosetGeneratorStep_1078 s
  · exact g32p_row23_cosetGeneratorStep_1079 s
  · exact g32p_row23_cosetGeneratorStep_1080 s
  · exact g32p_row23_cosetGeneratorStep_1081 s
  · exact g32p_row23_cosetGeneratorStep_1082 s
  · exact g32p_row23_cosetGeneratorStep_1083 s
  · exact g32p_row23_cosetGeneratorStep_1084 s
  · exact g32p_row23_cosetGeneratorStep_1085 s
  · exact g32p_row23_cosetGeneratorStep_1086 s
  · exact g32p_row23_cosetGeneratorStep_1087 s

theorem g32p_row23_cosetBranchBlock_0067 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 67 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 67 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 67 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1072 s
  · exact g32p_row23_cosetBranchStep_1073 s
  · exact g32p_row23_cosetBranchStep_1074 s
  · exact g32p_row23_cosetBranchStep_1075 s
  · exact g32p_row23_cosetBranchStep_1076 s
  · exact g32p_row23_cosetBranchStep_1077 s
  · exact g32p_row23_cosetBranchStep_1078 s
  · exact g32p_row23_cosetBranchStep_1079 s
  · exact g32p_row23_cosetBranchStep_1080 s
  · exact g32p_row23_cosetBranchStep_1081 s
  · exact g32p_row23_cosetBranchStep_1082 s
  · exact g32p_row23_cosetBranchStep_1083 s
  · exact g32p_row23_cosetBranchStep_1084 s
  · exact g32p_row23_cosetBranchStep_1085 s
  · exact g32p_row23_cosetBranchStep_1086 s
  · exact g32p_row23_cosetBranchStep_1087 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1088 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1088) = g32p_row23_cosetRepresentatives 1088 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1088 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1088) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1088))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1088)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1088 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1088) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1088))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1088)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1089 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1089) = g32p_row23_cosetRepresentatives 1089 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1089 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1089) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1089))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1089)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1089 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1089) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1089))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1089)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1090 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1090) = g32p_row23_cosetRepresentatives 1090 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1090 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1090) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1090))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1090)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1090 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1090) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1090))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1090)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1091 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1091) = g32p_row23_cosetRepresentatives 1091 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1091 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1091) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1091))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1091)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1091 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1091) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1091))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1091)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1092 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1092) = g32p_row23_cosetRepresentatives 1092 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1092 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1092) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1092))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1092)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1092 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1092) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1092))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1092)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1093 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1093) = g32p_row23_cosetRepresentatives 1093 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1093 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1093) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1093))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1093)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1093 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1093) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1093))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1093)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1094 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1094) = g32p_row23_cosetRepresentatives 1094 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1094 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1094) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1094))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1094)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1094 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1094) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1094))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1094)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1095 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1095) = g32p_row23_cosetRepresentatives 1095 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1095 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1095) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1095))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1095)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1095 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1095) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1095))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1095)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1096 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1096) = g32p_row23_cosetRepresentatives 1096 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1096 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1096) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1096))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1096)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1096 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1096) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1096))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1096)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1097 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1097) = g32p_row23_cosetRepresentatives 1097 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1097 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1097) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1097))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1097)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1097 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1097) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1097))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1097)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1098 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1098) = g32p_row23_cosetRepresentatives 1098 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1098 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1098) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1098))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1098)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1098 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1098) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1098))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1098)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1099 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1099) = g32p_row23_cosetRepresentatives 1099 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1099 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1099) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1099))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1099)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1099 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1099) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1099))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1099)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1100 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1100) = g32p_row23_cosetRepresentatives 1100 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1100 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1100) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1100))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1100)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1100 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1100) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1100))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1100)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1101 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1101) = g32p_row23_cosetRepresentatives 1101 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1101 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1101) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1101))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1101)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1101 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1101) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1101))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1101)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1102 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1102) = g32p_row23_cosetRepresentatives 1102 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1102 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1102) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1102))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1102)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1102 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1102) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1102))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1102)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1103 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1103) = g32p_row23_cosetRepresentatives 1103 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1103 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1103) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1103))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1103)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1103 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1103) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1103))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1103)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0068 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 68 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 68 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1088
  · exact g32p_row23_cosetWord_1089
  · exact g32p_row23_cosetWord_1090
  · exact g32p_row23_cosetWord_1091
  · exact g32p_row23_cosetWord_1092
  · exact g32p_row23_cosetWord_1093
  · exact g32p_row23_cosetWord_1094
  · exact g32p_row23_cosetWord_1095
  · exact g32p_row23_cosetWord_1096
  · exact g32p_row23_cosetWord_1097
  · exact g32p_row23_cosetWord_1098
  · exact g32p_row23_cosetWord_1099
  · exact g32p_row23_cosetWord_1100
  · exact g32p_row23_cosetWord_1101
  · exact g32p_row23_cosetWord_1102
  · exact g32p_row23_cosetWord_1103

theorem g32p_row23_cosetGeneratorBlock_0068 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 68 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 68 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 68 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1088 s
  · exact g32p_row23_cosetGeneratorStep_1089 s
  · exact g32p_row23_cosetGeneratorStep_1090 s
  · exact g32p_row23_cosetGeneratorStep_1091 s
  · exact g32p_row23_cosetGeneratorStep_1092 s
  · exact g32p_row23_cosetGeneratorStep_1093 s
  · exact g32p_row23_cosetGeneratorStep_1094 s
  · exact g32p_row23_cosetGeneratorStep_1095 s
  · exact g32p_row23_cosetGeneratorStep_1096 s
  · exact g32p_row23_cosetGeneratorStep_1097 s
  · exact g32p_row23_cosetGeneratorStep_1098 s
  · exact g32p_row23_cosetGeneratorStep_1099 s
  · exact g32p_row23_cosetGeneratorStep_1100 s
  · exact g32p_row23_cosetGeneratorStep_1101 s
  · exact g32p_row23_cosetGeneratorStep_1102 s
  · exact g32p_row23_cosetGeneratorStep_1103 s

theorem g32p_row23_cosetBranchBlock_0068 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 68 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 68 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 68 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1088 s
  · exact g32p_row23_cosetBranchStep_1089 s
  · exact g32p_row23_cosetBranchStep_1090 s
  · exact g32p_row23_cosetBranchStep_1091 s
  · exact g32p_row23_cosetBranchStep_1092 s
  · exact g32p_row23_cosetBranchStep_1093 s
  · exact g32p_row23_cosetBranchStep_1094 s
  · exact g32p_row23_cosetBranchStep_1095 s
  · exact g32p_row23_cosetBranchStep_1096 s
  · exact g32p_row23_cosetBranchStep_1097 s
  · exact g32p_row23_cosetBranchStep_1098 s
  · exact g32p_row23_cosetBranchStep_1099 s
  · exact g32p_row23_cosetBranchStep_1100 s
  · exact g32p_row23_cosetBranchStep_1101 s
  · exact g32p_row23_cosetBranchStep_1102 s
  · exact g32p_row23_cosetBranchStep_1103 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1104 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1104) = g32p_row23_cosetRepresentatives 1104 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1104 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1104) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1104))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1104)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1104 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1104) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1104))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1104)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1105 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1105) = g32p_row23_cosetRepresentatives 1105 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1105 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1105) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1105))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1105)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1105 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1105) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1105))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1105)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1106 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1106) = g32p_row23_cosetRepresentatives 1106 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1106 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1106) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1106))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1106)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1106 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1106) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1106))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1106)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1107 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1107) = g32p_row23_cosetRepresentatives 1107 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1107 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1107) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1107))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1107)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1107 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1107) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1107))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1107)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1108 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1108) = g32p_row23_cosetRepresentatives 1108 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1108 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1108) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1108))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1108)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1108 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1108) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1108))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1108)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1109 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1109) = g32p_row23_cosetRepresentatives 1109 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1109 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1109) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1109))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1109)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1109 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1109) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1109))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1109)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1110 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1110) = g32p_row23_cosetRepresentatives 1110 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1110 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1110) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1110))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1110)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1110 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1110) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1110))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1110)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1111 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1111) = g32p_row23_cosetRepresentatives 1111 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1111 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1111) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1111))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1111)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1111 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1111) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1111))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1111)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1112 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1112) = g32p_row23_cosetRepresentatives 1112 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1112 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1112) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1112))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1112)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1112 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1112) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1112))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1112)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1113 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1113) = g32p_row23_cosetRepresentatives 1113 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1113 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1113) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1113))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1113)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1113 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1113) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1113))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1113)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1114 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1114) = g32p_row23_cosetRepresentatives 1114 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1114 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1114) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1114))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1114)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1114 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1114) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1114))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1114)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1115 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1115) = g32p_row23_cosetRepresentatives 1115 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1115 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1115) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1115))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1115)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1115 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1115) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1115))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1115)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1116 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1116) = g32p_row23_cosetRepresentatives 1116 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1116 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1116) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1116))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1116)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1116 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1116) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1116))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1116)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1117 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1117) = g32p_row23_cosetRepresentatives 1117 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1117 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1117) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1117))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1117)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1117 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1117) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1117))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1117)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1118 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1118) = g32p_row23_cosetRepresentatives 1118 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1118 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1118) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1118))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1118)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1118 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1118) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1118))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1118)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1119 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1119) = g32p_row23_cosetRepresentatives 1119 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1119 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1119) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1119))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1119)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1119 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1119) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1119))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1119)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0069 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 69 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 69 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1104
  · exact g32p_row23_cosetWord_1105
  · exact g32p_row23_cosetWord_1106
  · exact g32p_row23_cosetWord_1107
  · exact g32p_row23_cosetWord_1108
  · exact g32p_row23_cosetWord_1109
  · exact g32p_row23_cosetWord_1110
  · exact g32p_row23_cosetWord_1111
  · exact g32p_row23_cosetWord_1112
  · exact g32p_row23_cosetWord_1113
  · exact g32p_row23_cosetWord_1114
  · exact g32p_row23_cosetWord_1115
  · exact g32p_row23_cosetWord_1116
  · exact g32p_row23_cosetWord_1117
  · exact g32p_row23_cosetWord_1118
  · exact g32p_row23_cosetWord_1119

theorem g32p_row23_cosetGeneratorBlock_0069 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 69 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 69 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 69 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1104 s
  · exact g32p_row23_cosetGeneratorStep_1105 s
  · exact g32p_row23_cosetGeneratorStep_1106 s
  · exact g32p_row23_cosetGeneratorStep_1107 s
  · exact g32p_row23_cosetGeneratorStep_1108 s
  · exact g32p_row23_cosetGeneratorStep_1109 s
  · exact g32p_row23_cosetGeneratorStep_1110 s
  · exact g32p_row23_cosetGeneratorStep_1111 s
  · exact g32p_row23_cosetGeneratorStep_1112 s
  · exact g32p_row23_cosetGeneratorStep_1113 s
  · exact g32p_row23_cosetGeneratorStep_1114 s
  · exact g32p_row23_cosetGeneratorStep_1115 s
  · exact g32p_row23_cosetGeneratorStep_1116 s
  · exact g32p_row23_cosetGeneratorStep_1117 s
  · exact g32p_row23_cosetGeneratorStep_1118 s
  · exact g32p_row23_cosetGeneratorStep_1119 s

theorem g32p_row23_cosetBranchBlock_0069 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 69 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 69 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 69 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1104 s
  · exact g32p_row23_cosetBranchStep_1105 s
  · exact g32p_row23_cosetBranchStep_1106 s
  · exact g32p_row23_cosetBranchStep_1107 s
  · exact g32p_row23_cosetBranchStep_1108 s
  · exact g32p_row23_cosetBranchStep_1109 s
  · exact g32p_row23_cosetBranchStep_1110 s
  · exact g32p_row23_cosetBranchStep_1111 s
  · exact g32p_row23_cosetBranchStep_1112 s
  · exact g32p_row23_cosetBranchStep_1113 s
  · exact g32p_row23_cosetBranchStep_1114 s
  · exact g32p_row23_cosetBranchStep_1115 s
  · exact g32p_row23_cosetBranchStep_1116 s
  · exact g32p_row23_cosetBranchStep_1117 s
  · exact g32p_row23_cosetBranchStep_1118 s
  · exact g32p_row23_cosetBranchStep_1119 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1120 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1120) = g32p_row23_cosetRepresentatives 1120 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1120 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1120) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1120))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1120)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1120 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1120) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1120))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1120)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1121 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1121) = g32p_row23_cosetRepresentatives 1121 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1121 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1121) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1121))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1121)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1121 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1121) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1121))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1121)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1122 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1122) = g32p_row23_cosetRepresentatives 1122 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1122 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1122) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1122))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1122)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1122 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1122) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1122))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1122)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1123 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1123) = g32p_row23_cosetRepresentatives 1123 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1123 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1123) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1123))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1123)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1123 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1123) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1123))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1123)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1124 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1124) = g32p_row23_cosetRepresentatives 1124 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1124 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1124) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1124))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1124)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1124 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1124) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1124))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1124)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1125 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1125) = g32p_row23_cosetRepresentatives 1125 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1125 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1125) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1125))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1125)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1125 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1125) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1125))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1125)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1126 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1126) = g32p_row23_cosetRepresentatives 1126 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1126 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1126) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1126))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1126)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1126 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1126) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1126))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1126)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1127 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1127) = g32p_row23_cosetRepresentatives 1127 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1127 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1127) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1127))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1127)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1127 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1127) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1127))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1127)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1128 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1128) = g32p_row23_cosetRepresentatives 1128 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1128 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1128) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1128))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1128)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1128 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1128) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1128))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1128)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1129 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1129) = g32p_row23_cosetRepresentatives 1129 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1129 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1129) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1129))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1129)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1129 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1129) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1129))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1129)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1130 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1130) = g32p_row23_cosetRepresentatives 1130 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1130 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1130) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1130))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1130)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1130 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1130) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1130))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1130)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1131 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1131) = g32p_row23_cosetRepresentatives 1131 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1131 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1131) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1131))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1131)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1131 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1131) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1131))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1131)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1132 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1132) = g32p_row23_cosetRepresentatives 1132 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1132 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1132) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1132))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1132)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1132 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1132) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1132))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1132)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1133 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1133) = g32p_row23_cosetRepresentatives 1133 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1133 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1133) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1133))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1133)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1133 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1133) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1133))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1133)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1134 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1134) = g32p_row23_cosetRepresentatives 1134 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1134 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1134) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1134))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1134)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1134 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1134) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1134))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1134)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1135 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1135) = g32p_row23_cosetRepresentatives 1135 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1135 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1135) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1135))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1135)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1135 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1135) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1135))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1135)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0070 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 70 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 70 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1120
  · exact g32p_row23_cosetWord_1121
  · exact g32p_row23_cosetWord_1122
  · exact g32p_row23_cosetWord_1123
  · exact g32p_row23_cosetWord_1124
  · exact g32p_row23_cosetWord_1125
  · exact g32p_row23_cosetWord_1126
  · exact g32p_row23_cosetWord_1127
  · exact g32p_row23_cosetWord_1128
  · exact g32p_row23_cosetWord_1129
  · exact g32p_row23_cosetWord_1130
  · exact g32p_row23_cosetWord_1131
  · exact g32p_row23_cosetWord_1132
  · exact g32p_row23_cosetWord_1133
  · exact g32p_row23_cosetWord_1134
  · exact g32p_row23_cosetWord_1135

theorem g32p_row23_cosetGeneratorBlock_0070 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 70 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 70 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 70 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1120 s
  · exact g32p_row23_cosetGeneratorStep_1121 s
  · exact g32p_row23_cosetGeneratorStep_1122 s
  · exact g32p_row23_cosetGeneratorStep_1123 s
  · exact g32p_row23_cosetGeneratorStep_1124 s
  · exact g32p_row23_cosetGeneratorStep_1125 s
  · exact g32p_row23_cosetGeneratorStep_1126 s
  · exact g32p_row23_cosetGeneratorStep_1127 s
  · exact g32p_row23_cosetGeneratorStep_1128 s
  · exact g32p_row23_cosetGeneratorStep_1129 s
  · exact g32p_row23_cosetGeneratorStep_1130 s
  · exact g32p_row23_cosetGeneratorStep_1131 s
  · exact g32p_row23_cosetGeneratorStep_1132 s
  · exact g32p_row23_cosetGeneratorStep_1133 s
  · exact g32p_row23_cosetGeneratorStep_1134 s
  · exact g32p_row23_cosetGeneratorStep_1135 s

theorem g32p_row23_cosetBranchBlock_0070 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 70 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 70 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 70 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1120 s
  · exact g32p_row23_cosetBranchStep_1121 s
  · exact g32p_row23_cosetBranchStep_1122 s
  · exact g32p_row23_cosetBranchStep_1123 s
  · exact g32p_row23_cosetBranchStep_1124 s
  · exact g32p_row23_cosetBranchStep_1125 s
  · exact g32p_row23_cosetBranchStep_1126 s
  · exact g32p_row23_cosetBranchStep_1127 s
  · exact g32p_row23_cosetBranchStep_1128 s
  · exact g32p_row23_cosetBranchStep_1129 s
  · exact g32p_row23_cosetBranchStep_1130 s
  · exact g32p_row23_cosetBranchStep_1131 s
  · exact g32p_row23_cosetBranchStep_1132 s
  · exact g32p_row23_cosetBranchStep_1133 s
  · exact g32p_row23_cosetBranchStep_1134 s
  · exact g32p_row23_cosetBranchStep_1135 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1136 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1136) = g32p_row23_cosetRepresentatives 1136 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1136 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1136) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1136))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1136)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1136 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1136) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1136))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1136)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1137 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1137) = g32p_row23_cosetRepresentatives 1137 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1137 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1137) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1137))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1137)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1137 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1137) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1137))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1137)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1138 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1138) = g32p_row23_cosetRepresentatives 1138 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1138 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1138) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1138))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1138)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1138 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1138) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1138))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1138)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1139 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1139) = g32p_row23_cosetRepresentatives 1139 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1139 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1139) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1139))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1139)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1139 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1139) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1139))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1139)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1140 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1140) = g32p_row23_cosetRepresentatives 1140 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1140 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1140) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1140))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1140)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1140 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1140) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1140))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1140)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1141 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1141) = g32p_row23_cosetRepresentatives 1141 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1141 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1141) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1141))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1141)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1141 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1141) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1141))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1141)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1142 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1142) = g32p_row23_cosetRepresentatives 1142 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1142 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1142) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1142))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1142)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1142 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1142) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1142))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1142)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1143 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1143) = g32p_row23_cosetRepresentatives 1143 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1143 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1143) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1143))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1143)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1143 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1143) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1143))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1143)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1144 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1144) = g32p_row23_cosetRepresentatives 1144 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1144 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1144) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1144))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1144)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1144 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1144) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1144))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1144)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1145 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1145) = g32p_row23_cosetRepresentatives 1145 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1145 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1145) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1145))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1145)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1145 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1145) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1145))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1145)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1146 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1146) = g32p_row23_cosetRepresentatives 1146 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1146 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1146) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1146))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1146)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1146 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1146) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1146))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1146)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1147 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1147) = g32p_row23_cosetRepresentatives 1147 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1147 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1147) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1147))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1147)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1147 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1147) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1147))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1147)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1148 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1148) = g32p_row23_cosetRepresentatives 1148 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1148 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1148) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1148))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1148)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1148 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1148) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1148))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1148)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1149 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1149) = g32p_row23_cosetRepresentatives 1149 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1149 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1149) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1149))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1149)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1149 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1149) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1149))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1149)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1150 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1150) = g32p_row23_cosetRepresentatives 1150 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1150 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1150) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1150))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1150)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1150 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1150) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1150))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1150)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1151 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1151) = g32p_row23_cosetRepresentatives 1151 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1151 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1151) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1151))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1151)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1151 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1151) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1151))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1151)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0071 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 71 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 71 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1136
  · exact g32p_row23_cosetWord_1137
  · exact g32p_row23_cosetWord_1138
  · exact g32p_row23_cosetWord_1139
  · exact g32p_row23_cosetWord_1140
  · exact g32p_row23_cosetWord_1141
  · exact g32p_row23_cosetWord_1142
  · exact g32p_row23_cosetWord_1143
  · exact g32p_row23_cosetWord_1144
  · exact g32p_row23_cosetWord_1145
  · exact g32p_row23_cosetWord_1146
  · exact g32p_row23_cosetWord_1147
  · exact g32p_row23_cosetWord_1148
  · exact g32p_row23_cosetWord_1149
  · exact g32p_row23_cosetWord_1150
  · exact g32p_row23_cosetWord_1151

theorem g32p_row23_cosetGeneratorBlock_0071 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 71 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 71 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 71 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1136 s
  · exact g32p_row23_cosetGeneratorStep_1137 s
  · exact g32p_row23_cosetGeneratorStep_1138 s
  · exact g32p_row23_cosetGeneratorStep_1139 s
  · exact g32p_row23_cosetGeneratorStep_1140 s
  · exact g32p_row23_cosetGeneratorStep_1141 s
  · exact g32p_row23_cosetGeneratorStep_1142 s
  · exact g32p_row23_cosetGeneratorStep_1143 s
  · exact g32p_row23_cosetGeneratorStep_1144 s
  · exact g32p_row23_cosetGeneratorStep_1145 s
  · exact g32p_row23_cosetGeneratorStep_1146 s
  · exact g32p_row23_cosetGeneratorStep_1147 s
  · exact g32p_row23_cosetGeneratorStep_1148 s
  · exact g32p_row23_cosetGeneratorStep_1149 s
  · exact g32p_row23_cosetGeneratorStep_1150 s
  · exact g32p_row23_cosetGeneratorStep_1151 s

theorem g32p_row23_cosetBranchBlock_0071 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 71 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 71 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 71 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1136 s
  · exact g32p_row23_cosetBranchStep_1137 s
  · exact g32p_row23_cosetBranchStep_1138 s
  · exact g32p_row23_cosetBranchStep_1139 s
  · exact g32p_row23_cosetBranchStep_1140 s
  · exact g32p_row23_cosetBranchStep_1141 s
  · exact g32p_row23_cosetBranchStep_1142 s
  · exact g32p_row23_cosetBranchStep_1143 s
  · exact g32p_row23_cosetBranchStep_1144 s
  · exact g32p_row23_cosetBranchStep_1145 s
  · exact g32p_row23_cosetBranchStep_1146 s
  · exact g32p_row23_cosetBranchStep_1147 s
  · exact g32p_row23_cosetBranchStep_1148 s
  · exact g32p_row23_cosetBranchStep_1149 s
  · exact g32p_row23_cosetBranchStep_1150 s
  · exact g32p_row23_cosetBranchStep_1151 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1152 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1152) = g32p_row23_cosetRepresentatives 1152 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1152 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1152) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1152))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1152)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1152 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1152) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1152))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1152)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1153 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1153) = g32p_row23_cosetRepresentatives 1153 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1153 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1153) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1153))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1153)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1153 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1153) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1153))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1153)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1154 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1154) = g32p_row23_cosetRepresentatives 1154 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1154 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1154) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1154))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1154)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1154 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1154) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1154))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1154)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1155 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1155) = g32p_row23_cosetRepresentatives 1155 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1155 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1155) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1155))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1155)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1155 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1155) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1155))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1155)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1156 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1156) = g32p_row23_cosetRepresentatives 1156 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1156 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1156) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1156))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1156)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1156 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1156) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1156))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1156)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1157 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1157) = g32p_row23_cosetRepresentatives 1157 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1157 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1157) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1157))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1157)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1157 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1157) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1157))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1157)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1158 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1158) = g32p_row23_cosetRepresentatives 1158 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1158 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1158) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1158))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1158)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1158 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1158) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1158))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1158)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1159 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1159) = g32p_row23_cosetRepresentatives 1159 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1159 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1159) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1159))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1159)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1159 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1159) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1159))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1159)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1160 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1160) = g32p_row23_cosetRepresentatives 1160 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1160 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1160) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1160))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1160)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1160 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1160) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1160))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1160)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1161 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1161) = g32p_row23_cosetRepresentatives 1161 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1161 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1161) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1161))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1161)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1161 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1161) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1161))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1161)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1162 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1162) = g32p_row23_cosetRepresentatives 1162 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1162 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1162) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1162))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1162)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1162 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1162) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1162))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1162)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1163 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1163) = g32p_row23_cosetRepresentatives 1163 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1163 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1163) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1163))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1163)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1163 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1163) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1163))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1163)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1164 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1164) = g32p_row23_cosetRepresentatives 1164 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1164 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1164) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1164))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1164)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1164 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1164) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1164))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1164)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1165 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1165) = g32p_row23_cosetRepresentatives 1165 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1165 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1165) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1165))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1165)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1165 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1165) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1165))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1165)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1166 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1166) = g32p_row23_cosetRepresentatives 1166 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1166 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1166) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1166))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1166)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1166 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1166) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1166))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1166)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1167 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1167) = g32p_row23_cosetRepresentatives 1167 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1167 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1167) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1167))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1167)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1167 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1167) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1167))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1167)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0072 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 72 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 72 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1152
  · exact g32p_row23_cosetWord_1153
  · exact g32p_row23_cosetWord_1154
  · exact g32p_row23_cosetWord_1155
  · exact g32p_row23_cosetWord_1156
  · exact g32p_row23_cosetWord_1157
  · exact g32p_row23_cosetWord_1158
  · exact g32p_row23_cosetWord_1159
  · exact g32p_row23_cosetWord_1160
  · exact g32p_row23_cosetWord_1161
  · exact g32p_row23_cosetWord_1162
  · exact g32p_row23_cosetWord_1163
  · exact g32p_row23_cosetWord_1164
  · exact g32p_row23_cosetWord_1165
  · exact g32p_row23_cosetWord_1166
  · exact g32p_row23_cosetWord_1167

theorem g32p_row23_cosetGeneratorBlock_0072 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 72 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 72 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 72 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1152 s
  · exact g32p_row23_cosetGeneratorStep_1153 s
  · exact g32p_row23_cosetGeneratorStep_1154 s
  · exact g32p_row23_cosetGeneratorStep_1155 s
  · exact g32p_row23_cosetGeneratorStep_1156 s
  · exact g32p_row23_cosetGeneratorStep_1157 s
  · exact g32p_row23_cosetGeneratorStep_1158 s
  · exact g32p_row23_cosetGeneratorStep_1159 s
  · exact g32p_row23_cosetGeneratorStep_1160 s
  · exact g32p_row23_cosetGeneratorStep_1161 s
  · exact g32p_row23_cosetGeneratorStep_1162 s
  · exact g32p_row23_cosetGeneratorStep_1163 s
  · exact g32p_row23_cosetGeneratorStep_1164 s
  · exact g32p_row23_cosetGeneratorStep_1165 s
  · exact g32p_row23_cosetGeneratorStep_1166 s
  · exact g32p_row23_cosetGeneratorStep_1167 s

theorem g32p_row23_cosetBranchBlock_0072 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 72 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 72 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 72 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1152 s
  · exact g32p_row23_cosetBranchStep_1153 s
  · exact g32p_row23_cosetBranchStep_1154 s
  · exact g32p_row23_cosetBranchStep_1155 s
  · exact g32p_row23_cosetBranchStep_1156 s
  · exact g32p_row23_cosetBranchStep_1157 s
  · exact g32p_row23_cosetBranchStep_1158 s
  · exact g32p_row23_cosetBranchStep_1159 s
  · exact g32p_row23_cosetBranchStep_1160 s
  · exact g32p_row23_cosetBranchStep_1161 s
  · exact g32p_row23_cosetBranchStep_1162 s
  · exact g32p_row23_cosetBranchStep_1163 s
  · exact g32p_row23_cosetBranchStep_1164 s
  · exact g32p_row23_cosetBranchStep_1165 s
  · exact g32p_row23_cosetBranchStep_1166 s
  · exact g32p_row23_cosetBranchStep_1167 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1168 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1168) = g32p_row23_cosetRepresentatives 1168 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1168 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1168) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1168))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1168)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1168 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1168) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1168))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1168)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1169 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1169) = g32p_row23_cosetRepresentatives 1169 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1169 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1169) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1169))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1169)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1169 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1169) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1169))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1169)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1170 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1170) = g32p_row23_cosetRepresentatives 1170 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1170 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1170) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1170))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1170)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1170 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1170) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1170))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1170)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1171 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1171) = g32p_row23_cosetRepresentatives 1171 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1171 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1171) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1171))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1171)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1171 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1171) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1171))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1171)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1172 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1172) = g32p_row23_cosetRepresentatives 1172 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1172 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1172) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1172))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1172)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1172 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1172) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1172))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1172)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1173 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1173) = g32p_row23_cosetRepresentatives 1173 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1173 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1173) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1173))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1173)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1173 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1173) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1173))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1173)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1174 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1174) = g32p_row23_cosetRepresentatives 1174 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1174 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1174) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1174))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1174)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1174 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1174) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1174))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1174)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1175 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1175) = g32p_row23_cosetRepresentatives 1175 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1175 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1175) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1175))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1175)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1175 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1175) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1175))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1175)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1176 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1176) = g32p_row23_cosetRepresentatives 1176 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1176 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1176) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1176))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1176)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1176 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1176) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1176))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1176)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1177 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1177) = g32p_row23_cosetRepresentatives 1177 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1177 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1177) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1177))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1177)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1177 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1177) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1177))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1177)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1178 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1178) = g32p_row23_cosetRepresentatives 1178 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1178 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1178) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1178))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1178)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1178 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1178) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1178))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1178)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1179 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1179) = g32p_row23_cosetRepresentatives 1179 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1179 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1179) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1179))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1179)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1179 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1179) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1179))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1179)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1180 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1180) = g32p_row23_cosetRepresentatives 1180 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1180 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1180) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1180))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1180)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1180 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1180) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1180))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1180)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1181 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1181) = g32p_row23_cosetRepresentatives 1181 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1181 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1181) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1181))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1181)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1181 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1181) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1181))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1181)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1182 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1182) = g32p_row23_cosetRepresentatives 1182 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1182 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1182) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1182))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1182)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1182 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1182) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1182))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1182)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1183 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1183) = g32p_row23_cosetRepresentatives 1183 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1183 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1183) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1183))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1183)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1183 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1183) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1183))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1183)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0073 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 73 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 73 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1168
  · exact g32p_row23_cosetWord_1169
  · exact g32p_row23_cosetWord_1170
  · exact g32p_row23_cosetWord_1171
  · exact g32p_row23_cosetWord_1172
  · exact g32p_row23_cosetWord_1173
  · exact g32p_row23_cosetWord_1174
  · exact g32p_row23_cosetWord_1175
  · exact g32p_row23_cosetWord_1176
  · exact g32p_row23_cosetWord_1177
  · exact g32p_row23_cosetWord_1178
  · exact g32p_row23_cosetWord_1179
  · exact g32p_row23_cosetWord_1180
  · exact g32p_row23_cosetWord_1181
  · exact g32p_row23_cosetWord_1182
  · exact g32p_row23_cosetWord_1183

theorem g32p_row23_cosetGeneratorBlock_0073 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 73 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 73 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 73 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1168 s
  · exact g32p_row23_cosetGeneratorStep_1169 s
  · exact g32p_row23_cosetGeneratorStep_1170 s
  · exact g32p_row23_cosetGeneratorStep_1171 s
  · exact g32p_row23_cosetGeneratorStep_1172 s
  · exact g32p_row23_cosetGeneratorStep_1173 s
  · exact g32p_row23_cosetGeneratorStep_1174 s
  · exact g32p_row23_cosetGeneratorStep_1175 s
  · exact g32p_row23_cosetGeneratorStep_1176 s
  · exact g32p_row23_cosetGeneratorStep_1177 s
  · exact g32p_row23_cosetGeneratorStep_1178 s
  · exact g32p_row23_cosetGeneratorStep_1179 s
  · exact g32p_row23_cosetGeneratorStep_1180 s
  · exact g32p_row23_cosetGeneratorStep_1181 s
  · exact g32p_row23_cosetGeneratorStep_1182 s
  · exact g32p_row23_cosetGeneratorStep_1183 s

theorem g32p_row23_cosetBranchBlock_0073 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 73 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 73 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 73 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1168 s
  · exact g32p_row23_cosetBranchStep_1169 s
  · exact g32p_row23_cosetBranchStep_1170 s
  · exact g32p_row23_cosetBranchStep_1171 s
  · exact g32p_row23_cosetBranchStep_1172 s
  · exact g32p_row23_cosetBranchStep_1173 s
  · exact g32p_row23_cosetBranchStep_1174 s
  · exact g32p_row23_cosetBranchStep_1175 s
  · exact g32p_row23_cosetBranchStep_1176 s
  · exact g32p_row23_cosetBranchStep_1177 s
  · exact g32p_row23_cosetBranchStep_1178 s
  · exact g32p_row23_cosetBranchStep_1179 s
  · exact g32p_row23_cosetBranchStep_1180 s
  · exact g32p_row23_cosetBranchStep_1181 s
  · exact g32p_row23_cosetBranchStep_1182 s
  · exact g32p_row23_cosetBranchStep_1183 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1184 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1184) = g32p_row23_cosetRepresentatives 1184 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1184 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1184) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1184))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1184)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1184 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1184) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1184))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1184)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1185 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1185) = g32p_row23_cosetRepresentatives 1185 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1185 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1185) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1185))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1185)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1185 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1185) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1185))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1185)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1186 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1186) = g32p_row23_cosetRepresentatives 1186 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1186 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1186) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1186))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1186)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1186 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1186) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1186))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1186)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1187 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1187) = g32p_row23_cosetRepresentatives 1187 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1187 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1187) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1187))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1187)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1187 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1187) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1187))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1187)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1188 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1188) = g32p_row23_cosetRepresentatives 1188 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1188 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1188) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1188))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1188)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1188 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1188) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1188))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1188)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1189 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1189) = g32p_row23_cosetRepresentatives 1189 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1189 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1189) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1189))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1189)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1189 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1189) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1189))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1189)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1190 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1190) = g32p_row23_cosetRepresentatives 1190 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1190 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1190) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1190))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1190)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1190 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1190) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1190))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1190)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1191 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1191) = g32p_row23_cosetRepresentatives 1191 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1191 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1191) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1191))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1191)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1191 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1191) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1191))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1191)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1192 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1192) = g32p_row23_cosetRepresentatives 1192 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1192 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1192) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1192))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1192)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1192 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1192) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1192))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1192)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1193 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1193) = g32p_row23_cosetRepresentatives 1193 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1193 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1193) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1193))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1193)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1193 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1193) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1193))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1193)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1194 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1194) = g32p_row23_cosetRepresentatives 1194 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1194 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1194) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1194))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1194)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1194 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1194) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1194))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1194)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1195 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1195) = g32p_row23_cosetRepresentatives 1195 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1195 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1195) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1195))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1195)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1195 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1195) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1195))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1195)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1196 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1196) = g32p_row23_cosetRepresentatives 1196 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1196 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1196) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1196))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1196)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1196 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1196) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1196))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1196)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1197 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1197) = g32p_row23_cosetRepresentatives 1197 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1197 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1197) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1197))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1197)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1197 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1197) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1197))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1197)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1198 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1198) = g32p_row23_cosetRepresentatives 1198 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1198 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1198) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1198))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1198)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1198 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1198) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1198))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1198)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1199 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1199) = g32p_row23_cosetRepresentatives 1199 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1199 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1199) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1199))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1199)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1199 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1199) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1199))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1199)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0074 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 74 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 74 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1184
  · exact g32p_row23_cosetWord_1185
  · exact g32p_row23_cosetWord_1186
  · exact g32p_row23_cosetWord_1187
  · exact g32p_row23_cosetWord_1188
  · exact g32p_row23_cosetWord_1189
  · exact g32p_row23_cosetWord_1190
  · exact g32p_row23_cosetWord_1191
  · exact g32p_row23_cosetWord_1192
  · exact g32p_row23_cosetWord_1193
  · exact g32p_row23_cosetWord_1194
  · exact g32p_row23_cosetWord_1195
  · exact g32p_row23_cosetWord_1196
  · exact g32p_row23_cosetWord_1197
  · exact g32p_row23_cosetWord_1198
  · exact g32p_row23_cosetWord_1199

theorem g32p_row23_cosetGeneratorBlock_0074 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 74 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 74 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 74 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1184 s
  · exact g32p_row23_cosetGeneratorStep_1185 s
  · exact g32p_row23_cosetGeneratorStep_1186 s
  · exact g32p_row23_cosetGeneratorStep_1187 s
  · exact g32p_row23_cosetGeneratorStep_1188 s
  · exact g32p_row23_cosetGeneratorStep_1189 s
  · exact g32p_row23_cosetGeneratorStep_1190 s
  · exact g32p_row23_cosetGeneratorStep_1191 s
  · exact g32p_row23_cosetGeneratorStep_1192 s
  · exact g32p_row23_cosetGeneratorStep_1193 s
  · exact g32p_row23_cosetGeneratorStep_1194 s
  · exact g32p_row23_cosetGeneratorStep_1195 s
  · exact g32p_row23_cosetGeneratorStep_1196 s
  · exact g32p_row23_cosetGeneratorStep_1197 s
  · exact g32p_row23_cosetGeneratorStep_1198 s
  · exact g32p_row23_cosetGeneratorStep_1199 s

theorem g32p_row23_cosetBranchBlock_0074 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 74 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 74 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 74 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1184 s
  · exact g32p_row23_cosetBranchStep_1185 s
  · exact g32p_row23_cosetBranchStep_1186 s
  · exact g32p_row23_cosetBranchStep_1187 s
  · exact g32p_row23_cosetBranchStep_1188 s
  · exact g32p_row23_cosetBranchStep_1189 s
  · exact g32p_row23_cosetBranchStep_1190 s
  · exact g32p_row23_cosetBranchStep_1191 s
  · exact g32p_row23_cosetBranchStep_1192 s
  · exact g32p_row23_cosetBranchStep_1193 s
  · exact g32p_row23_cosetBranchStep_1194 s
  · exact g32p_row23_cosetBranchStep_1195 s
  · exact g32p_row23_cosetBranchStep_1196 s
  · exact g32p_row23_cosetBranchStep_1197 s
  · exact g32p_row23_cosetBranchStep_1198 s
  · exact g32p_row23_cosetBranchStep_1199 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1200 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1200) = g32p_row23_cosetRepresentatives 1200 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1200 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1200) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1200))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1200)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1200 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1200) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1200))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1200)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1201 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1201) = g32p_row23_cosetRepresentatives 1201 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1201 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1201) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1201))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1201)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1201 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1201) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1201))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1201)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1202 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1202) = g32p_row23_cosetRepresentatives 1202 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1202 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1202) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1202))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1202)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1202 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1202) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1202))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1202)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1203 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1203) = g32p_row23_cosetRepresentatives 1203 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1203 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1203) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1203))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1203)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1203 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1203) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1203))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1203)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1204 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1204) = g32p_row23_cosetRepresentatives 1204 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1204 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1204) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1204))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1204)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1204 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1204) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1204))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1204)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1205 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1205) = g32p_row23_cosetRepresentatives 1205 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1205 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1205) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1205))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1205)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1205 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1205) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1205))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1205)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1206 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1206) = g32p_row23_cosetRepresentatives 1206 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1206 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1206) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1206))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1206)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1206 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1206) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1206))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1206)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1207 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1207) = g32p_row23_cosetRepresentatives 1207 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1207 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1207) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1207))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1207)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1207 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1207) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1207))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1207)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1208 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1208) = g32p_row23_cosetRepresentatives 1208 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1208 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1208) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1208))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1208)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1208 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1208) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1208))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1208)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1209 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1209) = g32p_row23_cosetRepresentatives 1209 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1209 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1209) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1209))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1209)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1209 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1209) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1209))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1209)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1210 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1210) = g32p_row23_cosetRepresentatives 1210 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1210 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1210) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1210))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1210)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1210 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1210) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1210))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1210)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1211 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1211) = g32p_row23_cosetRepresentatives 1211 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1211 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1211) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1211))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1211)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1211 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1211) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1211))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1211)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1212 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1212) = g32p_row23_cosetRepresentatives 1212 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1212 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1212) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1212))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1212)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1212 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1212) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1212))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1212)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1213 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1213) = g32p_row23_cosetRepresentatives 1213 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1213 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1213) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1213))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1213)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1213 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1213) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1213))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1213)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1214 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1214) = g32p_row23_cosetRepresentatives 1214 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1214 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1214) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1214))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1214)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1214 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1214) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1214))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1214)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1215 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1215) = g32p_row23_cosetRepresentatives 1215 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1215 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1215) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1215))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1215)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1215 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1215) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1215))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1215)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0075 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 75 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 75 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1200
  · exact g32p_row23_cosetWord_1201
  · exact g32p_row23_cosetWord_1202
  · exact g32p_row23_cosetWord_1203
  · exact g32p_row23_cosetWord_1204
  · exact g32p_row23_cosetWord_1205
  · exact g32p_row23_cosetWord_1206
  · exact g32p_row23_cosetWord_1207
  · exact g32p_row23_cosetWord_1208
  · exact g32p_row23_cosetWord_1209
  · exact g32p_row23_cosetWord_1210
  · exact g32p_row23_cosetWord_1211
  · exact g32p_row23_cosetWord_1212
  · exact g32p_row23_cosetWord_1213
  · exact g32p_row23_cosetWord_1214
  · exact g32p_row23_cosetWord_1215

theorem g32p_row23_cosetGeneratorBlock_0075 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 75 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 75 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 75 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1200 s
  · exact g32p_row23_cosetGeneratorStep_1201 s
  · exact g32p_row23_cosetGeneratorStep_1202 s
  · exact g32p_row23_cosetGeneratorStep_1203 s
  · exact g32p_row23_cosetGeneratorStep_1204 s
  · exact g32p_row23_cosetGeneratorStep_1205 s
  · exact g32p_row23_cosetGeneratorStep_1206 s
  · exact g32p_row23_cosetGeneratorStep_1207 s
  · exact g32p_row23_cosetGeneratorStep_1208 s
  · exact g32p_row23_cosetGeneratorStep_1209 s
  · exact g32p_row23_cosetGeneratorStep_1210 s
  · exact g32p_row23_cosetGeneratorStep_1211 s
  · exact g32p_row23_cosetGeneratorStep_1212 s
  · exact g32p_row23_cosetGeneratorStep_1213 s
  · exact g32p_row23_cosetGeneratorStep_1214 s
  · exact g32p_row23_cosetGeneratorStep_1215 s

theorem g32p_row23_cosetBranchBlock_0075 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 75 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 75 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 75 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1200 s
  · exact g32p_row23_cosetBranchStep_1201 s
  · exact g32p_row23_cosetBranchStep_1202 s
  · exact g32p_row23_cosetBranchStep_1203 s
  · exact g32p_row23_cosetBranchStep_1204 s
  · exact g32p_row23_cosetBranchStep_1205 s
  · exact g32p_row23_cosetBranchStep_1206 s
  · exact g32p_row23_cosetBranchStep_1207 s
  · exact g32p_row23_cosetBranchStep_1208 s
  · exact g32p_row23_cosetBranchStep_1209 s
  · exact g32p_row23_cosetBranchStep_1210 s
  · exact g32p_row23_cosetBranchStep_1211 s
  · exact g32p_row23_cosetBranchStep_1212 s
  · exact g32p_row23_cosetBranchStep_1213 s
  · exact g32p_row23_cosetBranchStep_1214 s
  · exact g32p_row23_cosetBranchStep_1215 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1216 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1216) = g32p_row23_cosetRepresentatives 1216 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1216 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1216) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1216))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1216)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1216 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1216) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1216))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1216)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1217 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1217) = g32p_row23_cosetRepresentatives 1217 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1217 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1217) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1217))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1217)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1217 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1217) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1217))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1217)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1218 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1218) = g32p_row23_cosetRepresentatives 1218 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1218 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1218) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1218))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1218)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1218 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1218) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1218))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1218)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1219 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1219) = g32p_row23_cosetRepresentatives 1219 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1219 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1219) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1219))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1219)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1219 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1219) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1219))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1219)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1220 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1220) = g32p_row23_cosetRepresentatives 1220 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1220 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1220) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1220))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1220)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1220 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1220) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1220))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1220)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1221 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1221) = g32p_row23_cosetRepresentatives 1221 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1221 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1221) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1221))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1221)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1221 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1221) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1221))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1221)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1222 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1222) = g32p_row23_cosetRepresentatives 1222 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1222 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1222) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1222))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1222)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1222 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1222) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1222))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1222)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1223 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1223) = g32p_row23_cosetRepresentatives 1223 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1223 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1223) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1223))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1223)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1223 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1223) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1223))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1223)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1224 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1224) = g32p_row23_cosetRepresentatives 1224 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1224 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1224) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1224))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1224)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1224 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1224) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1224))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1224)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1225 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1225) = g32p_row23_cosetRepresentatives 1225 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1225 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1225) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1225))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1225)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1225 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1225) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1225))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1225)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1226 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1226) = g32p_row23_cosetRepresentatives 1226 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1226 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1226) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1226))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1226)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1226 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1226) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1226))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1226)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1227 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1227) = g32p_row23_cosetRepresentatives 1227 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1227 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1227) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1227))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1227)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1227 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1227) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1227))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1227)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1228 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1228) = g32p_row23_cosetRepresentatives 1228 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1228 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1228) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1228))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1228)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1228 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1228) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1228))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1228)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1229 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1229) = g32p_row23_cosetRepresentatives 1229 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1229 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1229) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1229))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1229)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1229 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1229) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1229))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1229)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1230 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1230) = g32p_row23_cosetRepresentatives 1230 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1230 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1230) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1230))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1230)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1230 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1230) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1230))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1230)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1231 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1231) = g32p_row23_cosetRepresentatives 1231 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1231 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1231) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1231))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1231)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1231 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1231) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1231))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1231)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0076 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 76 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 76 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1216
  · exact g32p_row23_cosetWord_1217
  · exact g32p_row23_cosetWord_1218
  · exact g32p_row23_cosetWord_1219
  · exact g32p_row23_cosetWord_1220
  · exact g32p_row23_cosetWord_1221
  · exact g32p_row23_cosetWord_1222
  · exact g32p_row23_cosetWord_1223
  · exact g32p_row23_cosetWord_1224
  · exact g32p_row23_cosetWord_1225
  · exact g32p_row23_cosetWord_1226
  · exact g32p_row23_cosetWord_1227
  · exact g32p_row23_cosetWord_1228
  · exact g32p_row23_cosetWord_1229
  · exact g32p_row23_cosetWord_1230
  · exact g32p_row23_cosetWord_1231

theorem g32p_row23_cosetGeneratorBlock_0076 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 76 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 76 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 76 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1216 s
  · exact g32p_row23_cosetGeneratorStep_1217 s
  · exact g32p_row23_cosetGeneratorStep_1218 s
  · exact g32p_row23_cosetGeneratorStep_1219 s
  · exact g32p_row23_cosetGeneratorStep_1220 s
  · exact g32p_row23_cosetGeneratorStep_1221 s
  · exact g32p_row23_cosetGeneratorStep_1222 s
  · exact g32p_row23_cosetGeneratorStep_1223 s
  · exact g32p_row23_cosetGeneratorStep_1224 s
  · exact g32p_row23_cosetGeneratorStep_1225 s
  · exact g32p_row23_cosetGeneratorStep_1226 s
  · exact g32p_row23_cosetGeneratorStep_1227 s
  · exact g32p_row23_cosetGeneratorStep_1228 s
  · exact g32p_row23_cosetGeneratorStep_1229 s
  · exact g32p_row23_cosetGeneratorStep_1230 s
  · exact g32p_row23_cosetGeneratorStep_1231 s

theorem g32p_row23_cosetBranchBlock_0076 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 76 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 76 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 76 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1216 s
  · exact g32p_row23_cosetBranchStep_1217 s
  · exact g32p_row23_cosetBranchStep_1218 s
  · exact g32p_row23_cosetBranchStep_1219 s
  · exact g32p_row23_cosetBranchStep_1220 s
  · exact g32p_row23_cosetBranchStep_1221 s
  · exact g32p_row23_cosetBranchStep_1222 s
  · exact g32p_row23_cosetBranchStep_1223 s
  · exact g32p_row23_cosetBranchStep_1224 s
  · exact g32p_row23_cosetBranchStep_1225 s
  · exact g32p_row23_cosetBranchStep_1226 s
  · exact g32p_row23_cosetBranchStep_1227 s
  · exact g32p_row23_cosetBranchStep_1228 s
  · exact g32p_row23_cosetBranchStep_1229 s
  · exact g32p_row23_cosetBranchStep_1230 s
  · exact g32p_row23_cosetBranchStep_1231 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1232 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1232) = g32p_row23_cosetRepresentatives 1232 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1232 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1232) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1232))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1232)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1232 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1232) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1232))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1232)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1233 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1233) = g32p_row23_cosetRepresentatives 1233 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1233 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1233) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1233))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1233)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1233 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1233) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1233))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1233)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1234 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1234) = g32p_row23_cosetRepresentatives 1234 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1234 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1234) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1234))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1234)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1234 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1234) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1234))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1234)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1235 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1235) = g32p_row23_cosetRepresentatives 1235 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1235 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1235) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1235))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1235)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1235 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1235) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1235))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1235)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1236 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1236) = g32p_row23_cosetRepresentatives 1236 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1236 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1236) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1236))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1236)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1236 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1236) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1236))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1236)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1237 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1237) = g32p_row23_cosetRepresentatives 1237 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1237 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1237) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1237))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1237)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1237 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1237) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1237))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1237)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1238 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1238) = g32p_row23_cosetRepresentatives 1238 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1238 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1238) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1238))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1238)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1238 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1238) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1238))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1238)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1239 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1239) = g32p_row23_cosetRepresentatives 1239 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1239 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1239) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1239))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1239)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1239 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1239) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1239))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1239)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1240 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1240) = g32p_row23_cosetRepresentatives 1240 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1240 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1240) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1240))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1240)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1240 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1240) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1240))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1240)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1241 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1241) = g32p_row23_cosetRepresentatives 1241 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1241 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1241) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1241))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1241)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1241 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1241) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1241))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1241)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1242 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1242) = g32p_row23_cosetRepresentatives 1242 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1242 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1242) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1242))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1242)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1242 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1242) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1242))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1242)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1243 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1243) = g32p_row23_cosetRepresentatives 1243 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1243 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1243) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1243))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1243)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1243 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1243) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1243))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1243)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1244 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1244) = g32p_row23_cosetRepresentatives 1244 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1244 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1244) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1244))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1244)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1244 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1244) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1244))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1244)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1245 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1245) = g32p_row23_cosetRepresentatives 1245 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1245 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1245) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1245))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1245)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1245 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1245) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1245))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1245)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1246 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1246) = g32p_row23_cosetRepresentatives 1246 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1246 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1246) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1246))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1246)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1246 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1246) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1246))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1246)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1247 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1247) = g32p_row23_cosetRepresentatives 1247 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1247 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1247) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1247))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1247)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1247 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1247) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1247))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1247)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0077 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 77 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 77 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1232
  · exact g32p_row23_cosetWord_1233
  · exact g32p_row23_cosetWord_1234
  · exact g32p_row23_cosetWord_1235
  · exact g32p_row23_cosetWord_1236
  · exact g32p_row23_cosetWord_1237
  · exact g32p_row23_cosetWord_1238
  · exact g32p_row23_cosetWord_1239
  · exact g32p_row23_cosetWord_1240
  · exact g32p_row23_cosetWord_1241
  · exact g32p_row23_cosetWord_1242
  · exact g32p_row23_cosetWord_1243
  · exact g32p_row23_cosetWord_1244
  · exact g32p_row23_cosetWord_1245
  · exact g32p_row23_cosetWord_1246
  · exact g32p_row23_cosetWord_1247

theorem g32p_row23_cosetGeneratorBlock_0077 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 77 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 77 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 77 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1232 s
  · exact g32p_row23_cosetGeneratorStep_1233 s
  · exact g32p_row23_cosetGeneratorStep_1234 s
  · exact g32p_row23_cosetGeneratorStep_1235 s
  · exact g32p_row23_cosetGeneratorStep_1236 s
  · exact g32p_row23_cosetGeneratorStep_1237 s
  · exact g32p_row23_cosetGeneratorStep_1238 s
  · exact g32p_row23_cosetGeneratorStep_1239 s
  · exact g32p_row23_cosetGeneratorStep_1240 s
  · exact g32p_row23_cosetGeneratorStep_1241 s
  · exact g32p_row23_cosetGeneratorStep_1242 s
  · exact g32p_row23_cosetGeneratorStep_1243 s
  · exact g32p_row23_cosetGeneratorStep_1244 s
  · exact g32p_row23_cosetGeneratorStep_1245 s
  · exact g32p_row23_cosetGeneratorStep_1246 s
  · exact g32p_row23_cosetGeneratorStep_1247 s

theorem g32p_row23_cosetBranchBlock_0077 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 77 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 77 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 77 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1232 s
  · exact g32p_row23_cosetBranchStep_1233 s
  · exact g32p_row23_cosetBranchStep_1234 s
  · exact g32p_row23_cosetBranchStep_1235 s
  · exact g32p_row23_cosetBranchStep_1236 s
  · exact g32p_row23_cosetBranchStep_1237 s
  · exact g32p_row23_cosetBranchStep_1238 s
  · exact g32p_row23_cosetBranchStep_1239 s
  · exact g32p_row23_cosetBranchStep_1240 s
  · exact g32p_row23_cosetBranchStep_1241 s
  · exact g32p_row23_cosetBranchStep_1242 s
  · exact g32p_row23_cosetBranchStep_1243 s
  · exact g32p_row23_cosetBranchStep_1244 s
  · exact g32p_row23_cosetBranchStep_1245 s
  · exact g32p_row23_cosetBranchStep_1246 s
  · exact g32p_row23_cosetBranchStep_1247 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1248 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1248) = g32p_row23_cosetRepresentatives 1248 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1248 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1248) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1248))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1248)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1248 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1248) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1248))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1248)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1249 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1249) = g32p_row23_cosetRepresentatives 1249 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1249 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1249) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1249))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1249)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1249 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1249) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1249))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1249)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1250 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1250) = g32p_row23_cosetRepresentatives 1250 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1250 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1250) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1250))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1250)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1250 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1250) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1250))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1250)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1251 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1251) = g32p_row23_cosetRepresentatives 1251 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1251 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1251) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1251))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1251)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1251 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1251) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1251))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1251)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1252 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1252) = g32p_row23_cosetRepresentatives 1252 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1252 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1252) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1252))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1252)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1252 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1252) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1252))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1252)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1253 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1253) = g32p_row23_cosetRepresentatives 1253 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1253 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1253) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1253))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1253)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1253 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1253) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1253))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1253)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1254 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1254) = g32p_row23_cosetRepresentatives 1254 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1254 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1254) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1254))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1254)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1254 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1254) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1254))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1254)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1255 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1255) = g32p_row23_cosetRepresentatives 1255 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1255 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1255) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1255))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1255)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1255 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1255) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1255))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1255)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1256 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1256) = g32p_row23_cosetRepresentatives 1256 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1256) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1256))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1256)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1256) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1256))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1256)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1257 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1257) = g32p_row23_cosetRepresentatives 1257 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1257) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1257))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1257)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1257) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1257))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1257)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1258 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1258) = g32p_row23_cosetRepresentatives 1258 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1258) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1258))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1258)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1258) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1258))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1258)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1259 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1259) = g32p_row23_cosetRepresentatives 1259 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1259) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1259))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1259)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1259) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1259))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1259)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1260 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1260) = g32p_row23_cosetRepresentatives 1260 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1260) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1260))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1260)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1260) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1260))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1260)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1261 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1261) = g32p_row23_cosetRepresentatives 1261 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1261) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1261))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1261)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1261) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1261))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1261)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1262 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1262) = g32p_row23_cosetRepresentatives 1262 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1262) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1262))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1262)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1262) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1262))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1262)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1263 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1263) = g32p_row23_cosetRepresentatives 1263 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1263) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1263))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1263)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1263) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1263))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1263)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0078 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 78 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 78 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1248
  · exact g32p_row23_cosetWord_1249
  · exact g32p_row23_cosetWord_1250
  · exact g32p_row23_cosetWord_1251
  · exact g32p_row23_cosetWord_1252
  · exact g32p_row23_cosetWord_1253
  · exact g32p_row23_cosetWord_1254
  · exact g32p_row23_cosetWord_1255
  · exact g32p_row23_cosetWord_1256
  · exact g32p_row23_cosetWord_1257
  · exact g32p_row23_cosetWord_1258
  · exact g32p_row23_cosetWord_1259
  · exact g32p_row23_cosetWord_1260
  · exact g32p_row23_cosetWord_1261
  · exact g32p_row23_cosetWord_1262
  · exact g32p_row23_cosetWord_1263

theorem g32p_row23_cosetGeneratorBlock_0078 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 78 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 78 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 78 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1248 s
  · exact g32p_row23_cosetGeneratorStep_1249 s
  · exact g32p_row23_cosetGeneratorStep_1250 s
  · exact g32p_row23_cosetGeneratorStep_1251 s
  · exact g32p_row23_cosetGeneratorStep_1252 s
  · exact g32p_row23_cosetGeneratorStep_1253 s
  · exact g32p_row23_cosetGeneratorStep_1254 s
  · exact g32p_row23_cosetGeneratorStep_1255 s
  · exact g32p_row23_cosetGeneratorStep_1256 s
  · exact g32p_row23_cosetGeneratorStep_1257 s
  · exact g32p_row23_cosetGeneratorStep_1258 s
  · exact g32p_row23_cosetGeneratorStep_1259 s
  · exact g32p_row23_cosetGeneratorStep_1260 s
  · exact g32p_row23_cosetGeneratorStep_1261 s
  · exact g32p_row23_cosetGeneratorStep_1262 s
  · exact g32p_row23_cosetGeneratorStep_1263 s

theorem g32p_row23_cosetBranchBlock_0078 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 78 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 78 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 78 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1248 s
  · exact g32p_row23_cosetBranchStep_1249 s
  · exact g32p_row23_cosetBranchStep_1250 s
  · exact g32p_row23_cosetBranchStep_1251 s
  · exact g32p_row23_cosetBranchStep_1252 s
  · exact g32p_row23_cosetBranchStep_1253 s
  · exact g32p_row23_cosetBranchStep_1254 s
  · exact g32p_row23_cosetBranchStep_1255 s
  · exact g32p_row23_cosetBranchStep_1256 s
  · exact g32p_row23_cosetBranchStep_1257 s
  · exact g32p_row23_cosetBranchStep_1258 s
  · exact g32p_row23_cosetBranchStep_1259 s
  · exact g32p_row23_cosetBranchStep_1260 s
  · exact g32p_row23_cosetBranchStep_1261 s
  · exact g32p_row23_cosetBranchStep_1262 s
  · exact g32p_row23_cosetBranchStep_1263 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row23_cosetWord_1264 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1264) = g32p_row23_cosetRepresentatives 1264 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1264) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1264))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1264)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1264) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1264))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1264)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1265 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1265) = g32p_row23_cosetRepresentatives 1265 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1265) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1265))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1265)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1265) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1265))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1265)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1266 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1266) = g32p_row23_cosetRepresentatives 1266 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1266) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1266))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1266)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1266) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1266))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1266)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1267 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1267) = g32p_row23_cosetRepresentatives 1267 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1267) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1267))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1267)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1267) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1267))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1267)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1268 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1268) = g32p_row23_cosetRepresentatives 1268 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1268) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1268))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1268)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1268) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1268))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1268)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1269 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1269) = g32p_row23_cosetRepresentatives 1269 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1269) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1269))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1269)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1269) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1269))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1269)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1270 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1270) = g32p_row23_cosetRepresentatives 1270 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1270) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1270))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1270)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1270) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1270))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1270)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1271 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1271) = g32p_row23_cosetRepresentatives 1271 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1271) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1271))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1271)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1271) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1271))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1271)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1272 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1272) = g32p_row23_cosetRepresentatives 1272 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1272) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1272))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1272)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1272) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1272))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1272)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1273 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1273) = g32p_row23_cosetRepresentatives 1273 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1273) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1273))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1273)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1273) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1273))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1273)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1274 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1274) = g32p_row23_cosetRepresentatives 1274 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1274) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1274))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1274)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1274) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1274))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1274)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1275 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1275) = g32p_row23_cosetRepresentatives 1275 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1275) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1275))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1275)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1275) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1275))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1275)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1276 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1276) = g32p_row23_cosetRepresentatives 1276 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1276) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1276))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1276)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1276) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1276))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1276)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1277 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1277) = g32p_row23_cosetRepresentatives 1277 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1277) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1277))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1277)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1277) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1277))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1277)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1278 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1278) = g32p_row23_cosetRepresentatives 1278 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1278) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1278))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1278)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1278) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1278))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1278)) := by
  decide +kernel

theorem g32p_row23_cosetWord_1279 :
    g32p_archiveIntegralWord (g32p_row23_cosetWords 1279) = g32p_row23_cosetRepresentatives 1279 := by
  decide +kernel

theorem g32p_row23_cosetGeneratorStep_1279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives 1279) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s 1279))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s 1279)) := by
  decide +kernel

theorem g32p_row23_cosetBranchStep_1279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives 1279) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s 1279))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s 1279)) := by
  decide +kernel

theorem g32p_row23_cosetWordBlock_0079 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row23_cosetWords (g32p_finBlockIndex 1440 79 r)) = g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 79 r) := by
  fin_cases r
  · exact g32p_row23_cosetWord_1264
  · exact g32p_row23_cosetWord_1265
  · exact g32p_row23_cosetWord_1266
  · exact g32p_row23_cosetWord_1267
  · exact g32p_row23_cosetWord_1268
  · exact g32p_row23_cosetWord_1269
  · exact g32p_row23_cosetWord_1270
  · exact g32p_row23_cosetWord_1271
  · exact g32p_row23_cosetWord_1272
  · exact g32p_row23_cosetWord_1273
  · exact g32p_row23_cosetWord_1274
  · exact g32p_row23_cosetWord_1275
  · exact g32p_row23_cosetWord_1276
  · exact g32p_row23_cosetWord_1277
  · exact g32p_row23_cosetWord_1278
  · exact g32p_row23_cosetWord_1279

theorem g32p_row23_cosetGeneratorBlock_0079 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 79 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetGeneratorNext s (g32p_finBlockIndex 1440 79 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetGeneratorFactor s (g32p_finBlockIndex 1440 79 r))) := by
  fin_cases r
  · exact g32p_row23_cosetGeneratorStep_1264 s
  · exact g32p_row23_cosetGeneratorStep_1265 s
  · exact g32p_row23_cosetGeneratorStep_1266 s
  · exact g32p_row23_cosetGeneratorStep_1267 s
  · exact g32p_row23_cosetGeneratorStep_1268 s
  · exact g32p_row23_cosetGeneratorStep_1269 s
  · exact g32p_row23_cosetGeneratorStep_1270 s
  · exact g32p_row23_cosetGeneratorStep_1271 s
  · exact g32p_row23_cosetGeneratorStep_1272 s
  · exact g32p_row23_cosetGeneratorStep_1273 s
  · exact g32p_row23_cosetGeneratorStep_1274 s
  · exact g32p_row23_cosetGeneratorStep_1275 s
  · exact g32p_row23_cosetGeneratorStep_1276 s
  · exact g32p_row23_cosetGeneratorStep_1277 s
  · exact g32p_row23_cosetGeneratorStep_1278 s
  · exact g32p_row23_cosetGeneratorStep_1279 s

theorem g32p_row23_cosetBranchBlock_0079 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row23_cosetBranchMatrices s) (g32p_row23_cosetRepresentatives (g32p_finBlockIndex 1440 79 r)) =
      HurwitzPrymRex_mmul (g32p_row23_cosetRepresentatives (g32p_row23_cosetBranchNext s (g32p_finBlockIndex 1440 79 r)))
        (g32p_row23_groupNodes (g32p_row23_cosetBranchFactor s (g32p_finBlockIndex 1440 79 r))) := by
  fin_cases r
  · exact g32p_row23_cosetBranchStep_1264 s
  · exact g32p_row23_cosetBranchStep_1265 s
  · exact g32p_row23_cosetBranchStep_1266 s
  · exact g32p_row23_cosetBranchStep_1267 s
  · exact g32p_row23_cosetBranchStep_1268 s
  · exact g32p_row23_cosetBranchStep_1269 s
  · exact g32p_row23_cosetBranchStep_1270 s
  · exact g32p_row23_cosetBranchStep_1271 s
  · exact g32p_row23_cosetBranchStep_1272 s
  · exact g32p_row23_cosetBranchStep_1273 s
  · exact g32p_row23_cosetBranchStep_1274 s
  · exact g32p_row23_cosetBranchStep_1275 s
  · exact g32p_row23_cosetBranchStep_1276 s
  · exact g32p_row23_cosetBranchStep_1277 s
  · exact g32p_row23_cosetBranchStep_1278 s
  · exact g32p_row23_cosetBranchStep_1279 s


end HodgeLean.Foundations.Program

end
