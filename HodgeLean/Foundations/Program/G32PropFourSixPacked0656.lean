import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness06CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0652
import HodgeLean.Foundations.Program.G32PropFourSixPacked0653
import HodgeLean.Foundations.Program.G32PropFourSixPacked0654
import HodgeLean.Foundations.Program.G32PropFourSixPacked0655
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow06
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetWord_1024 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1024) = g32p_row06_cosetRepresentatives 1024 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1024 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1024) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1024))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1024)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1024 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1024) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1024))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1024)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1025 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1025) = g32p_row06_cosetRepresentatives 1025 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1025 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1025) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1025))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1025)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1025 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1025) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1025))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1025)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1026 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1026) = g32p_row06_cosetRepresentatives 1026 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1026 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1026) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1026))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1026)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1026 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1026) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1026))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1026)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1027 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1027) = g32p_row06_cosetRepresentatives 1027 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1027 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1027) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1027))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1027)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1027 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1027) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1027))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1027)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1028 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1028) = g32p_row06_cosetRepresentatives 1028 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1028 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1028) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1028))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1028)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1028 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1028) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1028))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1028)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1029 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1029) = g32p_row06_cosetRepresentatives 1029 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1029 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1029) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1029))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1029)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1029 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1029) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1029))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1029)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1030 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1030) = g32p_row06_cosetRepresentatives 1030 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1030 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1030) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1030))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1030)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1030 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1030) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1030))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1030)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1031 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1031) = g32p_row06_cosetRepresentatives 1031 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1031 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1031) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1031))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1031)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1031 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1031) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1031))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1031)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1032 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1032) = g32p_row06_cosetRepresentatives 1032 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1032 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1032) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1032))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1032)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1032 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1032) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1032))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1032)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1033 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1033) = g32p_row06_cosetRepresentatives 1033 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1033 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1033) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1033))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1033)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1033 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1033) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1033))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1033)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1034 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1034) = g32p_row06_cosetRepresentatives 1034 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1034 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1034) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1034))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1034)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1034 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1034) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1034))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1034)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1035 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1035) = g32p_row06_cosetRepresentatives 1035 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1035 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1035) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1035))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1035)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1035 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1035) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1035))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1035)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1036 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1036) = g32p_row06_cosetRepresentatives 1036 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1036 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1036) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1036))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1036)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1036 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1036) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1036))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1036)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1037 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1037) = g32p_row06_cosetRepresentatives 1037 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1037 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1037) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1037))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1037)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1037 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1037) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1037))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1037)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1038 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1038) = g32p_row06_cosetRepresentatives 1038 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1038 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1038) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1038))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1038)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1038 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1038) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1038))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1038)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1039 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1039) = g32p_row06_cosetRepresentatives 1039 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1039 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1039) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1039))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1039)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1039 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1039) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1039))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1039)) := by
  decide +kernel

theorem g32p_row06_cosetWordBlock_0064 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row06_cosetWords (g32p_finBlockIndex 1080 64 r)) = g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 64 r) := by
  fin_cases r
  · exact g32p_row06_cosetWord_1024
  · exact g32p_row06_cosetWord_1025
  · exact g32p_row06_cosetWord_1026
  · exact g32p_row06_cosetWord_1027
  · exact g32p_row06_cosetWord_1028
  · exact g32p_row06_cosetWord_1029
  · exact g32p_row06_cosetWord_1030
  · exact g32p_row06_cosetWord_1031
  · exact g32p_row06_cosetWord_1032
  · exact g32p_row06_cosetWord_1033
  · exact g32p_row06_cosetWord_1034
  · exact g32p_row06_cosetWord_1035
  · exact g32p_row06_cosetWord_1036
  · exact g32p_row06_cosetWord_1037
  · exact g32p_row06_cosetWord_1038
  · exact g32p_row06_cosetWord_1039

theorem g32p_row06_cosetGeneratorBlock_0064 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 64 r)) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s (g32p_finBlockIndex 1080 64 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s (g32p_finBlockIndex 1080 64 r))) := by
  fin_cases r
  · exact g32p_row06_cosetGeneratorStep_1024 s
  · exact g32p_row06_cosetGeneratorStep_1025 s
  · exact g32p_row06_cosetGeneratorStep_1026 s
  · exact g32p_row06_cosetGeneratorStep_1027 s
  · exact g32p_row06_cosetGeneratorStep_1028 s
  · exact g32p_row06_cosetGeneratorStep_1029 s
  · exact g32p_row06_cosetGeneratorStep_1030 s
  · exact g32p_row06_cosetGeneratorStep_1031 s
  · exact g32p_row06_cosetGeneratorStep_1032 s
  · exact g32p_row06_cosetGeneratorStep_1033 s
  · exact g32p_row06_cosetGeneratorStep_1034 s
  · exact g32p_row06_cosetGeneratorStep_1035 s
  · exact g32p_row06_cosetGeneratorStep_1036 s
  · exact g32p_row06_cosetGeneratorStep_1037 s
  · exact g32p_row06_cosetGeneratorStep_1038 s
  · exact g32p_row06_cosetGeneratorStep_1039 s

theorem g32p_row06_cosetBranchBlock_0064 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 64 r)) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s (g32p_finBlockIndex 1080 64 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s (g32p_finBlockIndex 1080 64 r))) := by
  fin_cases r
  · exact g32p_row06_cosetBranchStep_1024 s
  · exact g32p_row06_cosetBranchStep_1025 s
  · exact g32p_row06_cosetBranchStep_1026 s
  · exact g32p_row06_cosetBranchStep_1027 s
  · exact g32p_row06_cosetBranchStep_1028 s
  · exact g32p_row06_cosetBranchStep_1029 s
  · exact g32p_row06_cosetBranchStep_1030 s
  · exact g32p_row06_cosetBranchStep_1031 s
  · exact g32p_row06_cosetBranchStep_1032 s
  · exact g32p_row06_cosetBranchStep_1033 s
  · exact g32p_row06_cosetBranchStep_1034 s
  · exact g32p_row06_cosetBranchStep_1035 s
  · exact g32p_row06_cosetBranchStep_1036 s
  · exact g32p_row06_cosetBranchStep_1037 s
  · exact g32p_row06_cosetBranchStep_1038 s
  · exact g32p_row06_cosetBranchStep_1039 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetWord_1040 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1040) = g32p_row06_cosetRepresentatives 1040 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1040 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1040) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1040))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1040)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1040 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1040) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1040))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1040)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1041 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1041) = g32p_row06_cosetRepresentatives 1041 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1041 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1041) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1041))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1041)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1041 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1041) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1041))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1041)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1042 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1042) = g32p_row06_cosetRepresentatives 1042 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1042 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1042) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1042))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1042)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1042 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1042) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1042))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1042)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1043 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1043) = g32p_row06_cosetRepresentatives 1043 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1043 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1043) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1043))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1043)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1043 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1043) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1043))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1043)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1044 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1044) = g32p_row06_cosetRepresentatives 1044 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1044 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1044) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1044))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1044)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1044 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1044) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1044))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1044)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1045 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1045) = g32p_row06_cosetRepresentatives 1045 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1045 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1045) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1045))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1045)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1045 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1045) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1045))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1045)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1046 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1046) = g32p_row06_cosetRepresentatives 1046 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1046 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1046) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1046))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1046)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1046 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1046) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1046))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1046)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1047 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1047) = g32p_row06_cosetRepresentatives 1047 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1047 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1047) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1047))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1047)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1047 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1047) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1047))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1047)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1048 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1048) = g32p_row06_cosetRepresentatives 1048 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1048 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1048) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1048))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1048)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1048 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1048) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1048))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1048)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1049 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1049) = g32p_row06_cosetRepresentatives 1049 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1049 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1049) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1049))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1049)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1049 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1049) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1049))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1049)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1050 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1050) = g32p_row06_cosetRepresentatives 1050 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1050 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1050) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1050))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1050)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1050 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1050) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1050))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1050)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1051 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1051) = g32p_row06_cosetRepresentatives 1051 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1051 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1051) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1051))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1051)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1051 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1051) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1051))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1051)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1052 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1052) = g32p_row06_cosetRepresentatives 1052 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1052 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1052) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1052))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1052)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1052 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1052) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1052))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1052)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1053 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1053) = g32p_row06_cosetRepresentatives 1053 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1053 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1053) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1053))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1053)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1053 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1053) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1053))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1053)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1054 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1054) = g32p_row06_cosetRepresentatives 1054 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1054 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1054) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1054))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1054)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1054 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1054) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1054))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1054)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1055 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1055) = g32p_row06_cosetRepresentatives 1055 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1055 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1055) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1055))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1055)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1055 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1055) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1055))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1055)) := by
  decide +kernel

theorem g32p_row06_cosetWordBlock_0065 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row06_cosetWords (g32p_finBlockIndex 1080 65 r)) = g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 65 r) := by
  fin_cases r
  · exact g32p_row06_cosetWord_1040
  · exact g32p_row06_cosetWord_1041
  · exact g32p_row06_cosetWord_1042
  · exact g32p_row06_cosetWord_1043
  · exact g32p_row06_cosetWord_1044
  · exact g32p_row06_cosetWord_1045
  · exact g32p_row06_cosetWord_1046
  · exact g32p_row06_cosetWord_1047
  · exact g32p_row06_cosetWord_1048
  · exact g32p_row06_cosetWord_1049
  · exact g32p_row06_cosetWord_1050
  · exact g32p_row06_cosetWord_1051
  · exact g32p_row06_cosetWord_1052
  · exact g32p_row06_cosetWord_1053
  · exact g32p_row06_cosetWord_1054
  · exact g32p_row06_cosetWord_1055

theorem g32p_row06_cosetGeneratorBlock_0065 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 65 r)) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s (g32p_finBlockIndex 1080 65 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s (g32p_finBlockIndex 1080 65 r))) := by
  fin_cases r
  · exact g32p_row06_cosetGeneratorStep_1040 s
  · exact g32p_row06_cosetGeneratorStep_1041 s
  · exact g32p_row06_cosetGeneratorStep_1042 s
  · exact g32p_row06_cosetGeneratorStep_1043 s
  · exact g32p_row06_cosetGeneratorStep_1044 s
  · exact g32p_row06_cosetGeneratorStep_1045 s
  · exact g32p_row06_cosetGeneratorStep_1046 s
  · exact g32p_row06_cosetGeneratorStep_1047 s
  · exact g32p_row06_cosetGeneratorStep_1048 s
  · exact g32p_row06_cosetGeneratorStep_1049 s
  · exact g32p_row06_cosetGeneratorStep_1050 s
  · exact g32p_row06_cosetGeneratorStep_1051 s
  · exact g32p_row06_cosetGeneratorStep_1052 s
  · exact g32p_row06_cosetGeneratorStep_1053 s
  · exact g32p_row06_cosetGeneratorStep_1054 s
  · exact g32p_row06_cosetGeneratorStep_1055 s

theorem g32p_row06_cosetBranchBlock_0065 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 65 r)) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s (g32p_finBlockIndex 1080 65 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s (g32p_finBlockIndex 1080 65 r))) := by
  fin_cases r
  · exact g32p_row06_cosetBranchStep_1040 s
  · exact g32p_row06_cosetBranchStep_1041 s
  · exact g32p_row06_cosetBranchStep_1042 s
  · exact g32p_row06_cosetBranchStep_1043 s
  · exact g32p_row06_cosetBranchStep_1044 s
  · exact g32p_row06_cosetBranchStep_1045 s
  · exact g32p_row06_cosetBranchStep_1046 s
  · exact g32p_row06_cosetBranchStep_1047 s
  · exact g32p_row06_cosetBranchStep_1048 s
  · exact g32p_row06_cosetBranchStep_1049 s
  · exact g32p_row06_cosetBranchStep_1050 s
  · exact g32p_row06_cosetBranchStep_1051 s
  · exact g32p_row06_cosetBranchStep_1052 s
  · exact g32p_row06_cosetBranchStep_1053 s
  · exact g32p_row06_cosetBranchStep_1054 s
  · exact g32p_row06_cosetBranchStep_1055 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetWord_1056 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1056) = g32p_row06_cosetRepresentatives 1056 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1056 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1056) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1056))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1056)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1056 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1056) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1056))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1056)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1057 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1057) = g32p_row06_cosetRepresentatives 1057 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1057 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1057) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1057))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1057)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1057 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1057) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1057))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1057)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1058 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1058) = g32p_row06_cosetRepresentatives 1058 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1058 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1058) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1058))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1058)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1058 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1058) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1058))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1058)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1059 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1059) = g32p_row06_cosetRepresentatives 1059 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1059 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1059) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1059))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1059)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1059 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1059) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1059))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1059)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1060 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1060) = g32p_row06_cosetRepresentatives 1060 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1060 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1060) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1060))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1060)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1060 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1060) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1060))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1060)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1061 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1061) = g32p_row06_cosetRepresentatives 1061 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1061 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1061) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1061))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1061)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1061 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1061) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1061))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1061)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1062 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1062) = g32p_row06_cosetRepresentatives 1062 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1062 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1062) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1062))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1062)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1062 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1062) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1062))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1062)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1063 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1063) = g32p_row06_cosetRepresentatives 1063 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1063 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1063) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1063))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1063)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1063 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1063) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1063))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1063)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1064 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1064) = g32p_row06_cosetRepresentatives 1064 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1064 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1064) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1064))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1064)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1064 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1064) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1064))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1064)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1065 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1065) = g32p_row06_cosetRepresentatives 1065 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1065 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1065) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1065))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1065)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1065 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1065) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1065))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1065)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1066 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1066) = g32p_row06_cosetRepresentatives 1066 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1066 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1066) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1066))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1066)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1066 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1066) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1066))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1066)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1067 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1067) = g32p_row06_cosetRepresentatives 1067 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1067 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1067) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1067))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1067)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1067 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1067) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1067))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1067)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1068 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1068) = g32p_row06_cosetRepresentatives 1068 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1068 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1068) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1068))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1068)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1068 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1068) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1068))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1068)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1069 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1069) = g32p_row06_cosetRepresentatives 1069 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1069 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1069) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1069))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1069)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1069 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1069) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1069))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1069)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1070 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1070) = g32p_row06_cosetRepresentatives 1070 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1070 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1070) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1070))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1070)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1070 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1070) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1070))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1070)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1071 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1071) = g32p_row06_cosetRepresentatives 1071 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1071 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1071) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1071))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1071)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1071 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1071) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1071))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1071)) := by
  decide +kernel

theorem g32p_row06_cosetWordBlock_0066 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row06_cosetWords (g32p_finBlockIndex 1080 66 r)) = g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 66 r) := by
  fin_cases r
  · exact g32p_row06_cosetWord_1056
  · exact g32p_row06_cosetWord_1057
  · exact g32p_row06_cosetWord_1058
  · exact g32p_row06_cosetWord_1059
  · exact g32p_row06_cosetWord_1060
  · exact g32p_row06_cosetWord_1061
  · exact g32p_row06_cosetWord_1062
  · exact g32p_row06_cosetWord_1063
  · exact g32p_row06_cosetWord_1064
  · exact g32p_row06_cosetWord_1065
  · exact g32p_row06_cosetWord_1066
  · exact g32p_row06_cosetWord_1067
  · exact g32p_row06_cosetWord_1068
  · exact g32p_row06_cosetWord_1069
  · exact g32p_row06_cosetWord_1070
  · exact g32p_row06_cosetWord_1071

theorem g32p_row06_cosetGeneratorBlock_0066 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 66 r)) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s (g32p_finBlockIndex 1080 66 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s (g32p_finBlockIndex 1080 66 r))) := by
  fin_cases r
  · exact g32p_row06_cosetGeneratorStep_1056 s
  · exact g32p_row06_cosetGeneratorStep_1057 s
  · exact g32p_row06_cosetGeneratorStep_1058 s
  · exact g32p_row06_cosetGeneratorStep_1059 s
  · exact g32p_row06_cosetGeneratorStep_1060 s
  · exact g32p_row06_cosetGeneratorStep_1061 s
  · exact g32p_row06_cosetGeneratorStep_1062 s
  · exact g32p_row06_cosetGeneratorStep_1063 s
  · exact g32p_row06_cosetGeneratorStep_1064 s
  · exact g32p_row06_cosetGeneratorStep_1065 s
  · exact g32p_row06_cosetGeneratorStep_1066 s
  · exact g32p_row06_cosetGeneratorStep_1067 s
  · exact g32p_row06_cosetGeneratorStep_1068 s
  · exact g32p_row06_cosetGeneratorStep_1069 s
  · exact g32p_row06_cosetGeneratorStep_1070 s
  · exact g32p_row06_cosetGeneratorStep_1071 s

theorem g32p_row06_cosetBranchBlock_0066 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 66 r)) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s (g32p_finBlockIndex 1080 66 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s (g32p_finBlockIndex 1080 66 r))) := by
  fin_cases r
  · exact g32p_row06_cosetBranchStep_1056 s
  · exact g32p_row06_cosetBranchStep_1057 s
  · exact g32p_row06_cosetBranchStep_1058 s
  · exact g32p_row06_cosetBranchStep_1059 s
  · exact g32p_row06_cosetBranchStep_1060 s
  · exact g32p_row06_cosetBranchStep_1061 s
  · exact g32p_row06_cosetBranchStep_1062 s
  · exact g32p_row06_cosetBranchStep_1063 s
  · exact g32p_row06_cosetBranchStep_1064 s
  · exact g32p_row06_cosetBranchStep_1065 s
  · exact g32p_row06_cosetBranchStep_1066 s
  · exact g32p_row06_cosetBranchStep_1067 s
  · exact g32p_row06_cosetBranchStep_1068 s
  · exact g32p_row06_cosetBranchStep_1069 s
  · exact g32p_row06_cosetBranchStep_1070 s
  · exact g32p_row06_cosetBranchStep_1071 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetWord_1072 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1072) = g32p_row06_cosetRepresentatives 1072 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1072 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1072) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1072))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1072)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1072 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1072) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1072))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1072)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1073 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1073) = g32p_row06_cosetRepresentatives 1073 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1073 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1073) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1073))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1073)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1073 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1073) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1073))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1073)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1074 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1074) = g32p_row06_cosetRepresentatives 1074 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1074 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1074) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1074))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1074)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1074 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1074) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1074))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1074)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1075 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1075) = g32p_row06_cosetRepresentatives 1075 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1075 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1075) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1075))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1075)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1075 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1075) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1075))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1075)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1076 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1076) = g32p_row06_cosetRepresentatives 1076 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1076 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1076) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1076))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1076)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1076 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1076) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1076))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1076)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1077 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1077) = g32p_row06_cosetRepresentatives 1077 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1077 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1077) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1077))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1077)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1077 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1077) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1077))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1077)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1078 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1078) = g32p_row06_cosetRepresentatives 1078 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1078 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1078) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1078))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1078)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1078 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1078) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1078))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1078)) := by
  decide +kernel

theorem g32p_row06_cosetWord_1079 :
    g32p_archiveIntegralWord (g32p_row06_cosetWords 1079) = g32p_row06_cosetRepresentatives 1079 := by
  decide +kernel

theorem g32p_row06_cosetGeneratorStep_1079 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives 1079) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s 1079))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s 1079)) := by
  decide +kernel

theorem g32p_row06_cosetBranchStep_1079 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives 1079) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s 1079))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s 1079)) := by
  decide +kernel

theorem g32p_row06_cosetWordBlock_0067 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row06_cosetWords (g32p_finBlockIndex 1080 67 r)) = g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 67 r) := by
  fin_cases r
  · exact g32p_row06_cosetWord_1072
  · exact g32p_row06_cosetWord_1073
  · exact g32p_row06_cosetWord_1074
  · exact g32p_row06_cosetWord_1075
  · exact g32p_row06_cosetWord_1076
  · exact g32p_row06_cosetWord_1077
  · exact g32p_row06_cosetWord_1078
  · exact g32p_row06_cosetWord_1079
  · exact g32p_row06_cosetWord_0000
  · exact g32p_row06_cosetWord_0001
  · exact g32p_row06_cosetWord_0002
  · exact g32p_row06_cosetWord_0003
  · exact g32p_row06_cosetWord_0004
  · exact g32p_row06_cosetWord_0005
  · exact g32p_row06_cosetWord_0006
  · exact g32p_row06_cosetWord_0007

theorem g32p_row06_cosetGeneratorBlock_0067 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 67 r)) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s (g32p_finBlockIndex 1080 67 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s (g32p_finBlockIndex 1080 67 r))) := by
  fin_cases r
  · exact g32p_row06_cosetGeneratorStep_1072 s
  · exact g32p_row06_cosetGeneratorStep_1073 s
  · exact g32p_row06_cosetGeneratorStep_1074 s
  · exact g32p_row06_cosetGeneratorStep_1075 s
  · exact g32p_row06_cosetGeneratorStep_1076 s
  · exact g32p_row06_cosetGeneratorStep_1077 s
  · exact g32p_row06_cosetGeneratorStep_1078 s
  · exact g32p_row06_cosetGeneratorStep_1079 s
  · exact g32p_row06_cosetGeneratorStep_0000 s
  · exact g32p_row06_cosetGeneratorStep_0001 s
  · exact g32p_row06_cosetGeneratorStep_0002 s
  · exact g32p_row06_cosetGeneratorStep_0003 s
  · exact g32p_row06_cosetGeneratorStep_0004 s
  · exact g32p_row06_cosetGeneratorStep_0005 s
  · exact g32p_row06_cosetGeneratorStep_0006 s
  · exact g32p_row06_cosetGeneratorStep_0007 s

theorem g32p_row06_cosetBranchBlock_0067 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices s) (g32p_row06_cosetRepresentatives (g32p_finBlockIndex 1080 67 r)) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetBranchNext s (g32p_finBlockIndex 1080 67 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetBranchFactor s (g32p_finBlockIndex 1080 67 r))) := by
  fin_cases r
  · exact g32p_row06_cosetBranchStep_1072 s
  · exact g32p_row06_cosetBranchStep_1073 s
  · exact g32p_row06_cosetBranchStep_1074 s
  · exact g32p_row06_cosetBranchStep_1075 s
  · exact g32p_row06_cosetBranchStep_1076 s
  · exact g32p_row06_cosetBranchStep_1077 s
  · exact g32p_row06_cosetBranchStep_1078 s
  · exact g32p_row06_cosetBranchStep_1079 s
  · exact g32p_row06_cosetBranchStep_0000 s
  · exact g32p_row06_cosetBranchStep_0001 s
  · exact g32p_row06_cosetBranchStep_0002 s
  · exact g32p_row06_cosetBranchStep_0003 s
  · exact g32p_row06_cosetBranchStep_0004 s
  · exact g32p_row06_cosetBranchStep_0005 s
  · exact g32p_row06_cosetBranchStep_0006 s
  · exact g32p_row06_cosetBranchStep_0007 s


end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row06_cosetWord (i : Fin 1080) :
    g32p_archiveIntegralWord (g32p_row06_cosetWords i) = g32p_row06_cosetRepresentatives i := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row06_cosetWordBlock_0000
  · exact g32p_row06_cosetWordBlock_0001
  · exact g32p_row06_cosetWordBlock_0002
  · exact g32p_row06_cosetWordBlock_0003
  · exact g32p_row06_cosetWordBlock_0004
  · exact g32p_row06_cosetWordBlock_0005
  · exact g32p_row06_cosetWordBlock_0006
  · exact g32p_row06_cosetWordBlock_0007
  · exact g32p_row06_cosetWordBlock_0008
  · exact g32p_row06_cosetWordBlock_0009
  · exact g32p_row06_cosetWordBlock_0010
  · exact g32p_row06_cosetWordBlock_0011
  · exact g32p_row06_cosetWordBlock_0012
  · exact g32p_row06_cosetWordBlock_0013
  · exact g32p_row06_cosetWordBlock_0014
  · exact g32p_row06_cosetWordBlock_0015
  · exact g32p_row06_cosetWordBlock_0016
  · exact g32p_row06_cosetWordBlock_0017
  · exact g32p_row06_cosetWordBlock_0018
  · exact g32p_row06_cosetWordBlock_0019
  · exact g32p_row06_cosetWordBlock_0020
  · exact g32p_row06_cosetWordBlock_0021
  · exact g32p_row06_cosetWordBlock_0022
  · exact g32p_row06_cosetWordBlock_0023
  · exact g32p_row06_cosetWordBlock_0024
  · exact g32p_row06_cosetWordBlock_0025
  · exact g32p_row06_cosetWordBlock_0026
  · exact g32p_row06_cosetWordBlock_0027
  · exact g32p_row06_cosetWordBlock_0028
  · exact g32p_row06_cosetWordBlock_0029
  · exact g32p_row06_cosetWordBlock_0030
  · exact g32p_row06_cosetWordBlock_0031
  · exact g32p_row06_cosetWordBlock_0032
  · exact g32p_row06_cosetWordBlock_0033
  · exact g32p_row06_cosetWordBlock_0034
  · exact g32p_row06_cosetWordBlock_0035
  · exact g32p_row06_cosetWordBlock_0036
  · exact g32p_row06_cosetWordBlock_0037
  · exact g32p_row06_cosetWordBlock_0038
  · exact g32p_row06_cosetWordBlock_0039
  · exact g32p_row06_cosetWordBlock_0040
  · exact g32p_row06_cosetWordBlock_0041
  · exact g32p_row06_cosetWordBlock_0042
  · exact g32p_row06_cosetWordBlock_0043
  · exact g32p_row06_cosetWordBlock_0044
  · exact g32p_row06_cosetWordBlock_0045
  · exact g32p_row06_cosetWordBlock_0046
  · exact g32p_row06_cosetWordBlock_0047
  · exact g32p_row06_cosetWordBlock_0048
  · exact g32p_row06_cosetWordBlock_0049
  · exact g32p_row06_cosetWordBlock_0050
  · exact g32p_row06_cosetWordBlock_0051
  · exact g32p_row06_cosetWordBlock_0052
  · exact g32p_row06_cosetWordBlock_0053
  · exact g32p_row06_cosetWordBlock_0054
  · exact g32p_row06_cosetWordBlock_0055
  · exact g32p_row06_cosetWordBlock_0056
  · exact g32p_row06_cosetWordBlock_0057
  · exact g32p_row06_cosetWordBlock_0058
  · exact g32p_row06_cosetWordBlock_0059
  · exact g32p_row06_cosetWordBlock_0060
  · exact g32p_row06_cosetWordBlock_0061
  · exact g32p_row06_cosetWordBlock_0062
  · exact g32p_row06_cosetWordBlock_0063
  · exact g32p_row06_cosetWordBlock_0064
  · exact g32p_row06_cosetWordBlock_0065
  · exact g32p_row06_cosetWordBlock_0066
  · exact g32p_row06_cosetWordBlock_0067


def g32p_row06_cosetActualRepresentatives (i : Fin 1080) : g32p_G := g32p_archiveWord (g32p_row06_cosetWords i)

theorem g32p_row06_cosetActualRepresentatives_map (i : Fin 1080) :
    b4b_toMatrix (g32p_row06_cosetActualRepresentatives i) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row06_cosetRepresentatives i)) := by
  rw [g32p_row06_cosetActualRepresentatives, g32p_archiveIntegralWord_map, g32p_row06_cosetWord]

theorem g32p_row06_cosetGeneratorStep (s : Fin 4) (i : Fin 1080) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row06_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetGeneratorNext s i))
        (g32p_row06_groupNodes (g32p_row06_cosetGeneratorFactor s i)) := by
  revert i
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row06_cosetGeneratorBlock_0000 s
  · exact g32p_row06_cosetGeneratorBlock_0001 s
  · exact g32p_row06_cosetGeneratorBlock_0002 s
  · exact g32p_row06_cosetGeneratorBlock_0003 s
  · exact g32p_row06_cosetGeneratorBlock_0004 s
  · exact g32p_row06_cosetGeneratorBlock_0005 s
  · exact g32p_row06_cosetGeneratorBlock_0006 s
  · exact g32p_row06_cosetGeneratorBlock_0007 s
  · exact g32p_row06_cosetGeneratorBlock_0008 s
  · exact g32p_row06_cosetGeneratorBlock_0009 s
  · exact g32p_row06_cosetGeneratorBlock_0010 s
  · exact g32p_row06_cosetGeneratorBlock_0011 s
  · exact g32p_row06_cosetGeneratorBlock_0012 s
  · exact g32p_row06_cosetGeneratorBlock_0013 s
  · exact g32p_row06_cosetGeneratorBlock_0014 s
  · exact g32p_row06_cosetGeneratorBlock_0015 s
  · exact g32p_row06_cosetGeneratorBlock_0016 s
  · exact g32p_row06_cosetGeneratorBlock_0017 s
  · exact g32p_row06_cosetGeneratorBlock_0018 s
  · exact g32p_row06_cosetGeneratorBlock_0019 s
  · exact g32p_row06_cosetGeneratorBlock_0020 s
  · exact g32p_row06_cosetGeneratorBlock_0021 s
  · exact g32p_row06_cosetGeneratorBlock_0022 s
  · exact g32p_row06_cosetGeneratorBlock_0023 s
  · exact g32p_row06_cosetGeneratorBlock_0024 s
  · exact g32p_row06_cosetGeneratorBlock_0025 s
  · exact g32p_row06_cosetGeneratorBlock_0026 s
  · exact g32p_row06_cosetGeneratorBlock_0027 s
  · exact g32p_row06_cosetGeneratorBlock_0028 s
  · exact g32p_row06_cosetGeneratorBlock_0029 s
  · exact g32p_row06_cosetGeneratorBlock_0030 s
  · exact g32p_row06_cosetGeneratorBlock_0031 s
  · exact g32p_row06_cosetGeneratorBlock_0032 s
  · exact g32p_row06_cosetGeneratorBlock_0033 s
  · exact g32p_row06_cosetGeneratorBlock_0034 s
  · exact g32p_row06_cosetGeneratorBlock_0035 s
  · exact g32p_row06_cosetGeneratorBlock_0036 s
  · exact g32p_row06_cosetGeneratorBlock_0037 s
  · exact g32p_row06_cosetGeneratorBlock_0038 s
  · exact g32p_row06_cosetGeneratorBlock_0039 s
  · exact g32p_row06_cosetGeneratorBlock_0040 s
  · exact g32p_row06_cosetGeneratorBlock_0041 s
  · exact g32p_row06_cosetGeneratorBlock_0042 s
  · exact g32p_row06_cosetGeneratorBlock_0043 s
  · exact g32p_row06_cosetGeneratorBlock_0044 s
  · exact g32p_row06_cosetGeneratorBlock_0045 s
  · exact g32p_row06_cosetGeneratorBlock_0046 s
  · exact g32p_row06_cosetGeneratorBlock_0047 s
  · exact g32p_row06_cosetGeneratorBlock_0048 s
  · exact g32p_row06_cosetGeneratorBlock_0049 s
  · exact g32p_row06_cosetGeneratorBlock_0050 s
  · exact g32p_row06_cosetGeneratorBlock_0051 s
  · exact g32p_row06_cosetGeneratorBlock_0052 s
  · exact g32p_row06_cosetGeneratorBlock_0053 s
  · exact g32p_row06_cosetGeneratorBlock_0054 s
  · exact g32p_row06_cosetGeneratorBlock_0055 s
  · exact g32p_row06_cosetGeneratorBlock_0056 s
  · exact g32p_row06_cosetGeneratorBlock_0057 s
  · exact g32p_row06_cosetGeneratorBlock_0058 s
  · exact g32p_row06_cosetGeneratorBlock_0059 s
  · exact g32p_row06_cosetGeneratorBlock_0060 s
  · exact g32p_row06_cosetGeneratorBlock_0061 s
  · exact g32p_row06_cosetGeneratorBlock_0062 s
  · exact g32p_row06_cosetGeneratorBlock_0063 s
  · exact g32p_row06_cosetGeneratorBlock_0064 s
  · exact g32p_row06_cosetGeneratorBlock_0065 s
  · exact g32p_row06_cosetGeneratorBlock_0066 s
  · exact g32p_row06_cosetGeneratorBlock_0067 s


theorem g32p_row06_cosetActualStep (s : Fin 4) (i : Fin 1080) :
    g32p_word (g32p_archiveWords s) * g32p_row06_cosetActualRepresentatives i =
      g32p_row06_cosetActualRepresentatives (g32p_row06_cosetGeneratorNext s i) *
        (g32p_row06_groupEquiv (g32p_row06_cosetGeneratorFactor s i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_word (g32p_archiveWords s) * g32p_row06_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row06_cosetActualRepresentatives (g32p_row06_cosetGeneratorNext s i) *
      (g32p_row06_groupEquiv (g32p_row06_cosetGeneratorFactor s i) : g32p_G))
  rw [map_mul, map_mul, g32p_row06_cosetActualRepresentatives_map,
    g32p_row06_cosetActualRepresentatives_map, g32p_row06_groupEquiv_map,
    g32p_integralWord_map, g32p_archiveWordIntegral,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    g32p_row06_cosetGeneratorStep]

theorem g32p_row06_cosetEnumeration :
    Function.Bijective (fun i => (QuotientGroup.mk (g32p_row06_cosetActualRepresentatives i) :
      g32p_G ⧸ g32p_row06_finiteSupplier.H)) := by
  apply g32p_coset_bijective
  · apply g32p_coset_surjective _ _ g32p_archive_generators_top _ 0 (by rfl)
      g32p_row06_cosetGeneratorNext
      (fun s i => g32p_row06_groupEquiv (g32p_row06_cosetGeneratorFactor s i))
    exact g32p_row06_cosetActualStep
  · rw [g32p_row06_finiteSupplier_order]
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

theorem g32p_row06_cosetMonodromy_0_0000 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 0) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 0)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 0)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 0) = g32p_row06_cosetExponents0 0 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0001 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 1) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 1)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 1)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 1) = g32p_row06_cosetExponents0 1 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0002 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 2) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 2)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 2)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 2) = g32p_row06_cosetExponents0 2 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0003 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 3) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 3)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 3)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 3) = g32p_row06_cosetExponents0 3 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0004 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 4) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 4)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 4)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 4) = g32p_row06_cosetExponents0 4 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0005 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 5) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 5)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 5)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 5) = g32p_row06_cosetExponents0 5 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0006 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 6) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 6)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 6)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 6) = g32p_row06_cosetExponents0 6 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0007 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 7) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 7)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 7)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 7) = g32p_row06_cosetExponents0 7 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0008 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 8) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 8)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 8)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 8) = g32p_row06_cosetExponents0 8 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0009 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 9) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 9)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 9)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 9) = g32p_row06_cosetExponents0 9 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0010 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 10) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 10)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 10)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 10) = g32p_row06_cosetExponents0 10 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0011 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 11) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 11)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 11)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 11) = g32p_row06_cosetExponents0 11 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0012 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 12) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 12)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 12)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 12) = g32p_row06_cosetExponents0 12 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0013 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 13) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 13)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 13)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 13) = g32p_row06_cosetExponents0 13 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0014 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 14) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 14)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 14)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 14) = g32p_row06_cosetExponents0 14 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0015 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 15) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 15)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 15)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 15) = g32p_row06_cosetExponents0 15 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0000 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 0 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 0 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 0 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 0 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 0 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 0 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0000
  · exact g32p_row06_cosetMonodromy_0_0001
  · exact g32p_row06_cosetMonodromy_0_0002
  · exact g32p_row06_cosetMonodromy_0_0003
  · exact g32p_row06_cosetMonodromy_0_0004
  · exact g32p_row06_cosetMonodromy_0_0005
  · exact g32p_row06_cosetMonodromy_0_0006
  · exact g32p_row06_cosetMonodromy_0_0007
  · exact g32p_row06_cosetMonodromy_0_0008
  · exact g32p_row06_cosetMonodromy_0_0009
  · exact g32p_row06_cosetMonodromy_0_0010
  · exact g32p_row06_cosetMonodromy_0_0011
  · exact g32p_row06_cosetMonodromy_0_0012
  · exact g32p_row06_cosetMonodromy_0_0013
  · exact g32p_row06_cosetMonodromy_0_0014
  · exact g32p_row06_cosetMonodromy_0_0015


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0016 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 16) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 16)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 16)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 16) = g32p_row06_cosetExponents0 16 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0017 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 17) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 17)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 17)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 17) = g32p_row06_cosetExponents0 17 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0018 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 18) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 18)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 18)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 18) = g32p_row06_cosetExponents0 18 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0019 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 19) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 19)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 19)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 19) = g32p_row06_cosetExponents0 19 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0020 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 20) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 20)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 20)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 20) = g32p_row06_cosetExponents0 20 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0021 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 21) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 21)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 21)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 21) = g32p_row06_cosetExponents0 21 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0022 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 22) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 22)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 22)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 22) = g32p_row06_cosetExponents0 22 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 23) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 23)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 23)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 23) = g32p_row06_cosetExponents0 23 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 24) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 24)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 24)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 24) = g32p_row06_cosetExponents0 24 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 25) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 25)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 25)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 25) = g32p_row06_cosetExponents0 25 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 26) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 26)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 26)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 26) = g32p_row06_cosetExponents0 26 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 27) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 27)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 27)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 27) = g32p_row06_cosetExponents0 27 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 28) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 28)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 28)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 28) = g32p_row06_cosetExponents0 28 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0029 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 30) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 30)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 29)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 29) = g32p_row06_cosetExponents0 29 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0030 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 31) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 31)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 30)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 30) = g32p_row06_cosetExponents0 30 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0031 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 32) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 32)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 31)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 31) = g32p_row06_cosetExponents0 31 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0001 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 1 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 1 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 1 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 1 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 1 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 1 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0016
  · exact g32p_row06_cosetMonodromy_0_0017
  · exact g32p_row06_cosetMonodromy_0_0018
  · exact g32p_row06_cosetMonodromy_0_0019
  · exact g32p_row06_cosetMonodromy_0_0020
  · exact g32p_row06_cosetMonodromy_0_0021
  · exact g32p_row06_cosetMonodromy_0_0022
  · exact g32p_row06_cosetMonodromy_0_0023
  · exact g32p_row06_cosetMonodromy_0_0024
  · exact g32p_row06_cosetMonodromy_0_0025
  · exact g32p_row06_cosetMonodromy_0_0026
  · exact g32p_row06_cosetMonodromy_0_0027
  · exact g32p_row06_cosetMonodromy_0_0028
  · exact g32p_row06_cosetMonodromy_0_0029
  · exact g32p_row06_cosetMonodromy_0_0030
  · exact g32p_row06_cosetMonodromy_0_0031


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0032 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 33) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 33)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 32)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 32) = g32p_row06_cosetExponents0 32 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0033 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 34) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 34)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 33)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 33) = g32p_row06_cosetExponents0 33 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0034 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 35) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 35)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 34)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 34) = g32p_row06_cosetExponents0 34 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0035 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 36)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 35)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 35) = g32p_row06_cosetExponents0 35 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0036 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 37)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 36)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 36) = g32p_row06_cosetExponents0 36 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0037 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 38)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 37)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 37) = g32p_row06_cosetExponents0 37 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0038 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 39)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 38)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 38) = g32p_row06_cosetExponents0 38 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0039 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 40)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 39)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 39) = g32p_row06_cosetExponents0 39 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0040 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 41) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 41)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 40)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 40) = g32p_row06_cosetExponents0 40 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0041 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 42) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 42)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 41)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 41) = g32p_row06_cosetExponents0 41 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0042 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 43)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 42)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 42) = g32p_row06_cosetExponents0 42 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0043 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 44) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 44)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 43)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 43) = g32p_row06_cosetExponents0 43 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0044 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 45) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 45)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 44)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 44) = g32p_row06_cosetExponents0 44 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0045 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 46) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 46)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 45)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 45) = g32p_row06_cosetExponents0 45 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0046 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 47) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 47)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 46)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 46) = g32p_row06_cosetExponents0 46 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0047 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 48) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 48)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 47)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 47) = g32p_row06_cosetExponents0 47 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0002 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 2 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 2 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 2 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 2 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 2 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 2 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0032
  · exact g32p_row06_cosetMonodromy_0_0033
  · exact g32p_row06_cosetMonodromy_0_0034
  · exact g32p_row06_cosetMonodromy_0_0035
  · exact g32p_row06_cosetMonodromy_0_0036
  · exact g32p_row06_cosetMonodromy_0_0037
  · exact g32p_row06_cosetMonodromy_0_0038
  · exact g32p_row06_cosetMonodromy_0_0039
  · exact g32p_row06_cosetMonodromy_0_0040
  · exact g32p_row06_cosetMonodromy_0_0041
  · exact g32p_row06_cosetMonodromy_0_0042
  · exact g32p_row06_cosetMonodromy_0_0043
  · exact g32p_row06_cosetMonodromy_0_0044
  · exact g32p_row06_cosetMonodromy_0_0045
  · exact g32p_row06_cosetMonodromy_0_0046
  · exact g32p_row06_cosetMonodromy_0_0047


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0048 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 49) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 49)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 48)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 48) = g32p_row06_cosetExponents0 48 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0049 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 50) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 50)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 49)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 49) = g32p_row06_cosetExponents0 49 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0050 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 51) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 51)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 50)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 50) = g32p_row06_cosetExponents0 50 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0051 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 52) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 52)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 51)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 51) = g32p_row06_cosetExponents0 51 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0052 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 53) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 53)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 52)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 52) = g32p_row06_cosetExponents0 52 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0053 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 54) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 54)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 53)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 53) = g32p_row06_cosetExponents0 53 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0054 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 55) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 55)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 54)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 54) = g32p_row06_cosetExponents0 54 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0055 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 56) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 56)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 55)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 55) = g32p_row06_cosetExponents0 55 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0056 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 58) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 58)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 56)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 56) = g32p_row06_cosetExponents0 56 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0057 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 59) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 59)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 57)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 57) = g32p_row06_cosetExponents0 57 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0058 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 60) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 60)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 58)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 58) = g32p_row06_cosetExponents0 58 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0059 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 61) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 61)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 59)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 59) = g32p_row06_cosetExponents0 59 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0060 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 62) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 62)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 60)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 60) = g32p_row06_cosetExponents0 60 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0061 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 63) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 63)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 61)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 61) = g32p_row06_cosetExponents0 61 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0062 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 64) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 64)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 62)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 62) = g32p_row06_cosetExponents0 62 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0063 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 65) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 65)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 63)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 63) = g32p_row06_cosetExponents0 63 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0003 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 3 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 3 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 3 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 3 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 3 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 3 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0048
  · exact g32p_row06_cosetMonodromy_0_0049
  · exact g32p_row06_cosetMonodromy_0_0050
  · exact g32p_row06_cosetMonodromy_0_0051
  · exact g32p_row06_cosetMonodromy_0_0052
  · exact g32p_row06_cosetMonodromy_0_0053
  · exact g32p_row06_cosetMonodromy_0_0054
  · exact g32p_row06_cosetMonodromy_0_0055
  · exact g32p_row06_cosetMonodromy_0_0056
  · exact g32p_row06_cosetMonodromy_0_0057
  · exact g32p_row06_cosetMonodromy_0_0058
  · exact g32p_row06_cosetMonodromy_0_0059
  · exact g32p_row06_cosetMonodromy_0_0060
  · exact g32p_row06_cosetMonodromy_0_0061
  · exact g32p_row06_cosetMonodromy_0_0062
  · exact g32p_row06_cosetMonodromy_0_0063


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0064 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 66) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 66)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 64)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 64) = g32p_row06_cosetExponents0 64 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0065 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 67) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 67)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 65)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 65) = g32p_row06_cosetExponents0 65 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0066 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 68) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 68)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 66)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 66) = g32p_row06_cosetExponents0 66 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0067 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 69) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 69)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 67)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 67) = g32p_row06_cosetExponents0 67 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0068 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 70) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 70)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 68)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 68) = g32p_row06_cosetExponents0 68 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0069 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 71) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 71)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 69)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 69) = g32p_row06_cosetExponents0 69 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0070 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 72) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 72)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 70)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 70) = g32p_row06_cosetExponents0 70 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0071 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 73) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 73)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 71)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 71) = g32p_row06_cosetExponents0 71 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0072 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 74) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 74)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 72)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 72) = g32p_row06_cosetExponents0 72 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0073 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 75) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 75)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 73)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 73) = g32p_row06_cosetExponents0 73 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0074 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 76) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 76)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 74)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 74) = g32p_row06_cosetExponents0 74 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0075 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 77) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 77)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 75)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 75) = g32p_row06_cosetExponents0 75 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0076 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 78) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 78)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 76)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 76) = g32p_row06_cosetExponents0 76 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0077 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 79) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 79)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 77)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 77) = g32p_row06_cosetExponents0 77 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0078 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 82) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 82)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 78)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 78) = g32p_row06_cosetExponents0 78 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0079 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 85) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 85)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 79)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 79) = g32p_row06_cosetExponents0 79 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0004 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 4 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 4 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 4 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 4 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 4 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 4 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0064
  · exact g32p_row06_cosetMonodromy_0_0065
  · exact g32p_row06_cosetMonodromy_0_0066
  · exact g32p_row06_cosetMonodromy_0_0067
  · exact g32p_row06_cosetMonodromy_0_0068
  · exact g32p_row06_cosetMonodromy_0_0069
  · exact g32p_row06_cosetMonodromy_0_0070
  · exact g32p_row06_cosetMonodromy_0_0071
  · exact g32p_row06_cosetMonodromy_0_0072
  · exact g32p_row06_cosetMonodromy_0_0073
  · exact g32p_row06_cosetMonodromy_0_0074
  · exact g32p_row06_cosetMonodromy_0_0075
  · exact g32p_row06_cosetMonodromy_0_0076
  · exact g32p_row06_cosetMonodromy_0_0077
  · exact g32p_row06_cosetMonodromy_0_0078
  · exact g32p_row06_cosetMonodromy_0_0079


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0080 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 86) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 86)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 80)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 80) = g32p_row06_cosetExponents0 80 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0081 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 87) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 87)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 81)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 81) = g32p_row06_cosetExponents0 81 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0082 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 88) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 88)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 82)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 82) = g32p_row06_cosetExponents0 82 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0083 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 89) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 89)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 83)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 83) = g32p_row06_cosetExponents0 83 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0084 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 90) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 90)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 84)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 84) = g32p_row06_cosetExponents0 84 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0085 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 91) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 91)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 85)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 85) = g32p_row06_cosetExponents0 85 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0086 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 93) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 93)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 86)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 86) = g32p_row06_cosetExponents0 86 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0087 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 94) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 94)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 87)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 87) = g32p_row06_cosetExponents0 87 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0088 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 95) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 95)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 88)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 88) = g32p_row06_cosetExponents0 88 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0089 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 96) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 96)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 89)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 89) = g32p_row06_cosetExponents0 89 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0090 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 97) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 97)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 90)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 90) = g32p_row06_cosetExponents0 90 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0091 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 98) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 98)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 91)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 91) = g32p_row06_cosetExponents0 91 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0092 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 99) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 99)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 92)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 92) = g32p_row06_cosetExponents0 92 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0093 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 100) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 100)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 93)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 93) = g32p_row06_cosetExponents0 93 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0094 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 101) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 101)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 94)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 94) = g32p_row06_cosetExponents0 94 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0095 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 102) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 102)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 95)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 95) = g32p_row06_cosetExponents0 95 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0005 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 5 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 5 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 5 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 5 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 5 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 5 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0080
  · exact g32p_row06_cosetMonodromy_0_0081
  · exact g32p_row06_cosetMonodromy_0_0082
  · exact g32p_row06_cosetMonodromy_0_0083
  · exact g32p_row06_cosetMonodromy_0_0084
  · exact g32p_row06_cosetMonodromy_0_0085
  · exact g32p_row06_cosetMonodromy_0_0086
  · exact g32p_row06_cosetMonodromy_0_0087
  · exact g32p_row06_cosetMonodromy_0_0088
  · exact g32p_row06_cosetMonodromy_0_0089
  · exact g32p_row06_cosetMonodromy_0_0090
  · exact g32p_row06_cosetMonodromy_0_0091
  · exact g32p_row06_cosetMonodromy_0_0092
  · exact g32p_row06_cosetMonodromy_0_0093
  · exact g32p_row06_cosetMonodromy_0_0094
  · exact g32p_row06_cosetMonodromy_0_0095


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0096 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 103) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 103)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 96)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 96) = g32p_row06_cosetExponents0 96 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0097 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 104) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 104)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 97)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 97) = g32p_row06_cosetExponents0 97 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0098 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 105) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 105)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 98)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 98) = g32p_row06_cosetExponents0 98 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0099 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 107) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 107)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 99)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 99) = g32p_row06_cosetExponents0 99 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0100 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 108) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 108)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 100)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 100) = g32p_row06_cosetExponents0 100 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0101 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 109) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 109)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 101)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 101) = g32p_row06_cosetExponents0 101 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0102 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 110) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 110)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 102)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 102) = g32p_row06_cosetExponents0 102 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0103 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 111) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 111)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 103)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 103) = g32p_row06_cosetExponents0 103 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0104 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 112) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 112)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 104)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 104) = g32p_row06_cosetExponents0 104 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0105 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 113) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 113)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 105)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 105) = g32p_row06_cosetExponents0 105 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0106 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 114) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 114)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 106)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 106) = g32p_row06_cosetExponents0 106 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0107 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 115) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 115)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 107)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 107) = g32p_row06_cosetExponents0 107 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0108 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 117) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 117)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 108)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 108) = g32p_row06_cosetExponents0 108 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0109 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 118) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 118)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 109)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 109) = g32p_row06_cosetExponents0 109 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0110 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 119) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 119)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 110)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 110) = g32p_row06_cosetExponents0 110 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0111 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 121) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 121)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 111)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 111) = g32p_row06_cosetExponents0 111 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0006 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 6 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 6 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 6 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 6 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 6 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 6 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0096
  · exact g32p_row06_cosetMonodromy_0_0097
  · exact g32p_row06_cosetMonodromy_0_0098
  · exact g32p_row06_cosetMonodromy_0_0099
  · exact g32p_row06_cosetMonodromy_0_0100
  · exact g32p_row06_cosetMonodromy_0_0101
  · exact g32p_row06_cosetMonodromy_0_0102
  · exact g32p_row06_cosetMonodromy_0_0103
  · exact g32p_row06_cosetMonodromy_0_0104
  · exact g32p_row06_cosetMonodromy_0_0105
  · exact g32p_row06_cosetMonodromy_0_0106
  · exact g32p_row06_cosetMonodromy_0_0107
  · exact g32p_row06_cosetMonodromy_0_0108
  · exact g32p_row06_cosetMonodromy_0_0109
  · exact g32p_row06_cosetMonodromy_0_0110
  · exact g32p_row06_cosetMonodromy_0_0111


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0112 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 122) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 122)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 112)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 112) = g32p_row06_cosetExponents0 112 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0113 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 123) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 123)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 113)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 113) = g32p_row06_cosetExponents0 113 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0114 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 124) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 124)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 114)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 114) = g32p_row06_cosetExponents0 114 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0115 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 125) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 125)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 115)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 115) = g32p_row06_cosetExponents0 115 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0116 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 126) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 126)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 116)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 116) = g32p_row06_cosetExponents0 116 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0117 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 128) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 128)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 117)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 117) = g32p_row06_cosetExponents0 117 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0118 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 129) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 129)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 118)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 118) = g32p_row06_cosetExponents0 118 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0119 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 130) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 130)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 119)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 119) = g32p_row06_cosetExponents0 119 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0120 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 131) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 131)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 120)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 120) = g32p_row06_cosetExponents0 120 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0121 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 132) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 132)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 121)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 121) = g32p_row06_cosetExponents0 121 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0122 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 133) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 133)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 122)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 122) = g32p_row06_cosetExponents0 122 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0123 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 134) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 134)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 123)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 123) = g32p_row06_cosetExponents0 123 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0124 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 135) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 135)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 124)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 124) = g32p_row06_cosetExponents0 124 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0125 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 136) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 136)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 125)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 125) = g32p_row06_cosetExponents0 125 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0126 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 137) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 137)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 126)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 126) = g32p_row06_cosetExponents0 126 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0127 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 138) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 138)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 127)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 127) = g32p_row06_cosetExponents0 127 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0007 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 7 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 7 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 7 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 7 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 7 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 7 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0112
  · exact g32p_row06_cosetMonodromy_0_0113
  · exact g32p_row06_cosetMonodromy_0_0114
  · exact g32p_row06_cosetMonodromy_0_0115
  · exact g32p_row06_cosetMonodromy_0_0116
  · exact g32p_row06_cosetMonodromy_0_0117
  · exact g32p_row06_cosetMonodromy_0_0118
  · exact g32p_row06_cosetMonodromy_0_0119
  · exact g32p_row06_cosetMonodromy_0_0120
  · exact g32p_row06_cosetMonodromy_0_0121
  · exact g32p_row06_cosetMonodromy_0_0122
  · exact g32p_row06_cosetMonodromy_0_0123
  · exact g32p_row06_cosetMonodromy_0_0124
  · exact g32p_row06_cosetMonodromy_0_0125
  · exact g32p_row06_cosetMonodromy_0_0126
  · exact g32p_row06_cosetMonodromy_0_0127


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0128 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 139) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 139)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 128)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 128) = g32p_row06_cosetExponents0 128 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0129 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 140) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 140)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 129)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 129) = g32p_row06_cosetExponents0 129 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0130 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 141) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 141)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 130)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 130) = g32p_row06_cosetExponents0 130 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0131 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 143) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 143)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 131)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 131) = g32p_row06_cosetExponents0 131 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0132 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 148) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 148)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 132)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 132) = g32p_row06_cosetExponents0 132 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0133 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 149) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 149)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 133)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 133) = g32p_row06_cosetExponents0 133 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0134 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 150) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 150)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 134)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 134) = g32p_row06_cosetExponents0 134 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0135 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 151) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 151)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 135)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 135) = g32p_row06_cosetExponents0 135 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0136 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 153) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 153)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 136)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 136) = g32p_row06_cosetExponents0 136 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0137 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 154) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 154)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 137)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 137) = g32p_row06_cosetExponents0 137 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0138 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 157) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 157)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 138)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 138) = g32p_row06_cosetExponents0 138 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0139 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 158) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 158)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 139)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 139) = g32p_row06_cosetExponents0 139 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0140 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 160) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 160)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 140)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 140) = g32p_row06_cosetExponents0 140 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0141 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 161) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 161)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 141)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 141) = g32p_row06_cosetExponents0 141 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0142 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 162) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 162)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 142)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 142) = g32p_row06_cosetExponents0 142 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0143 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 163) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 163)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 143)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 143) = g32p_row06_cosetExponents0 143 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0008 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 8 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 8 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 8 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 8 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 8 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 8 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0128
  · exact g32p_row06_cosetMonodromy_0_0129
  · exact g32p_row06_cosetMonodromy_0_0130
  · exact g32p_row06_cosetMonodromy_0_0131
  · exact g32p_row06_cosetMonodromy_0_0132
  · exact g32p_row06_cosetMonodromy_0_0133
  · exact g32p_row06_cosetMonodromy_0_0134
  · exact g32p_row06_cosetMonodromy_0_0135
  · exact g32p_row06_cosetMonodromy_0_0136
  · exact g32p_row06_cosetMonodromy_0_0137
  · exact g32p_row06_cosetMonodromy_0_0138
  · exact g32p_row06_cosetMonodromy_0_0139
  · exact g32p_row06_cosetMonodromy_0_0140
  · exact g32p_row06_cosetMonodromy_0_0141
  · exact g32p_row06_cosetMonodromy_0_0142
  · exact g32p_row06_cosetMonodromy_0_0143


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0144 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 165) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 165)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 144)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 144) = g32p_row06_cosetExponents0 144 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0145 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 166) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 166)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 145)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 145) = g32p_row06_cosetExponents0 145 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0146 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 168) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 168)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 146)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 146) = g32p_row06_cosetExponents0 146 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0147 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 169) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 169)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 147)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 147) = g32p_row06_cosetExponents0 147 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0148 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 170) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 170)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 148)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 148) = g32p_row06_cosetExponents0 148 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0149 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 172) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 172)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 149)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 149) = g32p_row06_cosetExponents0 149 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0150 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 174) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 174)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 150)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 150) = g32p_row06_cosetExponents0 150 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0151 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 175) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 175)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 151)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 151) = g32p_row06_cosetExponents0 151 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0152 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 176) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 176)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 152)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 152) = g32p_row06_cosetExponents0 152 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0153 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 177) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 177)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 153)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 153) = g32p_row06_cosetExponents0 153 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0154 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 182) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 182)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 154)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 154) = g32p_row06_cosetExponents0 154 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0155 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 183) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 183)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 155)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 155) = g32p_row06_cosetExponents0 155 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0156 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 184) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 184)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 156)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 156) = g32p_row06_cosetExponents0 156 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0157 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 186) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 186)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 157)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 157) = g32p_row06_cosetExponents0 157 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0158 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 187) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 187)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 158)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 158) = g32p_row06_cosetExponents0 158 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0159 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 189) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 189)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 159)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 159) = g32p_row06_cosetExponents0 159 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0009 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 9 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 9 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 9 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 9 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 9 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 9 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0144
  · exact g32p_row06_cosetMonodromy_0_0145
  · exact g32p_row06_cosetMonodromy_0_0146
  · exact g32p_row06_cosetMonodromy_0_0147
  · exact g32p_row06_cosetMonodromy_0_0148
  · exact g32p_row06_cosetMonodromy_0_0149
  · exact g32p_row06_cosetMonodromy_0_0150
  · exact g32p_row06_cosetMonodromy_0_0151
  · exact g32p_row06_cosetMonodromy_0_0152
  · exact g32p_row06_cosetMonodromy_0_0153
  · exact g32p_row06_cosetMonodromy_0_0154
  · exact g32p_row06_cosetMonodromy_0_0155
  · exact g32p_row06_cosetMonodromy_0_0156
  · exact g32p_row06_cosetMonodromy_0_0157
  · exact g32p_row06_cosetMonodromy_0_0158
  · exact g32p_row06_cosetMonodromy_0_0159


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row06_cosetMonodromy_0_0160 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 191) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 191)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 160)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 160) = g32p_row06_cosetExponents0 160 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0161 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 192) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 192)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 161)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 161) = g32p_row06_cosetExponents0 161 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0162 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 196) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 196)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 162)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 162) = g32p_row06_cosetExponents0 162 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0163 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 199) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 199)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 163)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 163) = g32p_row06_cosetExponents0 163 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0164 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 201) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 201)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 164)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 164) = g32p_row06_cosetExponents0 164 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0165 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 202) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 202)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 165)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 165) = g32p_row06_cosetExponents0 165 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0166 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 203) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 203)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 166)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 166) = g32p_row06_cosetExponents0 166 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0167 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 205) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 205)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 167)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 167) = g32p_row06_cosetExponents0 167 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0168 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 209) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 209)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 168)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 168) = g32p_row06_cosetExponents0 168 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0169 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 212) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 212)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 169)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 169) = g32p_row06_cosetExponents0 169 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0170 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 214) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 214)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 170)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 170) = g32p_row06_cosetExponents0 170 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0171 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 216) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 216)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 171)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 171) = g32p_row06_cosetExponents0 171 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0172 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 218) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 218)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 172)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 172) = g32p_row06_cosetExponents0 172 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0173 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 220) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 220)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 173)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 173) = g32p_row06_cosetExponents0 173 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0174 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 223) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 223)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 174)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 174) = g32p_row06_cosetExponents0 174 := by
  decide +kernel

theorem g32p_row06_cosetMonodromy_0_0175 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mmul (g32p_row06_cosetBranchMatrices 0) (HurwitzPrymRex_mone)))) (g32p_row06_cosetRepresentatives 224) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives 224)
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 175)) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 175) = g32p_row06_cosetExponents0 175 := by
  decide +kernel

theorem g32p_row06_cosetMonodromyBlock0_0010 (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_integralMatrixPower (g32p_row06_cosetBranchMatrices 0) (g32p_row06_cosetLengths0 (g32p_finBlockIndex 360 10 r)))
      (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 10 r))) =
      HurwitzPrymRex_mmul (g32p_row06_cosetRepresentatives (g32p_row06_cosetRoots0 (g32p_finBlockIndex 360 10 r)))
        (g32p_row06_groupNodes (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 10 r))) ∧
    g32p_row06_characterValues (g32p_row06_cosetMonodromies0 (g32p_finBlockIndex 360 10 r)) = g32p_row06_cosetExponents0 (g32p_finBlockIndex 360 10 r) := by
  fin_cases r
  · exact g32p_row06_cosetMonodromy_0_0160
  · exact g32p_row06_cosetMonodromy_0_0161
  · exact g32p_row06_cosetMonodromy_0_0162
  · exact g32p_row06_cosetMonodromy_0_0163
  · exact g32p_row06_cosetMonodromy_0_0164
  · exact g32p_row06_cosetMonodromy_0_0165
  · exact g32p_row06_cosetMonodromy_0_0166
  · exact g32p_row06_cosetMonodromy_0_0167
  · exact g32p_row06_cosetMonodromy_0_0168
  · exact g32p_row06_cosetMonodromy_0_0169
  · exact g32p_row06_cosetMonodromy_0_0170
  · exact g32p_row06_cosetMonodromy_0_0171
  · exact g32p_row06_cosetMonodromy_0_0172
  · exact g32p_row06_cosetMonodromy_0_0173
  · exact g32p_row06_cosetMonodromy_0_0174
  · exact g32p_row06_cosetMonodromy_0_0175


end HodgeLean.Foundations.Program

end
