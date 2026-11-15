import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked1044

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2048 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2048) = g32p_row13_cosetRepresentatives 2048 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2048 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2048) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2048))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2048)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2048 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2048) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2048))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2048)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2049 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2049) = g32p_row13_cosetRepresentatives 2049 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2049 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2049) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2049))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2049)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2049 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2049) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2049))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2049)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2050 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2050) = g32p_row13_cosetRepresentatives 2050 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2050 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2050) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2050))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2050)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2050 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2050) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2050))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2050)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2051 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2051) = g32p_row13_cosetRepresentatives 2051 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2051 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2051) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2051))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2051)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2051 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2051) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2051))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2051)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2052 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2052) = g32p_row13_cosetRepresentatives 2052 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2052 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2052) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2052))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2052)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2052 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2052) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2052))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2052)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2053 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2053) = g32p_row13_cosetRepresentatives 2053 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2053 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2053) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2053))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2053)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2053 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2053) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2053))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2053)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2054 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2054) = g32p_row13_cosetRepresentatives 2054 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2054 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2054) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2054))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2054)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2054 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2054) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2054))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2054)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2055 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2055) = g32p_row13_cosetRepresentatives 2055 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2055 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2055) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2055))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2055)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2055 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2055) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2055))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2055)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2056 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2056) = g32p_row13_cosetRepresentatives 2056 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2056 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2056) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2056))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2056)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2056 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2056) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2056))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2056)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2057 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2057) = g32p_row13_cosetRepresentatives 2057 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2057 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2057) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2057))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2057)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2057 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2057) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2057))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2057)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2058 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2058) = g32p_row13_cosetRepresentatives 2058 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2058 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2058) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2058))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2058)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2058 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2058) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2058))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2058)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2059 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2059) = g32p_row13_cosetRepresentatives 2059 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2059 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2059) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2059))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2059)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2059 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2059) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2059))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2059)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2060 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2060) = g32p_row13_cosetRepresentatives 2060 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2060 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2060) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2060))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2060)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2060 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2060) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2060))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2060)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2061 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2061) = g32p_row13_cosetRepresentatives 2061 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2061 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2061) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2061))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2061)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2061 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2061) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2061))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2061)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2062 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2062) = g32p_row13_cosetRepresentatives 2062 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2062 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2062) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2062))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2062)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2062 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2062) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2062))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2062)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2063 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2063) = g32p_row13_cosetRepresentatives 2063 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2063 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2063) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2063))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2063)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2063 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2063) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2063))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2063)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0128 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 128 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 128 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2048
  · exact g32p_row13_cosetWord_2049
  · exact g32p_row13_cosetWord_2050
  · exact g32p_row13_cosetWord_2051
  · exact g32p_row13_cosetWord_2052
  · exact g32p_row13_cosetWord_2053
  · exact g32p_row13_cosetWord_2054
  · exact g32p_row13_cosetWord_2055
  · exact g32p_row13_cosetWord_2056
  · exact g32p_row13_cosetWord_2057
  · exact g32p_row13_cosetWord_2058
  · exact g32p_row13_cosetWord_2059
  · exact g32p_row13_cosetWord_2060
  · exact g32p_row13_cosetWord_2061
  · exact g32p_row13_cosetWord_2062
  · exact g32p_row13_cosetWord_2063

theorem g32p_row13_cosetGeneratorBlock_0128 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 128 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 128 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 128 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2048 s
  · exact g32p_row13_cosetGeneratorStep_2049 s
  · exact g32p_row13_cosetGeneratorStep_2050 s
  · exact g32p_row13_cosetGeneratorStep_2051 s
  · exact g32p_row13_cosetGeneratorStep_2052 s
  · exact g32p_row13_cosetGeneratorStep_2053 s
  · exact g32p_row13_cosetGeneratorStep_2054 s
  · exact g32p_row13_cosetGeneratorStep_2055 s
  · exact g32p_row13_cosetGeneratorStep_2056 s
  · exact g32p_row13_cosetGeneratorStep_2057 s
  · exact g32p_row13_cosetGeneratorStep_2058 s
  · exact g32p_row13_cosetGeneratorStep_2059 s
  · exact g32p_row13_cosetGeneratorStep_2060 s
  · exact g32p_row13_cosetGeneratorStep_2061 s
  · exact g32p_row13_cosetGeneratorStep_2062 s
  · exact g32p_row13_cosetGeneratorStep_2063 s

theorem g32p_row13_cosetBranchBlock_0128 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 128 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 128 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 128 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2048 s
  · exact g32p_row13_cosetBranchStep_2049 s
  · exact g32p_row13_cosetBranchStep_2050 s
  · exact g32p_row13_cosetBranchStep_2051 s
  · exact g32p_row13_cosetBranchStep_2052 s
  · exact g32p_row13_cosetBranchStep_2053 s
  · exact g32p_row13_cosetBranchStep_2054 s
  · exact g32p_row13_cosetBranchStep_2055 s
  · exact g32p_row13_cosetBranchStep_2056 s
  · exact g32p_row13_cosetBranchStep_2057 s
  · exact g32p_row13_cosetBranchStep_2058 s
  · exact g32p_row13_cosetBranchStep_2059 s
  · exact g32p_row13_cosetBranchStep_2060 s
  · exact g32p_row13_cosetBranchStep_2061 s
  · exact g32p_row13_cosetBranchStep_2062 s
  · exact g32p_row13_cosetBranchStep_2063 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2064 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2064) = g32p_row13_cosetRepresentatives 2064 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2064 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2064) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2064))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2064)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2064 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2064) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2064))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2064)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2065 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2065) = g32p_row13_cosetRepresentatives 2065 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2065 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2065) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2065))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2065)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2065 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2065) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2065))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2065)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2066 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2066) = g32p_row13_cosetRepresentatives 2066 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2066 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2066) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2066))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2066)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2066 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2066) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2066))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2066)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2067 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2067) = g32p_row13_cosetRepresentatives 2067 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2067 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2067) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2067))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2067)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2067 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2067) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2067))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2067)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2068 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2068) = g32p_row13_cosetRepresentatives 2068 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2068 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2068) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2068))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2068)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2068 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2068) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2068))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2068)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2069 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2069) = g32p_row13_cosetRepresentatives 2069 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2069 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2069) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2069))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2069)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2069 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2069) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2069))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2069)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2070 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2070) = g32p_row13_cosetRepresentatives 2070 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2070 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2070) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2070))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2070)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2070 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2070) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2070))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2070)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2071 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2071) = g32p_row13_cosetRepresentatives 2071 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2071 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2071) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2071))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2071)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2071 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2071) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2071))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2071)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2072 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2072) = g32p_row13_cosetRepresentatives 2072 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2072 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2072) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2072))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2072)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2072 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2072) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2072))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2072)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2073 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2073) = g32p_row13_cosetRepresentatives 2073 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2073 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2073) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2073))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2073)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2073 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2073) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2073))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2073)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2074 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2074) = g32p_row13_cosetRepresentatives 2074 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2074 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2074) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2074))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2074)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2074 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2074) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2074))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2074)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2075 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2075) = g32p_row13_cosetRepresentatives 2075 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2075 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2075) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2075))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2075)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2075 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2075) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2075))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2075)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2076 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2076) = g32p_row13_cosetRepresentatives 2076 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2076 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2076) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2076))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2076)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2076 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2076) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2076))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2076)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2077 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2077) = g32p_row13_cosetRepresentatives 2077 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2077 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2077) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2077))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2077)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2077 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2077) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2077))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2077)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2078 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2078) = g32p_row13_cosetRepresentatives 2078 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2078 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2078) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2078))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2078)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2078 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2078) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2078))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2078)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2079 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2079) = g32p_row13_cosetRepresentatives 2079 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2079 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2079) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2079))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2079)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2079 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2079) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2079))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2079)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0129 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 129 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 129 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2064
  · exact g32p_row13_cosetWord_2065
  · exact g32p_row13_cosetWord_2066
  · exact g32p_row13_cosetWord_2067
  · exact g32p_row13_cosetWord_2068
  · exact g32p_row13_cosetWord_2069
  · exact g32p_row13_cosetWord_2070
  · exact g32p_row13_cosetWord_2071
  · exact g32p_row13_cosetWord_2072
  · exact g32p_row13_cosetWord_2073
  · exact g32p_row13_cosetWord_2074
  · exact g32p_row13_cosetWord_2075
  · exact g32p_row13_cosetWord_2076
  · exact g32p_row13_cosetWord_2077
  · exact g32p_row13_cosetWord_2078
  · exact g32p_row13_cosetWord_2079

theorem g32p_row13_cosetGeneratorBlock_0129 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 129 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 129 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 129 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2064 s
  · exact g32p_row13_cosetGeneratorStep_2065 s
  · exact g32p_row13_cosetGeneratorStep_2066 s
  · exact g32p_row13_cosetGeneratorStep_2067 s
  · exact g32p_row13_cosetGeneratorStep_2068 s
  · exact g32p_row13_cosetGeneratorStep_2069 s
  · exact g32p_row13_cosetGeneratorStep_2070 s
  · exact g32p_row13_cosetGeneratorStep_2071 s
  · exact g32p_row13_cosetGeneratorStep_2072 s
  · exact g32p_row13_cosetGeneratorStep_2073 s
  · exact g32p_row13_cosetGeneratorStep_2074 s
  · exact g32p_row13_cosetGeneratorStep_2075 s
  · exact g32p_row13_cosetGeneratorStep_2076 s
  · exact g32p_row13_cosetGeneratorStep_2077 s
  · exact g32p_row13_cosetGeneratorStep_2078 s
  · exact g32p_row13_cosetGeneratorStep_2079 s

theorem g32p_row13_cosetBranchBlock_0129 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 129 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 129 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 129 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2064 s
  · exact g32p_row13_cosetBranchStep_2065 s
  · exact g32p_row13_cosetBranchStep_2066 s
  · exact g32p_row13_cosetBranchStep_2067 s
  · exact g32p_row13_cosetBranchStep_2068 s
  · exact g32p_row13_cosetBranchStep_2069 s
  · exact g32p_row13_cosetBranchStep_2070 s
  · exact g32p_row13_cosetBranchStep_2071 s
  · exact g32p_row13_cosetBranchStep_2072 s
  · exact g32p_row13_cosetBranchStep_2073 s
  · exact g32p_row13_cosetBranchStep_2074 s
  · exact g32p_row13_cosetBranchStep_2075 s
  · exact g32p_row13_cosetBranchStep_2076 s
  · exact g32p_row13_cosetBranchStep_2077 s
  · exact g32p_row13_cosetBranchStep_2078 s
  · exact g32p_row13_cosetBranchStep_2079 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2080 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2080) = g32p_row13_cosetRepresentatives 2080 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2080 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2080) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2080))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2080)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2080 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2080) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2080))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2080)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2081 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2081) = g32p_row13_cosetRepresentatives 2081 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2081 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2081) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2081))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2081)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2081 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2081) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2081))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2081)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2082 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2082) = g32p_row13_cosetRepresentatives 2082 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2082 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2082) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2082))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2082)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2082 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2082) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2082))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2082)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2083 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2083) = g32p_row13_cosetRepresentatives 2083 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2083 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2083) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2083))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2083)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2083 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2083) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2083))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2083)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2084 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2084) = g32p_row13_cosetRepresentatives 2084 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2084 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2084) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2084))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2084)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2084 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2084) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2084))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2084)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2085 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2085) = g32p_row13_cosetRepresentatives 2085 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2085 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2085) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2085))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2085)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2085 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2085) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2085))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2085)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2086 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2086) = g32p_row13_cosetRepresentatives 2086 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2086 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2086) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2086))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2086)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2086 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2086) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2086))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2086)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2087 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2087) = g32p_row13_cosetRepresentatives 2087 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2087 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2087) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2087))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2087)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2087 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2087) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2087))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2087)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2088 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2088) = g32p_row13_cosetRepresentatives 2088 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2088 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2088) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2088))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2088)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2088 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2088) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2088))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2088)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2089 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2089) = g32p_row13_cosetRepresentatives 2089 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2089 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2089) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2089))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2089)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2089 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2089) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2089))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2089)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2090 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2090) = g32p_row13_cosetRepresentatives 2090 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2090 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2090) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2090))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2090)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2090 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2090) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2090))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2090)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2091 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2091) = g32p_row13_cosetRepresentatives 2091 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2091 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2091) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2091))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2091)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2091 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2091) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2091))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2091)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2092 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2092) = g32p_row13_cosetRepresentatives 2092 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2092 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2092) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2092))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2092)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2092 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2092) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2092))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2092)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2093 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2093) = g32p_row13_cosetRepresentatives 2093 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2093 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2093) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2093))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2093)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2093 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2093) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2093))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2093)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2094 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2094) = g32p_row13_cosetRepresentatives 2094 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2094 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2094) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2094))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2094)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2094 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2094) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2094))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2094)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2095 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2095) = g32p_row13_cosetRepresentatives 2095 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2095 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2095) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2095))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2095)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2095 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2095) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2095))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2095)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0130 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 130 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 130 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2080
  · exact g32p_row13_cosetWord_2081
  · exact g32p_row13_cosetWord_2082
  · exact g32p_row13_cosetWord_2083
  · exact g32p_row13_cosetWord_2084
  · exact g32p_row13_cosetWord_2085
  · exact g32p_row13_cosetWord_2086
  · exact g32p_row13_cosetWord_2087
  · exact g32p_row13_cosetWord_2088
  · exact g32p_row13_cosetWord_2089
  · exact g32p_row13_cosetWord_2090
  · exact g32p_row13_cosetWord_2091
  · exact g32p_row13_cosetWord_2092
  · exact g32p_row13_cosetWord_2093
  · exact g32p_row13_cosetWord_2094
  · exact g32p_row13_cosetWord_2095

theorem g32p_row13_cosetGeneratorBlock_0130 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 130 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 130 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 130 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2080 s
  · exact g32p_row13_cosetGeneratorStep_2081 s
  · exact g32p_row13_cosetGeneratorStep_2082 s
  · exact g32p_row13_cosetGeneratorStep_2083 s
  · exact g32p_row13_cosetGeneratorStep_2084 s
  · exact g32p_row13_cosetGeneratorStep_2085 s
  · exact g32p_row13_cosetGeneratorStep_2086 s
  · exact g32p_row13_cosetGeneratorStep_2087 s
  · exact g32p_row13_cosetGeneratorStep_2088 s
  · exact g32p_row13_cosetGeneratorStep_2089 s
  · exact g32p_row13_cosetGeneratorStep_2090 s
  · exact g32p_row13_cosetGeneratorStep_2091 s
  · exact g32p_row13_cosetGeneratorStep_2092 s
  · exact g32p_row13_cosetGeneratorStep_2093 s
  · exact g32p_row13_cosetGeneratorStep_2094 s
  · exact g32p_row13_cosetGeneratorStep_2095 s

theorem g32p_row13_cosetBranchBlock_0130 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 130 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 130 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 130 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2080 s
  · exact g32p_row13_cosetBranchStep_2081 s
  · exact g32p_row13_cosetBranchStep_2082 s
  · exact g32p_row13_cosetBranchStep_2083 s
  · exact g32p_row13_cosetBranchStep_2084 s
  · exact g32p_row13_cosetBranchStep_2085 s
  · exact g32p_row13_cosetBranchStep_2086 s
  · exact g32p_row13_cosetBranchStep_2087 s
  · exact g32p_row13_cosetBranchStep_2088 s
  · exact g32p_row13_cosetBranchStep_2089 s
  · exact g32p_row13_cosetBranchStep_2090 s
  · exact g32p_row13_cosetBranchStep_2091 s
  · exact g32p_row13_cosetBranchStep_2092 s
  · exact g32p_row13_cosetBranchStep_2093 s
  · exact g32p_row13_cosetBranchStep_2094 s
  · exact g32p_row13_cosetBranchStep_2095 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2096 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2096) = g32p_row13_cosetRepresentatives 2096 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2096 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2096) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2096))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2096)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2096 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2096) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2096))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2096)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2097 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2097) = g32p_row13_cosetRepresentatives 2097 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2097 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2097) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2097))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2097)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2097 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2097) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2097))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2097)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2098 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2098) = g32p_row13_cosetRepresentatives 2098 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2098 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2098) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2098))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2098)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2098 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2098) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2098))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2098)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2099 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2099) = g32p_row13_cosetRepresentatives 2099 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2099 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2099) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2099))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2099)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2099 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2099) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2099))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2099)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2100 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2100) = g32p_row13_cosetRepresentatives 2100 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2100 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2100) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2100))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2100)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2100 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2100) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2100))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2100)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2101 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2101) = g32p_row13_cosetRepresentatives 2101 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2101 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2101) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2101))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2101)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2101 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2101) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2101))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2101)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2102 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2102) = g32p_row13_cosetRepresentatives 2102 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2102 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2102) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2102))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2102)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2102 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2102) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2102))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2102)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2103 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2103) = g32p_row13_cosetRepresentatives 2103 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2103 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2103) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2103))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2103)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2103 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2103) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2103))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2103)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2104 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2104) = g32p_row13_cosetRepresentatives 2104 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2104 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2104) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2104))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2104)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2104 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2104) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2104))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2104)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2105 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2105) = g32p_row13_cosetRepresentatives 2105 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2105 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2105) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2105))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2105)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2105 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2105) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2105))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2105)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2106 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2106) = g32p_row13_cosetRepresentatives 2106 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2106 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2106) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2106))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2106)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2106 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2106) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2106))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2106)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2107 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2107) = g32p_row13_cosetRepresentatives 2107 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2107 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2107) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2107))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2107)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2107 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2107) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2107))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2107)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2108 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2108) = g32p_row13_cosetRepresentatives 2108 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2108 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2108) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2108))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2108)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2108 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2108) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2108))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2108)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2109 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2109) = g32p_row13_cosetRepresentatives 2109 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2109 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2109) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2109))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2109)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2109 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2109) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2109))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2109)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2110 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2110) = g32p_row13_cosetRepresentatives 2110 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2110 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2110) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2110))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2110)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2110 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2110) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2110))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2110)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2111 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2111) = g32p_row13_cosetRepresentatives 2111 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2111 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2111) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2111))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2111)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2111 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2111) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2111))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2111)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0131 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 131 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 131 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2096
  · exact g32p_row13_cosetWord_2097
  · exact g32p_row13_cosetWord_2098
  · exact g32p_row13_cosetWord_2099
  · exact g32p_row13_cosetWord_2100
  · exact g32p_row13_cosetWord_2101
  · exact g32p_row13_cosetWord_2102
  · exact g32p_row13_cosetWord_2103
  · exact g32p_row13_cosetWord_2104
  · exact g32p_row13_cosetWord_2105
  · exact g32p_row13_cosetWord_2106
  · exact g32p_row13_cosetWord_2107
  · exact g32p_row13_cosetWord_2108
  · exact g32p_row13_cosetWord_2109
  · exact g32p_row13_cosetWord_2110
  · exact g32p_row13_cosetWord_2111

theorem g32p_row13_cosetGeneratorBlock_0131 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 131 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 131 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 131 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2096 s
  · exact g32p_row13_cosetGeneratorStep_2097 s
  · exact g32p_row13_cosetGeneratorStep_2098 s
  · exact g32p_row13_cosetGeneratorStep_2099 s
  · exact g32p_row13_cosetGeneratorStep_2100 s
  · exact g32p_row13_cosetGeneratorStep_2101 s
  · exact g32p_row13_cosetGeneratorStep_2102 s
  · exact g32p_row13_cosetGeneratorStep_2103 s
  · exact g32p_row13_cosetGeneratorStep_2104 s
  · exact g32p_row13_cosetGeneratorStep_2105 s
  · exact g32p_row13_cosetGeneratorStep_2106 s
  · exact g32p_row13_cosetGeneratorStep_2107 s
  · exact g32p_row13_cosetGeneratorStep_2108 s
  · exact g32p_row13_cosetGeneratorStep_2109 s
  · exact g32p_row13_cosetGeneratorStep_2110 s
  · exact g32p_row13_cosetGeneratorStep_2111 s

theorem g32p_row13_cosetBranchBlock_0131 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 131 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 131 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 131 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2096 s
  · exact g32p_row13_cosetBranchStep_2097 s
  · exact g32p_row13_cosetBranchStep_2098 s
  · exact g32p_row13_cosetBranchStep_2099 s
  · exact g32p_row13_cosetBranchStep_2100 s
  · exact g32p_row13_cosetBranchStep_2101 s
  · exact g32p_row13_cosetBranchStep_2102 s
  · exact g32p_row13_cosetBranchStep_2103 s
  · exact g32p_row13_cosetBranchStep_2104 s
  · exact g32p_row13_cosetBranchStep_2105 s
  · exact g32p_row13_cosetBranchStep_2106 s
  · exact g32p_row13_cosetBranchStep_2107 s
  · exact g32p_row13_cosetBranchStep_2108 s
  · exact g32p_row13_cosetBranchStep_2109 s
  · exact g32p_row13_cosetBranchStep_2110 s
  · exact g32p_row13_cosetBranchStep_2111 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2112 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2112) = g32p_row13_cosetRepresentatives 2112 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2112 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2112) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2112))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2112)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2112 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2112) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2112))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2112)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2113 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2113) = g32p_row13_cosetRepresentatives 2113 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2113 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2113) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2113))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2113)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2113 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2113) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2113))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2113)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2114 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2114) = g32p_row13_cosetRepresentatives 2114 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2114 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2114) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2114))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2114)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2114 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2114) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2114))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2114)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2115 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2115) = g32p_row13_cosetRepresentatives 2115 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2115 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2115) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2115))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2115)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2115 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2115) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2115))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2115)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2116 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2116) = g32p_row13_cosetRepresentatives 2116 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2116 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2116) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2116))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2116)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2116 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2116) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2116))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2116)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2117 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2117) = g32p_row13_cosetRepresentatives 2117 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2117 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2117) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2117))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2117)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2117 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2117) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2117))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2117)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2118 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2118) = g32p_row13_cosetRepresentatives 2118 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2118 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2118) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2118))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2118)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2118 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2118) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2118))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2118)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2119 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2119) = g32p_row13_cosetRepresentatives 2119 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2119 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2119) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2119))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2119)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2119 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2119) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2119))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2119)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2120 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2120) = g32p_row13_cosetRepresentatives 2120 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2120 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2120) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2120))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2120)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2120 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2120) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2120))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2120)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2121 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2121) = g32p_row13_cosetRepresentatives 2121 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2121 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2121) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2121))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2121)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2121 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2121) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2121))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2121)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2122 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2122) = g32p_row13_cosetRepresentatives 2122 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2122 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2122) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2122))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2122)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2122 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2122) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2122))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2122)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2123 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2123) = g32p_row13_cosetRepresentatives 2123 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2123 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2123) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2123))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2123)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2123 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2123) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2123))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2123)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2124 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2124) = g32p_row13_cosetRepresentatives 2124 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2124 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2124) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2124))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2124)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2124 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2124) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2124))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2124)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2125 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2125) = g32p_row13_cosetRepresentatives 2125 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2125 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2125) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2125))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2125)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2125 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2125) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2125))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2125)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2126 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2126) = g32p_row13_cosetRepresentatives 2126 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2126 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2126) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2126))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2126)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2126 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2126) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2126))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2126)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2127 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2127) = g32p_row13_cosetRepresentatives 2127 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2127 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2127) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2127))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2127)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2127 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2127) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2127))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2127)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0132 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 132 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 132 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2112
  · exact g32p_row13_cosetWord_2113
  · exact g32p_row13_cosetWord_2114
  · exact g32p_row13_cosetWord_2115
  · exact g32p_row13_cosetWord_2116
  · exact g32p_row13_cosetWord_2117
  · exact g32p_row13_cosetWord_2118
  · exact g32p_row13_cosetWord_2119
  · exact g32p_row13_cosetWord_2120
  · exact g32p_row13_cosetWord_2121
  · exact g32p_row13_cosetWord_2122
  · exact g32p_row13_cosetWord_2123
  · exact g32p_row13_cosetWord_2124
  · exact g32p_row13_cosetWord_2125
  · exact g32p_row13_cosetWord_2126
  · exact g32p_row13_cosetWord_2127

theorem g32p_row13_cosetGeneratorBlock_0132 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 132 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 132 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 132 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2112 s
  · exact g32p_row13_cosetGeneratorStep_2113 s
  · exact g32p_row13_cosetGeneratorStep_2114 s
  · exact g32p_row13_cosetGeneratorStep_2115 s
  · exact g32p_row13_cosetGeneratorStep_2116 s
  · exact g32p_row13_cosetGeneratorStep_2117 s
  · exact g32p_row13_cosetGeneratorStep_2118 s
  · exact g32p_row13_cosetGeneratorStep_2119 s
  · exact g32p_row13_cosetGeneratorStep_2120 s
  · exact g32p_row13_cosetGeneratorStep_2121 s
  · exact g32p_row13_cosetGeneratorStep_2122 s
  · exact g32p_row13_cosetGeneratorStep_2123 s
  · exact g32p_row13_cosetGeneratorStep_2124 s
  · exact g32p_row13_cosetGeneratorStep_2125 s
  · exact g32p_row13_cosetGeneratorStep_2126 s
  · exact g32p_row13_cosetGeneratorStep_2127 s

theorem g32p_row13_cosetBranchBlock_0132 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 132 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 132 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 132 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2112 s
  · exact g32p_row13_cosetBranchStep_2113 s
  · exact g32p_row13_cosetBranchStep_2114 s
  · exact g32p_row13_cosetBranchStep_2115 s
  · exact g32p_row13_cosetBranchStep_2116 s
  · exact g32p_row13_cosetBranchStep_2117 s
  · exact g32p_row13_cosetBranchStep_2118 s
  · exact g32p_row13_cosetBranchStep_2119 s
  · exact g32p_row13_cosetBranchStep_2120 s
  · exact g32p_row13_cosetBranchStep_2121 s
  · exact g32p_row13_cosetBranchStep_2122 s
  · exact g32p_row13_cosetBranchStep_2123 s
  · exact g32p_row13_cosetBranchStep_2124 s
  · exact g32p_row13_cosetBranchStep_2125 s
  · exact g32p_row13_cosetBranchStep_2126 s
  · exact g32p_row13_cosetBranchStep_2127 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2128 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2128) = g32p_row13_cosetRepresentatives 2128 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2128 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2128) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2128))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2128)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2128 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2128) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2128))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2128)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2129 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2129) = g32p_row13_cosetRepresentatives 2129 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2129 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2129) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2129))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2129)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2129 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2129) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2129))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2129)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2130 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2130) = g32p_row13_cosetRepresentatives 2130 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2130 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2130) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2130))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2130)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2130 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2130) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2130))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2130)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2131 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2131) = g32p_row13_cosetRepresentatives 2131 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2131 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2131) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2131))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2131)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2131 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2131) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2131))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2131)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2132 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2132) = g32p_row13_cosetRepresentatives 2132 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2132 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2132) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2132))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2132)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2132 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2132) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2132))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2132)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2133 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2133) = g32p_row13_cosetRepresentatives 2133 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2133 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2133) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2133))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2133)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2133 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2133) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2133))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2133)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2134 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2134) = g32p_row13_cosetRepresentatives 2134 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2134 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2134) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2134))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2134)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2134 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2134) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2134))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2134)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2135 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2135) = g32p_row13_cosetRepresentatives 2135 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2135 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2135) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2135))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2135)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2135 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2135) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2135))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2135)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2136 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2136) = g32p_row13_cosetRepresentatives 2136 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2136 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2136) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2136))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2136)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2136 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2136) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2136))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2136)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2137 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2137) = g32p_row13_cosetRepresentatives 2137 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2137 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2137) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2137))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2137)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2137 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2137) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2137))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2137)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2138 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2138) = g32p_row13_cosetRepresentatives 2138 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2138 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2138) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2138))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2138)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2138 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2138) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2138))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2138)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2139 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2139) = g32p_row13_cosetRepresentatives 2139 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2139 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2139) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2139))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2139)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2139 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2139) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2139))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2139)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2140 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2140) = g32p_row13_cosetRepresentatives 2140 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2140 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2140) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2140))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2140)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2140 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2140) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2140))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2140)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2141 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2141) = g32p_row13_cosetRepresentatives 2141 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2141 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2141) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2141))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2141)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2141 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2141) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2141))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2141)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2142 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2142) = g32p_row13_cosetRepresentatives 2142 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2142 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2142) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2142))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2142)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2142 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2142) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2142))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2142)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2143 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2143) = g32p_row13_cosetRepresentatives 2143 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2143 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2143) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2143))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2143)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2143 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2143) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2143))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2143)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0133 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 133 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 133 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2128
  · exact g32p_row13_cosetWord_2129
  · exact g32p_row13_cosetWord_2130
  · exact g32p_row13_cosetWord_2131
  · exact g32p_row13_cosetWord_2132
  · exact g32p_row13_cosetWord_2133
  · exact g32p_row13_cosetWord_2134
  · exact g32p_row13_cosetWord_2135
  · exact g32p_row13_cosetWord_2136
  · exact g32p_row13_cosetWord_2137
  · exact g32p_row13_cosetWord_2138
  · exact g32p_row13_cosetWord_2139
  · exact g32p_row13_cosetWord_2140
  · exact g32p_row13_cosetWord_2141
  · exact g32p_row13_cosetWord_2142
  · exact g32p_row13_cosetWord_2143

theorem g32p_row13_cosetGeneratorBlock_0133 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 133 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 133 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 133 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2128 s
  · exact g32p_row13_cosetGeneratorStep_2129 s
  · exact g32p_row13_cosetGeneratorStep_2130 s
  · exact g32p_row13_cosetGeneratorStep_2131 s
  · exact g32p_row13_cosetGeneratorStep_2132 s
  · exact g32p_row13_cosetGeneratorStep_2133 s
  · exact g32p_row13_cosetGeneratorStep_2134 s
  · exact g32p_row13_cosetGeneratorStep_2135 s
  · exact g32p_row13_cosetGeneratorStep_2136 s
  · exact g32p_row13_cosetGeneratorStep_2137 s
  · exact g32p_row13_cosetGeneratorStep_2138 s
  · exact g32p_row13_cosetGeneratorStep_2139 s
  · exact g32p_row13_cosetGeneratorStep_2140 s
  · exact g32p_row13_cosetGeneratorStep_2141 s
  · exact g32p_row13_cosetGeneratorStep_2142 s
  · exact g32p_row13_cosetGeneratorStep_2143 s

theorem g32p_row13_cosetBranchBlock_0133 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 133 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 133 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 133 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2128 s
  · exact g32p_row13_cosetBranchStep_2129 s
  · exact g32p_row13_cosetBranchStep_2130 s
  · exact g32p_row13_cosetBranchStep_2131 s
  · exact g32p_row13_cosetBranchStep_2132 s
  · exact g32p_row13_cosetBranchStep_2133 s
  · exact g32p_row13_cosetBranchStep_2134 s
  · exact g32p_row13_cosetBranchStep_2135 s
  · exact g32p_row13_cosetBranchStep_2136 s
  · exact g32p_row13_cosetBranchStep_2137 s
  · exact g32p_row13_cosetBranchStep_2138 s
  · exact g32p_row13_cosetBranchStep_2139 s
  · exact g32p_row13_cosetBranchStep_2140 s
  · exact g32p_row13_cosetBranchStep_2141 s
  · exact g32p_row13_cosetBranchStep_2142 s
  · exact g32p_row13_cosetBranchStep_2143 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2144 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2144) = g32p_row13_cosetRepresentatives 2144 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2144 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2144) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2144))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2144)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2144 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2144) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2144))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2144)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2145 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2145) = g32p_row13_cosetRepresentatives 2145 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2145 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2145) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2145))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2145)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2145 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2145) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2145))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2145)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2146 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2146) = g32p_row13_cosetRepresentatives 2146 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2146 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2146) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2146))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2146)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2146 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2146) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2146))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2146)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2147 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2147) = g32p_row13_cosetRepresentatives 2147 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2147 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2147) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2147))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2147)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2147 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2147) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2147))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2147)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2148 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2148) = g32p_row13_cosetRepresentatives 2148 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2148 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2148) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2148))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2148)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2148 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2148) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2148))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2148)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2149 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2149) = g32p_row13_cosetRepresentatives 2149 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2149 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2149) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2149))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2149)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2149 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2149) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2149))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2149)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2150 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2150) = g32p_row13_cosetRepresentatives 2150 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2150 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2150) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2150))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2150)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2150 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2150) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2150))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2150)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2151 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2151) = g32p_row13_cosetRepresentatives 2151 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2151 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2151) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2151))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2151)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2151 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2151) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2151))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2151)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2152 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2152) = g32p_row13_cosetRepresentatives 2152 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2152 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2152) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2152))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2152)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2152 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2152) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2152))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2152)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2153 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2153) = g32p_row13_cosetRepresentatives 2153 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2153 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2153) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2153))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2153)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2153 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2153) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2153))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2153)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2154 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2154) = g32p_row13_cosetRepresentatives 2154 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2154 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2154) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2154))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2154)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2154 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2154) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2154))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2154)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2155 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2155) = g32p_row13_cosetRepresentatives 2155 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2155 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2155) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2155))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2155)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2155 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2155) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2155))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2155)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2156 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2156) = g32p_row13_cosetRepresentatives 2156 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2156 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2156) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2156))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2156)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2156 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2156) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2156))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2156)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2157 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2157) = g32p_row13_cosetRepresentatives 2157 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2157 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2157) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2157))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2157)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2157 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2157) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2157))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2157)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2158 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2158) = g32p_row13_cosetRepresentatives 2158 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2158 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2158) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2158))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2158)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2158 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2158) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2158))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2158)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2159 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2159) = g32p_row13_cosetRepresentatives 2159 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2159 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2159) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2159))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2159)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2159 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2159) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2159))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2159)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0134 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 134 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 134 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2144
  · exact g32p_row13_cosetWord_2145
  · exact g32p_row13_cosetWord_2146
  · exact g32p_row13_cosetWord_2147
  · exact g32p_row13_cosetWord_2148
  · exact g32p_row13_cosetWord_2149
  · exact g32p_row13_cosetWord_2150
  · exact g32p_row13_cosetWord_2151
  · exact g32p_row13_cosetWord_2152
  · exact g32p_row13_cosetWord_2153
  · exact g32p_row13_cosetWord_2154
  · exact g32p_row13_cosetWord_2155
  · exact g32p_row13_cosetWord_2156
  · exact g32p_row13_cosetWord_2157
  · exact g32p_row13_cosetWord_2158
  · exact g32p_row13_cosetWord_2159

theorem g32p_row13_cosetGeneratorBlock_0134 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 134 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 134 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 134 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2144 s
  · exact g32p_row13_cosetGeneratorStep_2145 s
  · exact g32p_row13_cosetGeneratorStep_2146 s
  · exact g32p_row13_cosetGeneratorStep_2147 s
  · exact g32p_row13_cosetGeneratorStep_2148 s
  · exact g32p_row13_cosetGeneratorStep_2149 s
  · exact g32p_row13_cosetGeneratorStep_2150 s
  · exact g32p_row13_cosetGeneratorStep_2151 s
  · exact g32p_row13_cosetGeneratorStep_2152 s
  · exact g32p_row13_cosetGeneratorStep_2153 s
  · exact g32p_row13_cosetGeneratorStep_2154 s
  · exact g32p_row13_cosetGeneratorStep_2155 s
  · exact g32p_row13_cosetGeneratorStep_2156 s
  · exact g32p_row13_cosetGeneratorStep_2157 s
  · exact g32p_row13_cosetGeneratorStep_2158 s
  · exact g32p_row13_cosetGeneratorStep_2159 s

theorem g32p_row13_cosetBranchBlock_0134 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 134 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 134 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 134 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2144 s
  · exact g32p_row13_cosetBranchStep_2145 s
  · exact g32p_row13_cosetBranchStep_2146 s
  · exact g32p_row13_cosetBranchStep_2147 s
  · exact g32p_row13_cosetBranchStep_2148 s
  · exact g32p_row13_cosetBranchStep_2149 s
  · exact g32p_row13_cosetBranchStep_2150 s
  · exact g32p_row13_cosetBranchStep_2151 s
  · exact g32p_row13_cosetBranchStep_2152 s
  · exact g32p_row13_cosetBranchStep_2153 s
  · exact g32p_row13_cosetBranchStep_2154 s
  · exact g32p_row13_cosetBranchStep_2155 s
  · exact g32p_row13_cosetBranchStep_2156 s
  · exact g32p_row13_cosetBranchStep_2157 s
  · exact g32p_row13_cosetBranchStep_2158 s
  · exact g32p_row13_cosetBranchStep_2159 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2160 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2160) = g32p_row13_cosetRepresentatives 2160 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2160 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2160) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2160))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2160)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2160 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2160) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2160))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2160)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2161 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2161) = g32p_row13_cosetRepresentatives 2161 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2161 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2161) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2161))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2161)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2161 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2161) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2161))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2161)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2162 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2162) = g32p_row13_cosetRepresentatives 2162 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2162 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2162) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2162))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2162)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2162 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2162) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2162))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2162)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2163 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2163) = g32p_row13_cosetRepresentatives 2163 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2163 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2163) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2163))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2163)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2163 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2163) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2163))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2163)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2164 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2164) = g32p_row13_cosetRepresentatives 2164 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2164 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2164) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2164))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2164)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2164 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2164) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2164))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2164)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2165 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2165) = g32p_row13_cosetRepresentatives 2165 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2165 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2165) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2165))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2165)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2165 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2165) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2165))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2165)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2166 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2166) = g32p_row13_cosetRepresentatives 2166 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2166 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2166) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2166))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2166)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2166 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2166) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2166))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2166)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2167 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2167) = g32p_row13_cosetRepresentatives 2167 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2167 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2167) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2167))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2167)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2167 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2167) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2167))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2167)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2168 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2168) = g32p_row13_cosetRepresentatives 2168 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2168 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2168) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2168))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2168)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2168 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2168) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2168))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2168)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2169 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2169) = g32p_row13_cosetRepresentatives 2169 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2169 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2169) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2169))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2169)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2169 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2169) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2169))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2169)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2170 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2170) = g32p_row13_cosetRepresentatives 2170 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2170 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2170) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2170))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2170)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2170 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2170) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2170))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2170)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2171 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2171) = g32p_row13_cosetRepresentatives 2171 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2171 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2171) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2171))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2171)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2171 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2171) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2171))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2171)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2172 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2172) = g32p_row13_cosetRepresentatives 2172 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2172 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2172) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2172))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2172)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2172 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2172) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2172))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2172)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2173 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2173) = g32p_row13_cosetRepresentatives 2173 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2173 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2173) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2173))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2173)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2173 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2173) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2173))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2173)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2174 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2174) = g32p_row13_cosetRepresentatives 2174 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2174 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2174) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2174))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2174)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2174 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2174) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2174))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2174)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2175 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2175) = g32p_row13_cosetRepresentatives 2175 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2175 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2175) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2175))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2175)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2175 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2175) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2175))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2175)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0135 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 135 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 135 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2160
  · exact g32p_row13_cosetWord_2161
  · exact g32p_row13_cosetWord_2162
  · exact g32p_row13_cosetWord_2163
  · exact g32p_row13_cosetWord_2164
  · exact g32p_row13_cosetWord_2165
  · exact g32p_row13_cosetWord_2166
  · exact g32p_row13_cosetWord_2167
  · exact g32p_row13_cosetWord_2168
  · exact g32p_row13_cosetWord_2169
  · exact g32p_row13_cosetWord_2170
  · exact g32p_row13_cosetWord_2171
  · exact g32p_row13_cosetWord_2172
  · exact g32p_row13_cosetWord_2173
  · exact g32p_row13_cosetWord_2174
  · exact g32p_row13_cosetWord_2175

theorem g32p_row13_cosetGeneratorBlock_0135 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 135 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 135 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 135 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2160 s
  · exact g32p_row13_cosetGeneratorStep_2161 s
  · exact g32p_row13_cosetGeneratorStep_2162 s
  · exact g32p_row13_cosetGeneratorStep_2163 s
  · exact g32p_row13_cosetGeneratorStep_2164 s
  · exact g32p_row13_cosetGeneratorStep_2165 s
  · exact g32p_row13_cosetGeneratorStep_2166 s
  · exact g32p_row13_cosetGeneratorStep_2167 s
  · exact g32p_row13_cosetGeneratorStep_2168 s
  · exact g32p_row13_cosetGeneratorStep_2169 s
  · exact g32p_row13_cosetGeneratorStep_2170 s
  · exact g32p_row13_cosetGeneratorStep_2171 s
  · exact g32p_row13_cosetGeneratorStep_2172 s
  · exact g32p_row13_cosetGeneratorStep_2173 s
  · exact g32p_row13_cosetGeneratorStep_2174 s
  · exact g32p_row13_cosetGeneratorStep_2175 s

theorem g32p_row13_cosetBranchBlock_0135 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 135 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 135 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 135 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2160 s
  · exact g32p_row13_cosetBranchStep_2161 s
  · exact g32p_row13_cosetBranchStep_2162 s
  · exact g32p_row13_cosetBranchStep_2163 s
  · exact g32p_row13_cosetBranchStep_2164 s
  · exact g32p_row13_cosetBranchStep_2165 s
  · exact g32p_row13_cosetBranchStep_2166 s
  · exact g32p_row13_cosetBranchStep_2167 s
  · exact g32p_row13_cosetBranchStep_2168 s
  · exact g32p_row13_cosetBranchStep_2169 s
  · exact g32p_row13_cosetBranchStep_2170 s
  · exact g32p_row13_cosetBranchStep_2171 s
  · exact g32p_row13_cosetBranchStep_2172 s
  · exact g32p_row13_cosetBranchStep_2173 s
  · exact g32p_row13_cosetBranchStep_2174 s
  · exact g32p_row13_cosetBranchStep_2175 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2176 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2176) = g32p_row13_cosetRepresentatives 2176 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2176 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2176) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2176))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2176)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2176 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2176) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2176))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2176)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2177 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2177) = g32p_row13_cosetRepresentatives 2177 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2177 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2177) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2177))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2177)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2177 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2177) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2177))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2177)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2178 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2178) = g32p_row13_cosetRepresentatives 2178 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2178 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2178) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2178))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2178)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2178 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2178) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2178))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2178)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2179 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2179) = g32p_row13_cosetRepresentatives 2179 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2179 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2179) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2179))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2179)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2179 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2179) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2179))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2179)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2180 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2180) = g32p_row13_cosetRepresentatives 2180 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2180 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2180) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2180))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2180)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2180 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2180) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2180))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2180)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2181 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2181) = g32p_row13_cosetRepresentatives 2181 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2181 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2181) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2181))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2181)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2181 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2181) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2181))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2181)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2182 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2182) = g32p_row13_cosetRepresentatives 2182 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2182 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2182) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2182))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2182)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2182 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2182) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2182))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2182)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2183 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2183) = g32p_row13_cosetRepresentatives 2183 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2183 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2183) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2183))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2183)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2183 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2183) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2183))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2183)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2184 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2184) = g32p_row13_cosetRepresentatives 2184 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2184 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2184) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2184))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2184)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2184 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2184) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2184))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2184)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2185 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2185) = g32p_row13_cosetRepresentatives 2185 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2185 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2185) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2185))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2185)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2185 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2185) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2185))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2185)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2186 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2186) = g32p_row13_cosetRepresentatives 2186 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2186 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2186) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2186))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2186)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2186 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2186) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2186))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2186)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2187 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2187) = g32p_row13_cosetRepresentatives 2187 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2187 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2187) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2187))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2187)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2187 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2187) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2187))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2187)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2188 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2188) = g32p_row13_cosetRepresentatives 2188 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2188 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2188) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2188))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2188)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2188 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2188) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2188))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2188)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2189 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2189) = g32p_row13_cosetRepresentatives 2189 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2189 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2189) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2189))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2189)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2189 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2189) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2189))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2189)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2190 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2190) = g32p_row13_cosetRepresentatives 2190 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2190 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2190) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2190))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2190)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2190 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2190) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2190))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2190)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2191 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2191) = g32p_row13_cosetRepresentatives 2191 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2191 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2191) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2191))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2191)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2191 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2191) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2191))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2191)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0136 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 136 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 136 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2176
  · exact g32p_row13_cosetWord_2177
  · exact g32p_row13_cosetWord_2178
  · exact g32p_row13_cosetWord_2179
  · exact g32p_row13_cosetWord_2180
  · exact g32p_row13_cosetWord_2181
  · exact g32p_row13_cosetWord_2182
  · exact g32p_row13_cosetWord_2183
  · exact g32p_row13_cosetWord_2184
  · exact g32p_row13_cosetWord_2185
  · exact g32p_row13_cosetWord_2186
  · exact g32p_row13_cosetWord_2187
  · exact g32p_row13_cosetWord_2188
  · exact g32p_row13_cosetWord_2189
  · exact g32p_row13_cosetWord_2190
  · exact g32p_row13_cosetWord_2191

theorem g32p_row13_cosetGeneratorBlock_0136 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 136 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 136 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 136 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2176 s
  · exact g32p_row13_cosetGeneratorStep_2177 s
  · exact g32p_row13_cosetGeneratorStep_2178 s
  · exact g32p_row13_cosetGeneratorStep_2179 s
  · exact g32p_row13_cosetGeneratorStep_2180 s
  · exact g32p_row13_cosetGeneratorStep_2181 s
  · exact g32p_row13_cosetGeneratorStep_2182 s
  · exact g32p_row13_cosetGeneratorStep_2183 s
  · exact g32p_row13_cosetGeneratorStep_2184 s
  · exact g32p_row13_cosetGeneratorStep_2185 s
  · exact g32p_row13_cosetGeneratorStep_2186 s
  · exact g32p_row13_cosetGeneratorStep_2187 s
  · exact g32p_row13_cosetGeneratorStep_2188 s
  · exact g32p_row13_cosetGeneratorStep_2189 s
  · exact g32p_row13_cosetGeneratorStep_2190 s
  · exact g32p_row13_cosetGeneratorStep_2191 s

theorem g32p_row13_cosetBranchBlock_0136 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 136 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 136 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 136 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2176 s
  · exact g32p_row13_cosetBranchStep_2177 s
  · exact g32p_row13_cosetBranchStep_2178 s
  · exact g32p_row13_cosetBranchStep_2179 s
  · exact g32p_row13_cosetBranchStep_2180 s
  · exact g32p_row13_cosetBranchStep_2181 s
  · exact g32p_row13_cosetBranchStep_2182 s
  · exact g32p_row13_cosetBranchStep_2183 s
  · exact g32p_row13_cosetBranchStep_2184 s
  · exact g32p_row13_cosetBranchStep_2185 s
  · exact g32p_row13_cosetBranchStep_2186 s
  · exact g32p_row13_cosetBranchStep_2187 s
  · exact g32p_row13_cosetBranchStep_2188 s
  · exact g32p_row13_cosetBranchStep_2189 s
  · exact g32p_row13_cosetBranchStep_2190 s
  · exact g32p_row13_cosetBranchStep_2191 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2192 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2192) = g32p_row13_cosetRepresentatives 2192 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2192 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2192) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2192))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2192)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2192 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2192) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2192))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2192)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2193 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2193) = g32p_row13_cosetRepresentatives 2193 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2193 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2193) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2193))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2193)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2193 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2193) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2193))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2193)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2194 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2194) = g32p_row13_cosetRepresentatives 2194 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2194 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2194) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2194))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2194)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2194 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2194) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2194))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2194)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2195 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2195) = g32p_row13_cosetRepresentatives 2195 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2195 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2195) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2195))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2195)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2195 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2195) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2195))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2195)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2196 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2196) = g32p_row13_cosetRepresentatives 2196 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2196 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2196) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2196))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2196)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2196 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2196) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2196))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2196)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2197 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2197) = g32p_row13_cosetRepresentatives 2197 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2197 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2197) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2197))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2197)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2197 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2197) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2197))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2197)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2198 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2198) = g32p_row13_cosetRepresentatives 2198 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2198 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2198) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2198))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2198)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2198 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2198) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2198))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2198)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2199 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2199) = g32p_row13_cosetRepresentatives 2199 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2199 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2199) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2199))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2199)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2199 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2199) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2199))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2199)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2200 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2200) = g32p_row13_cosetRepresentatives 2200 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2200 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2200) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2200))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2200)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2200 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2200) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2200))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2200)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2201 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2201) = g32p_row13_cosetRepresentatives 2201 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2201 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2201) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2201))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2201)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2201 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2201) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2201))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2201)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2202 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2202) = g32p_row13_cosetRepresentatives 2202 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2202 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2202) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2202))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2202)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2202 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2202) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2202))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2202)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2203 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2203) = g32p_row13_cosetRepresentatives 2203 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2203 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2203) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2203))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2203)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2203 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2203) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2203))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2203)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2204 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2204) = g32p_row13_cosetRepresentatives 2204 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2204 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2204) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2204))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2204)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2204 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2204) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2204))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2204)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2205 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2205) = g32p_row13_cosetRepresentatives 2205 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2205 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2205) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2205))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2205)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2205 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2205) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2205))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2205)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2206 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2206) = g32p_row13_cosetRepresentatives 2206 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2206 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2206) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2206))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2206)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2206 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2206) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2206))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2206)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2207 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2207) = g32p_row13_cosetRepresentatives 2207 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2207 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2207) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2207))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2207)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2207 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2207) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2207))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2207)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0137 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 137 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 137 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2192
  · exact g32p_row13_cosetWord_2193
  · exact g32p_row13_cosetWord_2194
  · exact g32p_row13_cosetWord_2195
  · exact g32p_row13_cosetWord_2196
  · exact g32p_row13_cosetWord_2197
  · exact g32p_row13_cosetWord_2198
  · exact g32p_row13_cosetWord_2199
  · exact g32p_row13_cosetWord_2200
  · exact g32p_row13_cosetWord_2201
  · exact g32p_row13_cosetWord_2202
  · exact g32p_row13_cosetWord_2203
  · exact g32p_row13_cosetWord_2204
  · exact g32p_row13_cosetWord_2205
  · exact g32p_row13_cosetWord_2206
  · exact g32p_row13_cosetWord_2207

theorem g32p_row13_cosetGeneratorBlock_0137 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 137 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 137 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 137 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2192 s
  · exact g32p_row13_cosetGeneratorStep_2193 s
  · exact g32p_row13_cosetGeneratorStep_2194 s
  · exact g32p_row13_cosetGeneratorStep_2195 s
  · exact g32p_row13_cosetGeneratorStep_2196 s
  · exact g32p_row13_cosetGeneratorStep_2197 s
  · exact g32p_row13_cosetGeneratorStep_2198 s
  · exact g32p_row13_cosetGeneratorStep_2199 s
  · exact g32p_row13_cosetGeneratorStep_2200 s
  · exact g32p_row13_cosetGeneratorStep_2201 s
  · exact g32p_row13_cosetGeneratorStep_2202 s
  · exact g32p_row13_cosetGeneratorStep_2203 s
  · exact g32p_row13_cosetGeneratorStep_2204 s
  · exact g32p_row13_cosetGeneratorStep_2205 s
  · exact g32p_row13_cosetGeneratorStep_2206 s
  · exact g32p_row13_cosetGeneratorStep_2207 s

theorem g32p_row13_cosetBranchBlock_0137 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 137 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 137 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 137 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2192 s
  · exact g32p_row13_cosetBranchStep_2193 s
  · exact g32p_row13_cosetBranchStep_2194 s
  · exact g32p_row13_cosetBranchStep_2195 s
  · exact g32p_row13_cosetBranchStep_2196 s
  · exact g32p_row13_cosetBranchStep_2197 s
  · exact g32p_row13_cosetBranchStep_2198 s
  · exact g32p_row13_cosetBranchStep_2199 s
  · exact g32p_row13_cosetBranchStep_2200 s
  · exact g32p_row13_cosetBranchStep_2201 s
  · exact g32p_row13_cosetBranchStep_2202 s
  · exact g32p_row13_cosetBranchStep_2203 s
  · exact g32p_row13_cosetBranchStep_2204 s
  · exact g32p_row13_cosetBranchStep_2205 s
  · exact g32p_row13_cosetBranchStep_2206 s
  · exact g32p_row13_cosetBranchStep_2207 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2208 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2208) = g32p_row13_cosetRepresentatives 2208 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2208 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2208) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2208))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2208)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2208 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2208) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2208))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2208)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2209 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2209) = g32p_row13_cosetRepresentatives 2209 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2209 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2209) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2209))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2209)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2209 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2209) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2209))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2209)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2210 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2210) = g32p_row13_cosetRepresentatives 2210 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2210 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2210) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2210))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2210)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2210 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2210) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2210))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2210)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2211 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2211) = g32p_row13_cosetRepresentatives 2211 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2211 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2211) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2211))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2211)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2211 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2211) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2211))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2211)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2212 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2212) = g32p_row13_cosetRepresentatives 2212 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2212 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2212) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2212))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2212)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2212 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2212) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2212))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2212)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2213 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2213) = g32p_row13_cosetRepresentatives 2213 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2213 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2213) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2213))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2213)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2213 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2213) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2213))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2213)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2214 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2214) = g32p_row13_cosetRepresentatives 2214 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2214 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2214) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2214))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2214)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2214 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2214) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2214))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2214)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2215 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2215) = g32p_row13_cosetRepresentatives 2215 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2215 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2215) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2215))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2215)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2215 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2215) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2215))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2215)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2216 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2216) = g32p_row13_cosetRepresentatives 2216 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2216 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2216) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2216))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2216)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2216 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2216) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2216))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2216)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2217 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2217) = g32p_row13_cosetRepresentatives 2217 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2217 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2217) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2217))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2217)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2217 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2217) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2217))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2217)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2218 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2218) = g32p_row13_cosetRepresentatives 2218 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2218 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2218) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2218))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2218)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2218 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2218) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2218))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2218)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2219 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2219) = g32p_row13_cosetRepresentatives 2219 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2219 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2219) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2219))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2219)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2219 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2219) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2219))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2219)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2220 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2220) = g32p_row13_cosetRepresentatives 2220 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2220 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2220) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2220))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2220)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2220 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2220) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2220))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2220)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2221 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2221) = g32p_row13_cosetRepresentatives 2221 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2221 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2221) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2221))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2221)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2221 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2221) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2221))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2221)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2222 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2222) = g32p_row13_cosetRepresentatives 2222 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2222 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2222) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2222))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2222)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2222 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2222) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2222))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2222)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2223 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2223) = g32p_row13_cosetRepresentatives 2223 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2223 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2223) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2223))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2223)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2223 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2223) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2223))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2223)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0138 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 138 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 138 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2208
  · exact g32p_row13_cosetWord_2209
  · exact g32p_row13_cosetWord_2210
  · exact g32p_row13_cosetWord_2211
  · exact g32p_row13_cosetWord_2212
  · exact g32p_row13_cosetWord_2213
  · exact g32p_row13_cosetWord_2214
  · exact g32p_row13_cosetWord_2215
  · exact g32p_row13_cosetWord_2216
  · exact g32p_row13_cosetWord_2217
  · exact g32p_row13_cosetWord_2218
  · exact g32p_row13_cosetWord_2219
  · exact g32p_row13_cosetWord_2220
  · exact g32p_row13_cosetWord_2221
  · exact g32p_row13_cosetWord_2222
  · exact g32p_row13_cosetWord_2223

theorem g32p_row13_cosetGeneratorBlock_0138 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 138 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 138 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 138 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2208 s
  · exact g32p_row13_cosetGeneratorStep_2209 s
  · exact g32p_row13_cosetGeneratorStep_2210 s
  · exact g32p_row13_cosetGeneratorStep_2211 s
  · exact g32p_row13_cosetGeneratorStep_2212 s
  · exact g32p_row13_cosetGeneratorStep_2213 s
  · exact g32p_row13_cosetGeneratorStep_2214 s
  · exact g32p_row13_cosetGeneratorStep_2215 s
  · exact g32p_row13_cosetGeneratorStep_2216 s
  · exact g32p_row13_cosetGeneratorStep_2217 s
  · exact g32p_row13_cosetGeneratorStep_2218 s
  · exact g32p_row13_cosetGeneratorStep_2219 s
  · exact g32p_row13_cosetGeneratorStep_2220 s
  · exact g32p_row13_cosetGeneratorStep_2221 s
  · exact g32p_row13_cosetGeneratorStep_2222 s
  · exact g32p_row13_cosetGeneratorStep_2223 s

theorem g32p_row13_cosetBranchBlock_0138 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 138 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 138 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 138 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2208 s
  · exact g32p_row13_cosetBranchStep_2209 s
  · exact g32p_row13_cosetBranchStep_2210 s
  · exact g32p_row13_cosetBranchStep_2211 s
  · exact g32p_row13_cosetBranchStep_2212 s
  · exact g32p_row13_cosetBranchStep_2213 s
  · exact g32p_row13_cosetBranchStep_2214 s
  · exact g32p_row13_cosetBranchStep_2215 s
  · exact g32p_row13_cosetBranchStep_2216 s
  · exact g32p_row13_cosetBranchStep_2217 s
  · exact g32p_row13_cosetBranchStep_2218 s
  · exact g32p_row13_cosetBranchStep_2219 s
  · exact g32p_row13_cosetBranchStep_2220 s
  · exact g32p_row13_cosetBranchStep_2221 s
  · exact g32p_row13_cosetBranchStep_2222 s
  · exact g32p_row13_cosetBranchStep_2223 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2224 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2224) = g32p_row13_cosetRepresentatives 2224 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2224 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2224) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2224))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2224)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2224 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2224) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2224))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2224)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2225 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2225) = g32p_row13_cosetRepresentatives 2225 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2225 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2225) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2225))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2225)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2225 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2225) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2225))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2225)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2226 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2226) = g32p_row13_cosetRepresentatives 2226 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2226 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2226) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2226))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2226)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2226 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2226) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2226))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2226)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2227 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2227) = g32p_row13_cosetRepresentatives 2227 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2227 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2227) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2227))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2227)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2227 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2227) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2227))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2227)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2228 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2228) = g32p_row13_cosetRepresentatives 2228 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2228 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2228) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2228))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2228)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2228 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2228) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2228))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2228)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2229 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2229) = g32p_row13_cosetRepresentatives 2229 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2229 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2229) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2229))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2229)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2229 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2229) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2229))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2229)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2230 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2230) = g32p_row13_cosetRepresentatives 2230 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2230 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2230) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2230))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2230)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2230 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2230) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2230))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2230)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2231 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2231) = g32p_row13_cosetRepresentatives 2231 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2231 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2231) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2231))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2231)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2231 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2231) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2231))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2231)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2232 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2232) = g32p_row13_cosetRepresentatives 2232 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2232 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2232) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2232))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2232)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2232 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2232) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2232))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2232)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2233 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2233) = g32p_row13_cosetRepresentatives 2233 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2233 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2233) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2233))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2233)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2233 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2233) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2233))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2233)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2234 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2234) = g32p_row13_cosetRepresentatives 2234 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2234 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2234) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2234))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2234)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2234 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2234) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2234))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2234)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2235 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2235) = g32p_row13_cosetRepresentatives 2235 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2235 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2235) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2235))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2235)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2235 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2235) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2235))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2235)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2236 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2236) = g32p_row13_cosetRepresentatives 2236 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2236 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2236) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2236))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2236)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2236 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2236) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2236))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2236)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2237 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2237) = g32p_row13_cosetRepresentatives 2237 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2237 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2237) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2237))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2237)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2237 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2237) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2237))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2237)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2238 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2238) = g32p_row13_cosetRepresentatives 2238 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2238 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2238) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2238))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2238)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2238 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2238) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2238))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2238)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2239 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2239) = g32p_row13_cosetRepresentatives 2239 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2239 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2239) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2239))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2239)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2239 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2239) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2239))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2239)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0139 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 139 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 139 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2224
  · exact g32p_row13_cosetWord_2225
  · exact g32p_row13_cosetWord_2226
  · exact g32p_row13_cosetWord_2227
  · exact g32p_row13_cosetWord_2228
  · exact g32p_row13_cosetWord_2229
  · exact g32p_row13_cosetWord_2230
  · exact g32p_row13_cosetWord_2231
  · exact g32p_row13_cosetWord_2232
  · exact g32p_row13_cosetWord_2233
  · exact g32p_row13_cosetWord_2234
  · exact g32p_row13_cosetWord_2235
  · exact g32p_row13_cosetWord_2236
  · exact g32p_row13_cosetWord_2237
  · exact g32p_row13_cosetWord_2238
  · exact g32p_row13_cosetWord_2239

theorem g32p_row13_cosetGeneratorBlock_0139 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 139 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 139 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 139 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2224 s
  · exact g32p_row13_cosetGeneratorStep_2225 s
  · exact g32p_row13_cosetGeneratorStep_2226 s
  · exact g32p_row13_cosetGeneratorStep_2227 s
  · exact g32p_row13_cosetGeneratorStep_2228 s
  · exact g32p_row13_cosetGeneratorStep_2229 s
  · exact g32p_row13_cosetGeneratorStep_2230 s
  · exact g32p_row13_cosetGeneratorStep_2231 s
  · exact g32p_row13_cosetGeneratorStep_2232 s
  · exact g32p_row13_cosetGeneratorStep_2233 s
  · exact g32p_row13_cosetGeneratorStep_2234 s
  · exact g32p_row13_cosetGeneratorStep_2235 s
  · exact g32p_row13_cosetGeneratorStep_2236 s
  · exact g32p_row13_cosetGeneratorStep_2237 s
  · exact g32p_row13_cosetGeneratorStep_2238 s
  · exact g32p_row13_cosetGeneratorStep_2239 s

theorem g32p_row13_cosetBranchBlock_0139 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 139 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 139 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 139 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2224 s
  · exact g32p_row13_cosetBranchStep_2225 s
  · exact g32p_row13_cosetBranchStep_2226 s
  · exact g32p_row13_cosetBranchStep_2227 s
  · exact g32p_row13_cosetBranchStep_2228 s
  · exact g32p_row13_cosetBranchStep_2229 s
  · exact g32p_row13_cosetBranchStep_2230 s
  · exact g32p_row13_cosetBranchStep_2231 s
  · exact g32p_row13_cosetBranchStep_2232 s
  · exact g32p_row13_cosetBranchStep_2233 s
  · exact g32p_row13_cosetBranchStep_2234 s
  · exact g32p_row13_cosetBranchStep_2235 s
  · exact g32p_row13_cosetBranchStep_2236 s
  · exact g32p_row13_cosetBranchStep_2237 s
  · exact g32p_row13_cosetBranchStep_2238 s
  · exact g32p_row13_cosetBranchStep_2239 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2240 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2240) = g32p_row13_cosetRepresentatives 2240 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2240 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2240) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2240))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2240)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2240 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2240) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2240))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2240)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2241 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2241) = g32p_row13_cosetRepresentatives 2241 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2241 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2241) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2241))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2241)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2241 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2241) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2241))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2241)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2242 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2242) = g32p_row13_cosetRepresentatives 2242 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2242 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2242) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2242))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2242)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2242 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2242) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2242))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2242)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2243 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2243) = g32p_row13_cosetRepresentatives 2243 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2243 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2243) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2243))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2243)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2243 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2243) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2243))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2243)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2244 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2244) = g32p_row13_cosetRepresentatives 2244 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2244 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2244) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2244))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2244)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2244 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2244) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2244))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2244)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2245 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2245) = g32p_row13_cosetRepresentatives 2245 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2245 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2245) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2245))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2245)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2245 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2245) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2245))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2245)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2246 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2246) = g32p_row13_cosetRepresentatives 2246 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2246 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2246) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2246))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2246)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2246 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2246) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2246))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2246)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2247 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2247) = g32p_row13_cosetRepresentatives 2247 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2247 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2247) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2247))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2247)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2247 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2247) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2247))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2247)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2248 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2248) = g32p_row13_cosetRepresentatives 2248 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2248 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2248) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2248))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2248)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2248 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2248) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2248))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2248)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2249 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2249) = g32p_row13_cosetRepresentatives 2249 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2249 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2249) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2249))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2249)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2249 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2249) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2249))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2249)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2250 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2250) = g32p_row13_cosetRepresentatives 2250 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2250 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2250) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2250))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2250)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2250 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2250) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2250))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2250)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2251 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2251) = g32p_row13_cosetRepresentatives 2251 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2251 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2251) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2251))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2251)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2251 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2251) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2251))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2251)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2252 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2252) = g32p_row13_cosetRepresentatives 2252 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2252 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2252) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2252))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2252)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2252 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2252) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2252))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2252)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2253 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2253) = g32p_row13_cosetRepresentatives 2253 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2253 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2253) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2253))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2253)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2253 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2253) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2253))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2253)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2254 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2254) = g32p_row13_cosetRepresentatives 2254 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2254 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2254) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2254))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2254)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2254 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2254) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2254))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2254)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2255 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2255) = g32p_row13_cosetRepresentatives 2255 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2255 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2255) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2255))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2255)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2255 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2255) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2255))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2255)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0140 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 140 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 140 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2240
  · exact g32p_row13_cosetWord_2241
  · exact g32p_row13_cosetWord_2242
  · exact g32p_row13_cosetWord_2243
  · exact g32p_row13_cosetWord_2244
  · exact g32p_row13_cosetWord_2245
  · exact g32p_row13_cosetWord_2246
  · exact g32p_row13_cosetWord_2247
  · exact g32p_row13_cosetWord_2248
  · exact g32p_row13_cosetWord_2249
  · exact g32p_row13_cosetWord_2250
  · exact g32p_row13_cosetWord_2251
  · exact g32p_row13_cosetWord_2252
  · exact g32p_row13_cosetWord_2253
  · exact g32p_row13_cosetWord_2254
  · exact g32p_row13_cosetWord_2255

theorem g32p_row13_cosetGeneratorBlock_0140 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 140 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 140 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 140 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2240 s
  · exact g32p_row13_cosetGeneratorStep_2241 s
  · exact g32p_row13_cosetGeneratorStep_2242 s
  · exact g32p_row13_cosetGeneratorStep_2243 s
  · exact g32p_row13_cosetGeneratorStep_2244 s
  · exact g32p_row13_cosetGeneratorStep_2245 s
  · exact g32p_row13_cosetGeneratorStep_2246 s
  · exact g32p_row13_cosetGeneratorStep_2247 s
  · exact g32p_row13_cosetGeneratorStep_2248 s
  · exact g32p_row13_cosetGeneratorStep_2249 s
  · exact g32p_row13_cosetGeneratorStep_2250 s
  · exact g32p_row13_cosetGeneratorStep_2251 s
  · exact g32p_row13_cosetGeneratorStep_2252 s
  · exact g32p_row13_cosetGeneratorStep_2253 s
  · exact g32p_row13_cosetGeneratorStep_2254 s
  · exact g32p_row13_cosetGeneratorStep_2255 s

theorem g32p_row13_cosetBranchBlock_0140 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 140 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 140 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 140 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2240 s
  · exact g32p_row13_cosetBranchStep_2241 s
  · exact g32p_row13_cosetBranchStep_2242 s
  · exact g32p_row13_cosetBranchStep_2243 s
  · exact g32p_row13_cosetBranchStep_2244 s
  · exact g32p_row13_cosetBranchStep_2245 s
  · exact g32p_row13_cosetBranchStep_2246 s
  · exact g32p_row13_cosetBranchStep_2247 s
  · exact g32p_row13_cosetBranchStep_2248 s
  · exact g32p_row13_cosetBranchStep_2249 s
  · exact g32p_row13_cosetBranchStep_2250 s
  · exact g32p_row13_cosetBranchStep_2251 s
  · exact g32p_row13_cosetBranchStep_2252 s
  · exact g32p_row13_cosetBranchStep_2253 s
  · exact g32p_row13_cosetBranchStep_2254 s
  · exact g32p_row13_cosetBranchStep_2255 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2256 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2256) = g32p_row13_cosetRepresentatives 2256 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2256) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2256))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2256)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2256) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2256))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2256)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2257 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2257) = g32p_row13_cosetRepresentatives 2257 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2257) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2257))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2257)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2257) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2257))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2257)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2258 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2258) = g32p_row13_cosetRepresentatives 2258 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2258) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2258))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2258)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2258) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2258))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2258)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2259 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2259) = g32p_row13_cosetRepresentatives 2259 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2259) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2259))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2259)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2259) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2259))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2259)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2260 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2260) = g32p_row13_cosetRepresentatives 2260 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2260) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2260))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2260)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2260) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2260))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2260)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2261 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2261) = g32p_row13_cosetRepresentatives 2261 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2261) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2261))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2261)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2261) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2261))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2261)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2262 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2262) = g32p_row13_cosetRepresentatives 2262 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2262) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2262))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2262)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2262) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2262))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2262)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2263 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2263) = g32p_row13_cosetRepresentatives 2263 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2263) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2263))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2263)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2263) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2263))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2263)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2264 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2264) = g32p_row13_cosetRepresentatives 2264 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2264) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2264))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2264)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2264) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2264))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2264)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2265 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2265) = g32p_row13_cosetRepresentatives 2265 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2265) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2265))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2265)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2265) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2265))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2265)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2266 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2266) = g32p_row13_cosetRepresentatives 2266 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2266) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2266))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2266)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2266) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2266))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2266)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2267 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2267) = g32p_row13_cosetRepresentatives 2267 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2267) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2267))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2267)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2267) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2267))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2267)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2268 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2268) = g32p_row13_cosetRepresentatives 2268 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2268) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2268))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2268)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2268) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2268))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2268)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2269 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2269) = g32p_row13_cosetRepresentatives 2269 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2269) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2269))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2269)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2269) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2269))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2269)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2270 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2270) = g32p_row13_cosetRepresentatives 2270 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2270) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2270))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2270)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2270) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2270))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2270)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2271 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2271) = g32p_row13_cosetRepresentatives 2271 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2271) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2271))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2271)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2271) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2271))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2271)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0141 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 141 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 141 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2256
  · exact g32p_row13_cosetWord_2257
  · exact g32p_row13_cosetWord_2258
  · exact g32p_row13_cosetWord_2259
  · exact g32p_row13_cosetWord_2260
  · exact g32p_row13_cosetWord_2261
  · exact g32p_row13_cosetWord_2262
  · exact g32p_row13_cosetWord_2263
  · exact g32p_row13_cosetWord_2264
  · exact g32p_row13_cosetWord_2265
  · exact g32p_row13_cosetWord_2266
  · exact g32p_row13_cosetWord_2267
  · exact g32p_row13_cosetWord_2268
  · exact g32p_row13_cosetWord_2269
  · exact g32p_row13_cosetWord_2270
  · exact g32p_row13_cosetWord_2271

theorem g32p_row13_cosetGeneratorBlock_0141 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 141 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 141 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 141 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2256 s
  · exact g32p_row13_cosetGeneratorStep_2257 s
  · exact g32p_row13_cosetGeneratorStep_2258 s
  · exact g32p_row13_cosetGeneratorStep_2259 s
  · exact g32p_row13_cosetGeneratorStep_2260 s
  · exact g32p_row13_cosetGeneratorStep_2261 s
  · exact g32p_row13_cosetGeneratorStep_2262 s
  · exact g32p_row13_cosetGeneratorStep_2263 s
  · exact g32p_row13_cosetGeneratorStep_2264 s
  · exact g32p_row13_cosetGeneratorStep_2265 s
  · exact g32p_row13_cosetGeneratorStep_2266 s
  · exact g32p_row13_cosetGeneratorStep_2267 s
  · exact g32p_row13_cosetGeneratorStep_2268 s
  · exact g32p_row13_cosetGeneratorStep_2269 s
  · exact g32p_row13_cosetGeneratorStep_2270 s
  · exact g32p_row13_cosetGeneratorStep_2271 s

theorem g32p_row13_cosetBranchBlock_0141 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 141 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 141 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 141 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2256 s
  · exact g32p_row13_cosetBranchStep_2257 s
  · exact g32p_row13_cosetBranchStep_2258 s
  · exact g32p_row13_cosetBranchStep_2259 s
  · exact g32p_row13_cosetBranchStep_2260 s
  · exact g32p_row13_cosetBranchStep_2261 s
  · exact g32p_row13_cosetBranchStep_2262 s
  · exact g32p_row13_cosetBranchStep_2263 s
  · exact g32p_row13_cosetBranchStep_2264 s
  · exact g32p_row13_cosetBranchStep_2265 s
  · exact g32p_row13_cosetBranchStep_2266 s
  · exact g32p_row13_cosetBranchStep_2267 s
  · exact g32p_row13_cosetBranchStep_2268 s
  · exact g32p_row13_cosetBranchStep_2269 s
  · exact g32p_row13_cosetBranchStep_2270 s
  · exact g32p_row13_cosetBranchStep_2271 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2272 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2272) = g32p_row13_cosetRepresentatives 2272 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2272) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2272))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2272)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2272) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2272))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2272)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2273 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2273) = g32p_row13_cosetRepresentatives 2273 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2273) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2273))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2273)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2273) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2273))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2273)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2274 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2274) = g32p_row13_cosetRepresentatives 2274 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2274) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2274))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2274)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2274) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2274))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2274)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2275 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2275) = g32p_row13_cosetRepresentatives 2275 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2275) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2275))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2275)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2275) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2275))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2275)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2276 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2276) = g32p_row13_cosetRepresentatives 2276 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2276) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2276))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2276)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2276) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2276))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2276)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2277 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2277) = g32p_row13_cosetRepresentatives 2277 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2277) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2277))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2277)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2277) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2277))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2277)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2278 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2278) = g32p_row13_cosetRepresentatives 2278 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2278) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2278))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2278)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2278) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2278))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2278)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2279 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2279) = g32p_row13_cosetRepresentatives 2279 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2279) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2279))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2279)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2279) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2279))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2279)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2280 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2280) = g32p_row13_cosetRepresentatives 2280 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2280) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2280))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2280)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2280) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2280))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2280)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2281 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2281) = g32p_row13_cosetRepresentatives 2281 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2281) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2281))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2281)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2281) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2281))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2281)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2282 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2282) = g32p_row13_cosetRepresentatives 2282 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2282) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2282))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2282)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2282) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2282))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2282)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2283 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2283) = g32p_row13_cosetRepresentatives 2283 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2283) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2283))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2283)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2283) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2283))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2283)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2284 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2284) = g32p_row13_cosetRepresentatives 2284 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2284) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2284))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2284)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2284) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2284))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2284)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2285 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2285) = g32p_row13_cosetRepresentatives 2285 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2285) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2285))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2285)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2285) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2285))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2285)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2286 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2286) = g32p_row13_cosetRepresentatives 2286 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2286) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2286))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2286)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2286) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2286))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2286)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2287 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2287) = g32p_row13_cosetRepresentatives 2287 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2287) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2287))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2287)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2287) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2287))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2287)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0142 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 142 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 142 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2272
  · exact g32p_row13_cosetWord_2273
  · exact g32p_row13_cosetWord_2274
  · exact g32p_row13_cosetWord_2275
  · exact g32p_row13_cosetWord_2276
  · exact g32p_row13_cosetWord_2277
  · exact g32p_row13_cosetWord_2278
  · exact g32p_row13_cosetWord_2279
  · exact g32p_row13_cosetWord_2280
  · exact g32p_row13_cosetWord_2281
  · exact g32p_row13_cosetWord_2282
  · exact g32p_row13_cosetWord_2283
  · exact g32p_row13_cosetWord_2284
  · exact g32p_row13_cosetWord_2285
  · exact g32p_row13_cosetWord_2286
  · exact g32p_row13_cosetWord_2287

theorem g32p_row13_cosetGeneratorBlock_0142 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 142 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 142 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 142 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2272 s
  · exact g32p_row13_cosetGeneratorStep_2273 s
  · exact g32p_row13_cosetGeneratorStep_2274 s
  · exact g32p_row13_cosetGeneratorStep_2275 s
  · exact g32p_row13_cosetGeneratorStep_2276 s
  · exact g32p_row13_cosetGeneratorStep_2277 s
  · exact g32p_row13_cosetGeneratorStep_2278 s
  · exact g32p_row13_cosetGeneratorStep_2279 s
  · exact g32p_row13_cosetGeneratorStep_2280 s
  · exact g32p_row13_cosetGeneratorStep_2281 s
  · exact g32p_row13_cosetGeneratorStep_2282 s
  · exact g32p_row13_cosetGeneratorStep_2283 s
  · exact g32p_row13_cosetGeneratorStep_2284 s
  · exact g32p_row13_cosetGeneratorStep_2285 s
  · exact g32p_row13_cosetGeneratorStep_2286 s
  · exact g32p_row13_cosetGeneratorStep_2287 s

theorem g32p_row13_cosetBranchBlock_0142 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 142 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 142 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 142 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2272 s
  · exact g32p_row13_cosetBranchStep_2273 s
  · exact g32p_row13_cosetBranchStep_2274 s
  · exact g32p_row13_cosetBranchStep_2275 s
  · exact g32p_row13_cosetBranchStep_2276 s
  · exact g32p_row13_cosetBranchStep_2277 s
  · exact g32p_row13_cosetBranchStep_2278 s
  · exact g32p_row13_cosetBranchStep_2279 s
  · exact g32p_row13_cosetBranchStep_2280 s
  · exact g32p_row13_cosetBranchStep_2281 s
  · exact g32p_row13_cosetBranchStep_2282 s
  · exact g32p_row13_cosetBranchStep_2283 s
  · exact g32p_row13_cosetBranchStep_2284 s
  · exact g32p_row13_cosetBranchStep_2285 s
  · exact g32p_row13_cosetBranchStep_2286 s
  · exact g32p_row13_cosetBranchStep_2287 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_2288 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2288) = g32p_row13_cosetRepresentatives 2288 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2288) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2288))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2288)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2288) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2288))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2288)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2289 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2289) = g32p_row13_cosetRepresentatives 2289 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2289) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2289))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2289)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2289) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2289))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2289)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2290 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2290) = g32p_row13_cosetRepresentatives 2290 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2290) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2290))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2290)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2290) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2290))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2290)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2291 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2291) = g32p_row13_cosetRepresentatives 2291 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2291) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2291))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2291)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2291) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2291))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2291)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2292 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2292) = g32p_row13_cosetRepresentatives 2292 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2292) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2292))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2292)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2292) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2292))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2292)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2293 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2293) = g32p_row13_cosetRepresentatives 2293 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2293) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2293))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2293)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2293) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2293))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2293)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2294 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2294) = g32p_row13_cosetRepresentatives 2294 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2294) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2294))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2294)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2294) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2294))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2294)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2295 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2295) = g32p_row13_cosetRepresentatives 2295 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2295) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2295))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2295)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2295) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2295))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2295)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2296 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2296) = g32p_row13_cosetRepresentatives 2296 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2296) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2296))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2296)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2296) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2296))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2296)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2297 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2297) = g32p_row13_cosetRepresentatives 2297 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2297) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2297))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2297)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2297) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2297))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2297)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2298 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2298) = g32p_row13_cosetRepresentatives 2298 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2298) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2298))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2298)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2298) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2298))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2298)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2299 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2299) = g32p_row13_cosetRepresentatives 2299 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2299) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2299))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2299)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2299) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2299))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2299)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2300 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2300) = g32p_row13_cosetRepresentatives 2300 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2300) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2300))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2300)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2300) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2300))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2300)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2301 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2301) = g32p_row13_cosetRepresentatives 2301 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2301) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2301))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2301)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2301) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2301))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2301)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2302 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2302) = g32p_row13_cosetRepresentatives 2302 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2302) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2302))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2302)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2302) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2302))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2302)) := by
  decide +kernel

theorem g32p_row13_cosetWord_2303 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 2303) = g32p_row13_cosetRepresentatives 2303 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_2303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 2303) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 2303))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 2303)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_2303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 2303) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 2303))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 2303)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0143 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 143 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 143 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_2288
  · exact g32p_row13_cosetWord_2289
  · exact g32p_row13_cosetWord_2290
  · exact g32p_row13_cosetWord_2291
  · exact g32p_row13_cosetWord_2292
  · exact g32p_row13_cosetWord_2293
  · exact g32p_row13_cosetWord_2294
  · exact g32p_row13_cosetWord_2295
  · exact g32p_row13_cosetWord_2296
  · exact g32p_row13_cosetWord_2297
  · exact g32p_row13_cosetWord_2298
  · exact g32p_row13_cosetWord_2299
  · exact g32p_row13_cosetWord_2300
  · exact g32p_row13_cosetWord_2301
  · exact g32p_row13_cosetWord_2302
  · exact g32p_row13_cosetWord_2303

theorem g32p_row13_cosetGeneratorBlock_0143 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 143 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 143 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 143 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_2288 s
  · exact g32p_row13_cosetGeneratorStep_2289 s
  · exact g32p_row13_cosetGeneratorStep_2290 s
  · exact g32p_row13_cosetGeneratorStep_2291 s
  · exact g32p_row13_cosetGeneratorStep_2292 s
  · exact g32p_row13_cosetGeneratorStep_2293 s
  · exact g32p_row13_cosetGeneratorStep_2294 s
  · exact g32p_row13_cosetGeneratorStep_2295 s
  · exact g32p_row13_cosetGeneratorStep_2296 s
  · exact g32p_row13_cosetGeneratorStep_2297 s
  · exact g32p_row13_cosetGeneratorStep_2298 s
  · exact g32p_row13_cosetGeneratorStep_2299 s
  · exact g32p_row13_cosetGeneratorStep_2300 s
  · exact g32p_row13_cosetGeneratorStep_2301 s
  · exact g32p_row13_cosetGeneratorStep_2302 s
  · exact g32p_row13_cosetGeneratorStep_2303 s

theorem g32p_row13_cosetBranchBlock_0143 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 143 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 143 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 143 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_2288 s
  · exact g32p_row13_cosetBranchStep_2289 s
  · exact g32p_row13_cosetBranchStep_2290 s
  · exact g32p_row13_cosetBranchStep_2291 s
  · exact g32p_row13_cosetBranchStep_2292 s
  · exact g32p_row13_cosetBranchStep_2293 s
  · exact g32p_row13_cosetBranchStep_2294 s
  · exact g32p_row13_cosetBranchStep_2295 s
  · exact g32p_row13_cosetBranchStep_2296 s
  · exact g32p_row13_cosetBranchStep_2297 s
  · exact g32p_row13_cosetBranchStep_2298 s
  · exact g32p_row13_cosetBranchStep_2299 s
  · exact g32p_row13_cosetBranchStep_2300 s
  · exact g32p_row13_cosetBranchStep_2301 s
  · exact g32p_row13_cosetBranchStep_2302 s
  · exact g32p_row13_cosetBranchStep_2303 s


end HodgeLean.Foundations.Program

end
