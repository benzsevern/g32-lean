import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked1044

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6144 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6144) = g32p_row13_cosetRepresentatives 6144 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6144 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6144) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6144))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6144)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6144 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6144) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6144))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6144)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6145 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6145) = g32p_row13_cosetRepresentatives 6145 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6145 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6145) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6145))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6145)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6145 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6145) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6145))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6145)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6146 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6146) = g32p_row13_cosetRepresentatives 6146 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6146 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6146) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6146))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6146)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6146 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6146) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6146))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6146)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6147 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6147) = g32p_row13_cosetRepresentatives 6147 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6147 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6147) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6147))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6147)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6147 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6147) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6147))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6147)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6148 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6148) = g32p_row13_cosetRepresentatives 6148 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6148 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6148) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6148))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6148)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6148 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6148) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6148))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6148)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6149 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6149) = g32p_row13_cosetRepresentatives 6149 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6149 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6149) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6149))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6149)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6149 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6149) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6149))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6149)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6150 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6150) = g32p_row13_cosetRepresentatives 6150 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6150 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6150) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6150))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6150)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6150 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6150) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6150))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6150)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6151 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6151) = g32p_row13_cosetRepresentatives 6151 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6151 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6151) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6151))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6151)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6151 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6151) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6151))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6151)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6152 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6152) = g32p_row13_cosetRepresentatives 6152 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6152 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6152) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6152))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6152)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6152 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6152) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6152))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6152)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6153 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6153) = g32p_row13_cosetRepresentatives 6153 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6153 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6153) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6153))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6153)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6153 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6153) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6153))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6153)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6154 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6154) = g32p_row13_cosetRepresentatives 6154 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6154 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6154) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6154))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6154)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6154 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6154) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6154))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6154)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6155 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6155) = g32p_row13_cosetRepresentatives 6155 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6155 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6155) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6155))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6155)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6155 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6155) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6155))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6155)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6156 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6156) = g32p_row13_cosetRepresentatives 6156 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6156 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6156) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6156))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6156)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6156 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6156) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6156))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6156)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6157 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6157) = g32p_row13_cosetRepresentatives 6157 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6157 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6157) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6157))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6157)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6157 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6157) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6157))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6157)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6158 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6158) = g32p_row13_cosetRepresentatives 6158 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6158 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6158) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6158))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6158)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6158 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6158) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6158))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6158)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6159 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6159) = g32p_row13_cosetRepresentatives 6159 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6159 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6159) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6159))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6159)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6159 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6159) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6159))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6159)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0384 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 384 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 384 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6144
  · exact g32p_row13_cosetWord_6145
  · exact g32p_row13_cosetWord_6146
  · exact g32p_row13_cosetWord_6147
  · exact g32p_row13_cosetWord_6148
  · exact g32p_row13_cosetWord_6149
  · exact g32p_row13_cosetWord_6150
  · exact g32p_row13_cosetWord_6151
  · exact g32p_row13_cosetWord_6152
  · exact g32p_row13_cosetWord_6153
  · exact g32p_row13_cosetWord_6154
  · exact g32p_row13_cosetWord_6155
  · exact g32p_row13_cosetWord_6156
  · exact g32p_row13_cosetWord_6157
  · exact g32p_row13_cosetWord_6158
  · exact g32p_row13_cosetWord_6159

theorem g32p_row13_cosetGeneratorBlock_0384 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 384 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 384 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 384 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6144 s
  · exact g32p_row13_cosetGeneratorStep_6145 s
  · exact g32p_row13_cosetGeneratorStep_6146 s
  · exact g32p_row13_cosetGeneratorStep_6147 s
  · exact g32p_row13_cosetGeneratorStep_6148 s
  · exact g32p_row13_cosetGeneratorStep_6149 s
  · exact g32p_row13_cosetGeneratorStep_6150 s
  · exact g32p_row13_cosetGeneratorStep_6151 s
  · exact g32p_row13_cosetGeneratorStep_6152 s
  · exact g32p_row13_cosetGeneratorStep_6153 s
  · exact g32p_row13_cosetGeneratorStep_6154 s
  · exact g32p_row13_cosetGeneratorStep_6155 s
  · exact g32p_row13_cosetGeneratorStep_6156 s
  · exact g32p_row13_cosetGeneratorStep_6157 s
  · exact g32p_row13_cosetGeneratorStep_6158 s
  · exact g32p_row13_cosetGeneratorStep_6159 s

theorem g32p_row13_cosetBranchBlock_0384 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 384 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 384 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 384 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6144 s
  · exact g32p_row13_cosetBranchStep_6145 s
  · exact g32p_row13_cosetBranchStep_6146 s
  · exact g32p_row13_cosetBranchStep_6147 s
  · exact g32p_row13_cosetBranchStep_6148 s
  · exact g32p_row13_cosetBranchStep_6149 s
  · exact g32p_row13_cosetBranchStep_6150 s
  · exact g32p_row13_cosetBranchStep_6151 s
  · exact g32p_row13_cosetBranchStep_6152 s
  · exact g32p_row13_cosetBranchStep_6153 s
  · exact g32p_row13_cosetBranchStep_6154 s
  · exact g32p_row13_cosetBranchStep_6155 s
  · exact g32p_row13_cosetBranchStep_6156 s
  · exact g32p_row13_cosetBranchStep_6157 s
  · exact g32p_row13_cosetBranchStep_6158 s
  · exact g32p_row13_cosetBranchStep_6159 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6160 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6160) = g32p_row13_cosetRepresentatives 6160 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6160 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6160) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6160))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6160)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6160 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6160) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6160))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6160)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6161 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6161) = g32p_row13_cosetRepresentatives 6161 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6161 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6161) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6161))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6161)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6161 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6161) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6161))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6161)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6162 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6162) = g32p_row13_cosetRepresentatives 6162 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6162 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6162) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6162))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6162)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6162 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6162) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6162))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6162)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6163 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6163) = g32p_row13_cosetRepresentatives 6163 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6163 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6163) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6163))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6163)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6163 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6163) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6163))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6163)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6164 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6164) = g32p_row13_cosetRepresentatives 6164 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6164 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6164) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6164))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6164)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6164 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6164) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6164))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6164)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6165 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6165) = g32p_row13_cosetRepresentatives 6165 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6165 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6165) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6165))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6165)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6165 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6165) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6165))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6165)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6166 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6166) = g32p_row13_cosetRepresentatives 6166 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6166 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6166) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6166))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6166)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6166 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6166) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6166))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6166)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6167 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6167) = g32p_row13_cosetRepresentatives 6167 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6167 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6167) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6167))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6167)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6167 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6167) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6167))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6167)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6168 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6168) = g32p_row13_cosetRepresentatives 6168 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6168 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6168) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6168))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6168)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6168 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6168) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6168))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6168)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6169 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6169) = g32p_row13_cosetRepresentatives 6169 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6169 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6169) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6169))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6169)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6169 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6169) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6169))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6169)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6170 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6170) = g32p_row13_cosetRepresentatives 6170 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6170 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6170) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6170))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6170)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6170 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6170) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6170))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6170)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6171 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6171) = g32p_row13_cosetRepresentatives 6171 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6171 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6171) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6171))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6171)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6171 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6171) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6171))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6171)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6172 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6172) = g32p_row13_cosetRepresentatives 6172 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6172 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6172) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6172))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6172)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6172 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6172) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6172))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6172)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6173 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6173) = g32p_row13_cosetRepresentatives 6173 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6173 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6173) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6173))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6173)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6173 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6173) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6173))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6173)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6174 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6174) = g32p_row13_cosetRepresentatives 6174 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6174 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6174) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6174))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6174)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6174 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6174) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6174))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6174)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6175 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6175) = g32p_row13_cosetRepresentatives 6175 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6175 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6175) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6175))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6175)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6175 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6175) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6175))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6175)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0385 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 385 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 385 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6160
  · exact g32p_row13_cosetWord_6161
  · exact g32p_row13_cosetWord_6162
  · exact g32p_row13_cosetWord_6163
  · exact g32p_row13_cosetWord_6164
  · exact g32p_row13_cosetWord_6165
  · exact g32p_row13_cosetWord_6166
  · exact g32p_row13_cosetWord_6167
  · exact g32p_row13_cosetWord_6168
  · exact g32p_row13_cosetWord_6169
  · exact g32p_row13_cosetWord_6170
  · exact g32p_row13_cosetWord_6171
  · exact g32p_row13_cosetWord_6172
  · exact g32p_row13_cosetWord_6173
  · exact g32p_row13_cosetWord_6174
  · exact g32p_row13_cosetWord_6175

theorem g32p_row13_cosetGeneratorBlock_0385 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 385 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 385 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 385 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6160 s
  · exact g32p_row13_cosetGeneratorStep_6161 s
  · exact g32p_row13_cosetGeneratorStep_6162 s
  · exact g32p_row13_cosetGeneratorStep_6163 s
  · exact g32p_row13_cosetGeneratorStep_6164 s
  · exact g32p_row13_cosetGeneratorStep_6165 s
  · exact g32p_row13_cosetGeneratorStep_6166 s
  · exact g32p_row13_cosetGeneratorStep_6167 s
  · exact g32p_row13_cosetGeneratorStep_6168 s
  · exact g32p_row13_cosetGeneratorStep_6169 s
  · exact g32p_row13_cosetGeneratorStep_6170 s
  · exact g32p_row13_cosetGeneratorStep_6171 s
  · exact g32p_row13_cosetGeneratorStep_6172 s
  · exact g32p_row13_cosetGeneratorStep_6173 s
  · exact g32p_row13_cosetGeneratorStep_6174 s
  · exact g32p_row13_cosetGeneratorStep_6175 s

theorem g32p_row13_cosetBranchBlock_0385 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 385 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 385 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 385 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6160 s
  · exact g32p_row13_cosetBranchStep_6161 s
  · exact g32p_row13_cosetBranchStep_6162 s
  · exact g32p_row13_cosetBranchStep_6163 s
  · exact g32p_row13_cosetBranchStep_6164 s
  · exact g32p_row13_cosetBranchStep_6165 s
  · exact g32p_row13_cosetBranchStep_6166 s
  · exact g32p_row13_cosetBranchStep_6167 s
  · exact g32p_row13_cosetBranchStep_6168 s
  · exact g32p_row13_cosetBranchStep_6169 s
  · exact g32p_row13_cosetBranchStep_6170 s
  · exact g32p_row13_cosetBranchStep_6171 s
  · exact g32p_row13_cosetBranchStep_6172 s
  · exact g32p_row13_cosetBranchStep_6173 s
  · exact g32p_row13_cosetBranchStep_6174 s
  · exact g32p_row13_cosetBranchStep_6175 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6176 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6176) = g32p_row13_cosetRepresentatives 6176 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6176 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6176) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6176))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6176)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6176 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6176) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6176))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6176)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6177 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6177) = g32p_row13_cosetRepresentatives 6177 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6177 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6177) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6177))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6177)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6177 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6177) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6177))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6177)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6178 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6178) = g32p_row13_cosetRepresentatives 6178 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6178 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6178) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6178))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6178)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6178 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6178) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6178))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6178)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6179 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6179) = g32p_row13_cosetRepresentatives 6179 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6179 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6179) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6179))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6179)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6179 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6179) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6179))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6179)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6180 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6180) = g32p_row13_cosetRepresentatives 6180 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6180 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6180) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6180))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6180)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6180 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6180) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6180))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6180)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6181 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6181) = g32p_row13_cosetRepresentatives 6181 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6181 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6181) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6181))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6181)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6181 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6181) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6181))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6181)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6182 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6182) = g32p_row13_cosetRepresentatives 6182 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6182 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6182) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6182))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6182)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6182 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6182) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6182))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6182)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6183 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6183) = g32p_row13_cosetRepresentatives 6183 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6183 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6183) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6183))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6183)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6183 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6183) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6183))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6183)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6184 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6184) = g32p_row13_cosetRepresentatives 6184 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6184 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6184) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6184))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6184)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6184 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6184) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6184))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6184)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6185 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6185) = g32p_row13_cosetRepresentatives 6185 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6185 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6185) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6185))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6185)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6185 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6185) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6185))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6185)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6186 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6186) = g32p_row13_cosetRepresentatives 6186 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6186 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6186) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6186))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6186)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6186 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6186) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6186))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6186)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6187 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6187) = g32p_row13_cosetRepresentatives 6187 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6187 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6187) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6187))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6187)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6187 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6187) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6187))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6187)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6188 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6188) = g32p_row13_cosetRepresentatives 6188 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6188 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6188) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6188))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6188)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6188 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6188) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6188))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6188)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6189 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6189) = g32p_row13_cosetRepresentatives 6189 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6189 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6189) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6189))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6189)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6189 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6189) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6189))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6189)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6190 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6190) = g32p_row13_cosetRepresentatives 6190 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6190 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6190) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6190))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6190)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6190 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6190) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6190))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6190)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6191 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6191) = g32p_row13_cosetRepresentatives 6191 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6191 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6191) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6191))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6191)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6191 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6191) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6191))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6191)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0386 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 386 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 386 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6176
  · exact g32p_row13_cosetWord_6177
  · exact g32p_row13_cosetWord_6178
  · exact g32p_row13_cosetWord_6179
  · exact g32p_row13_cosetWord_6180
  · exact g32p_row13_cosetWord_6181
  · exact g32p_row13_cosetWord_6182
  · exact g32p_row13_cosetWord_6183
  · exact g32p_row13_cosetWord_6184
  · exact g32p_row13_cosetWord_6185
  · exact g32p_row13_cosetWord_6186
  · exact g32p_row13_cosetWord_6187
  · exact g32p_row13_cosetWord_6188
  · exact g32p_row13_cosetWord_6189
  · exact g32p_row13_cosetWord_6190
  · exact g32p_row13_cosetWord_6191

theorem g32p_row13_cosetGeneratorBlock_0386 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 386 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 386 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 386 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6176 s
  · exact g32p_row13_cosetGeneratorStep_6177 s
  · exact g32p_row13_cosetGeneratorStep_6178 s
  · exact g32p_row13_cosetGeneratorStep_6179 s
  · exact g32p_row13_cosetGeneratorStep_6180 s
  · exact g32p_row13_cosetGeneratorStep_6181 s
  · exact g32p_row13_cosetGeneratorStep_6182 s
  · exact g32p_row13_cosetGeneratorStep_6183 s
  · exact g32p_row13_cosetGeneratorStep_6184 s
  · exact g32p_row13_cosetGeneratorStep_6185 s
  · exact g32p_row13_cosetGeneratorStep_6186 s
  · exact g32p_row13_cosetGeneratorStep_6187 s
  · exact g32p_row13_cosetGeneratorStep_6188 s
  · exact g32p_row13_cosetGeneratorStep_6189 s
  · exact g32p_row13_cosetGeneratorStep_6190 s
  · exact g32p_row13_cosetGeneratorStep_6191 s

theorem g32p_row13_cosetBranchBlock_0386 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 386 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 386 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 386 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6176 s
  · exact g32p_row13_cosetBranchStep_6177 s
  · exact g32p_row13_cosetBranchStep_6178 s
  · exact g32p_row13_cosetBranchStep_6179 s
  · exact g32p_row13_cosetBranchStep_6180 s
  · exact g32p_row13_cosetBranchStep_6181 s
  · exact g32p_row13_cosetBranchStep_6182 s
  · exact g32p_row13_cosetBranchStep_6183 s
  · exact g32p_row13_cosetBranchStep_6184 s
  · exact g32p_row13_cosetBranchStep_6185 s
  · exact g32p_row13_cosetBranchStep_6186 s
  · exact g32p_row13_cosetBranchStep_6187 s
  · exact g32p_row13_cosetBranchStep_6188 s
  · exact g32p_row13_cosetBranchStep_6189 s
  · exact g32p_row13_cosetBranchStep_6190 s
  · exact g32p_row13_cosetBranchStep_6191 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6192 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6192) = g32p_row13_cosetRepresentatives 6192 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6192 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6192) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6192))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6192)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6192 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6192) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6192))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6192)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6193 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6193) = g32p_row13_cosetRepresentatives 6193 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6193 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6193) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6193))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6193)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6193 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6193) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6193))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6193)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6194 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6194) = g32p_row13_cosetRepresentatives 6194 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6194 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6194) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6194))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6194)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6194 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6194) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6194))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6194)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6195 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6195) = g32p_row13_cosetRepresentatives 6195 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6195 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6195) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6195))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6195)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6195 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6195) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6195))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6195)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6196 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6196) = g32p_row13_cosetRepresentatives 6196 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6196 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6196) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6196))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6196)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6196 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6196) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6196))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6196)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6197 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6197) = g32p_row13_cosetRepresentatives 6197 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6197 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6197) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6197))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6197)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6197 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6197) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6197))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6197)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6198 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6198) = g32p_row13_cosetRepresentatives 6198 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6198 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6198) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6198))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6198)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6198 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6198) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6198))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6198)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6199 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6199) = g32p_row13_cosetRepresentatives 6199 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6199 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6199) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6199))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6199)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6199 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6199) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6199))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6199)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6200 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6200) = g32p_row13_cosetRepresentatives 6200 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6200 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6200) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6200))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6200)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6200 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6200) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6200))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6200)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6201 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6201) = g32p_row13_cosetRepresentatives 6201 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6201 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6201) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6201))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6201)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6201 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6201) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6201))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6201)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6202 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6202) = g32p_row13_cosetRepresentatives 6202 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6202 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6202) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6202))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6202)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6202 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6202) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6202))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6202)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6203 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6203) = g32p_row13_cosetRepresentatives 6203 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6203 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6203) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6203))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6203)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6203 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6203) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6203))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6203)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6204 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6204) = g32p_row13_cosetRepresentatives 6204 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6204 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6204) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6204))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6204)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6204 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6204) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6204))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6204)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6205 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6205) = g32p_row13_cosetRepresentatives 6205 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6205 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6205) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6205))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6205)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6205 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6205) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6205))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6205)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6206 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6206) = g32p_row13_cosetRepresentatives 6206 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6206 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6206) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6206))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6206)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6206 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6206) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6206))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6206)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6207 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6207) = g32p_row13_cosetRepresentatives 6207 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6207 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6207) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6207))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6207)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6207 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6207) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6207))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6207)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0387 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 387 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 387 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6192
  · exact g32p_row13_cosetWord_6193
  · exact g32p_row13_cosetWord_6194
  · exact g32p_row13_cosetWord_6195
  · exact g32p_row13_cosetWord_6196
  · exact g32p_row13_cosetWord_6197
  · exact g32p_row13_cosetWord_6198
  · exact g32p_row13_cosetWord_6199
  · exact g32p_row13_cosetWord_6200
  · exact g32p_row13_cosetWord_6201
  · exact g32p_row13_cosetWord_6202
  · exact g32p_row13_cosetWord_6203
  · exact g32p_row13_cosetWord_6204
  · exact g32p_row13_cosetWord_6205
  · exact g32p_row13_cosetWord_6206
  · exact g32p_row13_cosetWord_6207

theorem g32p_row13_cosetGeneratorBlock_0387 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 387 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 387 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 387 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6192 s
  · exact g32p_row13_cosetGeneratorStep_6193 s
  · exact g32p_row13_cosetGeneratorStep_6194 s
  · exact g32p_row13_cosetGeneratorStep_6195 s
  · exact g32p_row13_cosetGeneratorStep_6196 s
  · exact g32p_row13_cosetGeneratorStep_6197 s
  · exact g32p_row13_cosetGeneratorStep_6198 s
  · exact g32p_row13_cosetGeneratorStep_6199 s
  · exact g32p_row13_cosetGeneratorStep_6200 s
  · exact g32p_row13_cosetGeneratorStep_6201 s
  · exact g32p_row13_cosetGeneratorStep_6202 s
  · exact g32p_row13_cosetGeneratorStep_6203 s
  · exact g32p_row13_cosetGeneratorStep_6204 s
  · exact g32p_row13_cosetGeneratorStep_6205 s
  · exact g32p_row13_cosetGeneratorStep_6206 s
  · exact g32p_row13_cosetGeneratorStep_6207 s

theorem g32p_row13_cosetBranchBlock_0387 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 387 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 387 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 387 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6192 s
  · exact g32p_row13_cosetBranchStep_6193 s
  · exact g32p_row13_cosetBranchStep_6194 s
  · exact g32p_row13_cosetBranchStep_6195 s
  · exact g32p_row13_cosetBranchStep_6196 s
  · exact g32p_row13_cosetBranchStep_6197 s
  · exact g32p_row13_cosetBranchStep_6198 s
  · exact g32p_row13_cosetBranchStep_6199 s
  · exact g32p_row13_cosetBranchStep_6200 s
  · exact g32p_row13_cosetBranchStep_6201 s
  · exact g32p_row13_cosetBranchStep_6202 s
  · exact g32p_row13_cosetBranchStep_6203 s
  · exact g32p_row13_cosetBranchStep_6204 s
  · exact g32p_row13_cosetBranchStep_6205 s
  · exact g32p_row13_cosetBranchStep_6206 s
  · exact g32p_row13_cosetBranchStep_6207 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6208 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6208) = g32p_row13_cosetRepresentatives 6208 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6208 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6208) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6208))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6208)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6208 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6208) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6208))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6208)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6209 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6209) = g32p_row13_cosetRepresentatives 6209 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6209 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6209) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6209))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6209)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6209 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6209) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6209))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6209)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6210 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6210) = g32p_row13_cosetRepresentatives 6210 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6210 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6210) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6210))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6210)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6210 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6210) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6210))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6210)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6211 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6211) = g32p_row13_cosetRepresentatives 6211 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6211 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6211) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6211))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6211)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6211 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6211) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6211))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6211)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6212 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6212) = g32p_row13_cosetRepresentatives 6212 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6212 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6212) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6212))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6212)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6212 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6212) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6212))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6212)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6213 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6213) = g32p_row13_cosetRepresentatives 6213 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6213 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6213) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6213))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6213)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6213 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6213) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6213))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6213)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6214 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6214) = g32p_row13_cosetRepresentatives 6214 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6214 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6214) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6214))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6214)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6214 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6214) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6214))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6214)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6215 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6215) = g32p_row13_cosetRepresentatives 6215 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6215 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6215) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6215))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6215)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6215 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6215) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6215))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6215)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6216 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6216) = g32p_row13_cosetRepresentatives 6216 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6216 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6216) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6216))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6216)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6216 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6216) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6216))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6216)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6217 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6217) = g32p_row13_cosetRepresentatives 6217 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6217 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6217) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6217))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6217)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6217 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6217) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6217))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6217)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6218 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6218) = g32p_row13_cosetRepresentatives 6218 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6218 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6218) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6218))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6218)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6218 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6218) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6218))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6218)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6219 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6219) = g32p_row13_cosetRepresentatives 6219 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6219 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6219) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6219))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6219)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6219 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6219) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6219))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6219)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6220 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6220) = g32p_row13_cosetRepresentatives 6220 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6220 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6220) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6220))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6220)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6220 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6220) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6220))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6220)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6221 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6221) = g32p_row13_cosetRepresentatives 6221 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6221 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6221) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6221))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6221)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6221 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6221) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6221))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6221)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6222 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6222) = g32p_row13_cosetRepresentatives 6222 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6222 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6222) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6222))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6222)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6222 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6222) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6222))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6222)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6223 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6223) = g32p_row13_cosetRepresentatives 6223 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6223 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6223) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6223))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6223)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6223 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6223) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6223))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6223)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0388 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 388 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 388 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6208
  · exact g32p_row13_cosetWord_6209
  · exact g32p_row13_cosetWord_6210
  · exact g32p_row13_cosetWord_6211
  · exact g32p_row13_cosetWord_6212
  · exact g32p_row13_cosetWord_6213
  · exact g32p_row13_cosetWord_6214
  · exact g32p_row13_cosetWord_6215
  · exact g32p_row13_cosetWord_6216
  · exact g32p_row13_cosetWord_6217
  · exact g32p_row13_cosetWord_6218
  · exact g32p_row13_cosetWord_6219
  · exact g32p_row13_cosetWord_6220
  · exact g32p_row13_cosetWord_6221
  · exact g32p_row13_cosetWord_6222
  · exact g32p_row13_cosetWord_6223

theorem g32p_row13_cosetGeneratorBlock_0388 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 388 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 388 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 388 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6208 s
  · exact g32p_row13_cosetGeneratorStep_6209 s
  · exact g32p_row13_cosetGeneratorStep_6210 s
  · exact g32p_row13_cosetGeneratorStep_6211 s
  · exact g32p_row13_cosetGeneratorStep_6212 s
  · exact g32p_row13_cosetGeneratorStep_6213 s
  · exact g32p_row13_cosetGeneratorStep_6214 s
  · exact g32p_row13_cosetGeneratorStep_6215 s
  · exact g32p_row13_cosetGeneratorStep_6216 s
  · exact g32p_row13_cosetGeneratorStep_6217 s
  · exact g32p_row13_cosetGeneratorStep_6218 s
  · exact g32p_row13_cosetGeneratorStep_6219 s
  · exact g32p_row13_cosetGeneratorStep_6220 s
  · exact g32p_row13_cosetGeneratorStep_6221 s
  · exact g32p_row13_cosetGeneratorStep_6222 s
  · exact g32p_row13_cosetGeneratorStep_6223 s

theorem g32p_row13_cosetBranchBlock_0388 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 388 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 388 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 388 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6208 s
  · exact g32p_row13_cosetBranchStep_6209 s
  · exact g32p_row13_cosetBranchStep_6210 s
  · exact g32p_row13_cosetBranchStep_6211 s
  · exact g32p_row13_cosetBranchStep_6212 s
  · exact g32p_row13_cosetBranchStep_6213 s
  · exact g32p_row13_cosetBranchStep_6214 s
  · exact g32p_row13_cosetBranchStep_6215 s
  · exact g32p_row13_cosetBranchStep_6216 s
  · exact g32p_row13_cosetBranchStep_6217 s
  · exact g32p_row13_cosetBranchStep_6218 s
  · exact g32p_row13_cosetBranchStep_6219 s
  · exact g32p_row13_cosetBranchStep_6220 s
  · exact g32p_row13_cosetBranchStep_6221 s
  · exact g32p_row13_cosetBranchStep_6222 s
  · exact g32p_row13_cosetBranchStep_6223 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6224 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6224) = g32p_row13_cosetRepresentatives 6224 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6224 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6224) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6224))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6224)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6224 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6224) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6224))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6224)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6225 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6225) = g32p_row13_cosetRepresentatives 6225 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6225 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6225) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6225))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6225)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6225 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6225) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6225))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6225)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6226 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6226) = g32p_row13_cosetRepresentatives 6226 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6226 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6226) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6226))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6226)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6226 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6226) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6226))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6226)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6227 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6227) = g32p_row13_cosetRepresentatives 6227 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6227 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6227) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6227))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6227)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6227 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6227) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6227))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6227)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6228 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6228) = g32p_row13_cosetRepresentatives 6228 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6228 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6228) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6228))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6228)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6228 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6228) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6228))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6228)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6229 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6229) = g32p_row13_cosetRepresentatives 6229 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6229 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6229) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6229))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6229)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6229 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6229) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6229))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6229)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6230 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6230) = g32p_row13_cosetRepresentatives 6230 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6230 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6230) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6230))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6230)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6230 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6230) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6230))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6230)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6231 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6231) = g32p_row13_cosetRepresentatives 6231 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6231 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6231) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6231))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6231)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6231 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6231) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6231))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6231)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6232 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6232) = g32p_row13_cosetRepresentatives 6232 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6232 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6232) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6232))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6232)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6232 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6232) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6232))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6232)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6233 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6233) = g32p_row13_cosetRepresentatives 6233 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6233 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6233) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6233))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6233)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6233 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6233) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6233))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6233)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6234 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6234) = g32p_row13_cosetRepresentatives 6234 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6234 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6234) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6234))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6234)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6234 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6234) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6234))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6234)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6235 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6235) = g32p_row13_cosetRepresentatives 6235 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6235 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6235) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6235))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6235)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6235 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6235) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6235))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6235)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6236 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6236) = g32p_row13_cosetRepresentatives 6236 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6236 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6236) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6236))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6236)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6236 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6236) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6236))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6236)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6237 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6237) = g32p_row13_cosetRepresentatives 6237 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6237 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6237) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6237))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6237)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6237 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6237) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6237))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6237)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6238 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6238) = g32p_row13_cosetRepresentatives 6238 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6238 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6238) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6238))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6238)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6238 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6238) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6238))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6238)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6239 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6239) = g32p_row13_cosetRepresentatives 6239 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6239 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6239) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6239))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6239)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6239 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6239) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6239))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6239)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0389 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 389 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 389 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6224
  · exact g32p_row13_cosetWord_6225
  · exact g32p_row13_cosetWord_6226
  · exact g32p_row13_cosetWord_6227
  · exact g32p_row13_cosetWord_6228
  · exact g32p_row13_cosetWord_6229
  · exact g32p_row13_cosetWord_6230
  · exact g32p_row13_cosetWord_6231
  · exact g32p_row13_cosetWord_6232
  · exact g32p_row13_cosetWord_6233
  · exact g32p_row13_cosetWord_6234
  · exact g32p_row13_cosetWord_6235
  · exact g32p_row13_cosetWord_6236
  · exact g32p_row13_cosetWord_6237
  · exact g32p_row13_cosetWord_6238
  · exact g32p_row13_cosetWord_6239

theorem g32p_row13_cosetGeneratorBlock_0389 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 389 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 389 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 389 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6224 s
  · exact g32p_row13_cosetGeneratorStep_6225 s
  · exact g32p_row13_cosetGeneratorStep_6226 s
  · exact g32p_row13_cosetGeneratorStep_6227 s
  · exact g32p_row13_cosetGeneratorStep_6228 s
  · exact g32p_row13_cosetGeneratorStep_6229 s
  · exact g32p_row13_cosetGeneratorStep_6230 s
  · exact g32p_row13_cosetGeneratorStep_6231 s
  · exact g32p_row13_cosetGeneratorStep_6232 s
  · exact g32p_row13_cosetGeneratorStep_6233 s
  · exact g32p_row13_cosetGeneratorStep_6234 s
  · exact g32p_row13_cosetGeneratorStep_6235 s
  · exact g32p_row13_cosetGeneratorStep_6236 s
  · exact g32p_row13_cosetGeneratorStep_6237 s
  · exact g32p_row13_cosetGeneratorStep_6238 s
  · exact g32p_row13_cosetGeneratorStep_6239 s

theorem g32p_row13_cosetBranchBlock_0389 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 389 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 389 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 389 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6224 s
  · exact g32p_row13_cosetBranchStep_6225 s
  · exact g32p_row13_cosetBranchStep_6226 s
  · exact g32p_row13_cosetBranchStep_6227 s
  · exact g32p_row13_cosetBranchStep_6228 s
  · exact g32p_row13_cosetBranchStep_6229 s
  · exact g32p_row13_cosetBranchStep_6230 s
  · exact g32p_row13_cosetBranchStep_6231 s
  · exact g32p_row13_cosetBranchStep_6232 s
  · exact g32p_row13_cosetBranchStep_6233 s
  · exact g32p_row13_cosetBranchStep_6234 s
  · exact g32p_row13_cosetBranchStep_6235 s
  · exact g32p_row13_cosetBranchStep_6236 s
  · exact g32p_row13_cosetBranchStep_6237 s
  · exact g32p_row13_cosetBranchStep_6238 s
  · exact g32p_row13_cosetBranchStep_6239 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6240 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6240) = g32p_row13_cosetRepresentatives 6240 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6240 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6240) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6240))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6240)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6240 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6240) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6240))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6240)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6241 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6241) = g32p_row13_cosetRepresentatives 6241 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6241 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6241) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6241))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6241)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6241 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6241) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6241))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6241)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6242 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6242) = g32p_row13_cosetRepresentatives 6242 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6242 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6242) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6242))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6242)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6242 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6242) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6242))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6242)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6243 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6243) = g32p_row13_cosetRepresentatives 6243 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6243 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6243) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6243))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6243)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6243 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6243) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6243))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6243)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6244 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6244) = g32p_row13_cosetRepresentatives 6244 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6244 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6244) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6244))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6244)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6244 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6244) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6244))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6244)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6245 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6245) = g32p_row13_cosetRepresentatives 6245 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6245 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6245) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6245))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6245)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6245 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6245) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6245))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6245)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6246 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6246) = g32p_row13_cosetRepresentatives 6246 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6246 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6246) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6246))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6246)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6246 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6246) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6246))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6246)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6247 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6247) = g32p_row13_cosetRepresentatives 6247 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6247 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6247) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6247))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6247)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6247 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6247) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6247))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6247)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6248 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6248) = g32p_row13_cosetRepresentatives 6248 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6248 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6248) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6248))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6248)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6248 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6248) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6248))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6248)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6249 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6249) = g32p_row13_cosetRepresentatives 6249 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6249 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6249) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6249))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6249)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6249 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6249) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6249))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6249)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6250 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6250) = g32p_row13_cosetRepresentatives 6250 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6250 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6250) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6250))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6250)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6250 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6250) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6250))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6250)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6251 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6251) = g32p_row13_cosetRepresentatives 6251 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6251 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6251) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6251))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6251)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6251 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6251) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6251))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6251)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6252 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6252) = g32p_row13_cosetRepresentatives 6252 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6252 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6252) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6252))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6252)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6252 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6252) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6252))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6252)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6253 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6253) = g32p_row13_cosetRepresentatives 6253 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6253 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6253) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6253))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6253)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6253 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6253) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6253))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6253)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6254 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6254) = g32p_row13_cosetRepresentatives 6254 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6254 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6254) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6254))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6254)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6254 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6254) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6254))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6254)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6255 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6255) = g32p_row13_cosetRepresentatives 6255 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6255 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6255) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6255))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6255)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6255 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6255) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6255))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6255)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0390 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 390 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 390 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6240
  · exact g32p_row13_cosetWord_6241
  · exact g32p_row13_cosetWord_6242
  · exact g32p_row13_cosetWord_6243
  · exact g32p_row13_cosetWord_6244
  · exact g32p_row13_cosetWord_6245
  · exact g32p_row13_cosetWord_6246
  · exact g32p_row13_cosetWord_6247
  · exact g32p_row13_cosetWord_6248
  · exact g32p_row13_cosetWord_6249
  · exact g32p_row13_cosetWord_6250
  · exact g32p_row13_cosetWord_6251
  · exact g32p_row13_cosetWord_6252
  · exact g32p_row13_cosetWord_6253
  · exact g32p_row13_cosetWord_6254
  · exact g32p_row13_cosetWord_6255

theorem g32p_row13_cosetGeneratorBlock_0390 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 390 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 390 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 390 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6240 s
  · exact g32p_row13_cosetGeneratorStep_6241 s
  · exact g32p_row13_cosetGeneratorStep_6242 s
  · exact g32p_row13_cosetGeneratorStep_6243 s
  · exact g32p_row13_cosetGeneratorStep_6244 s
  · exact g32p_row13_cosetGeneratorStep_6245 s
  · exact g32p_row13_cosetGeneratorStep_6246 s
  · exact g32p_row13_cosetGeneratorStep_6247 s
  · exact g32p_row13_cosetGeneratorStep_6248 s
  · exact g32p_row13_cosetGeneratorStep_6249 s
  · exact g32p_row13_cosetGeneratorStep_6250 s
  · exact g32p_row13_cosetGeneratorStep_6251 s
  · exact g32p_row13_cosetGeneratorStep_6252 s
  · exact g32p_row13_cosetGeneratorStep_6253 s
  · exact g32p_row13_cosetGeneratorStep_6254 s
  · exact g32p_row13_cosetGeneratorStep_6255 s

theorem g32p_row13_cosetBranchBlock_0390 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 390 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 390 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 390 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6240 s
  · exact g32p_row13_cosetBranchStep_6241 s
  · exact g32p_row13_cosetBranchStep_6242 s
  · exact g32p_row13_cosetBranchStep_6243 s
  · exact g32p_row13_cosetBranchStep_6244 s
  · exact g32p_row13_cosetBranchStep_6245 s
  · exact g32p_row13_cosetBranchStep_6246 s
  · exact g32p_row13_cosetBranchStep_6247 s
  · exact g32p_row13_cosetBranchStep_6248 s
  · exact g32p_row13_cosetBranchStep_6249 s
  · exact g32p_row13_cosetBranchStep_6250 s
  · exact g32p_row13_cosetBranchStep_6251 s
  · exact g32p_row13_cosetBranchStep_6252 s
  · exact g32p_row13_cosetBranchStep_6253 s
  · exact g32p_row13_cosetBranchStep_6254 s
  · exact g32p_row13_cosetBranchStep_6255 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6256 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6256) = g32p_row13_cosetRepresentatives 6256 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6256 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6256) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6256))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6256)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6256 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6256) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6256))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6256)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6257 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6257) = g32p_row13_cosetRepresentatives 6257 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6257 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6257) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6257))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6257)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6257 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6257) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6257))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6257)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6258 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6258) = g32p_row13_cosetRepresentatives 6258 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6258 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6258) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6258))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6258)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6258 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6258) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6258))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6258)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6259 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6259) = g32p_row13_cosetRepresentatives 6259 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6259 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6259) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6259))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6259)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6259 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6259) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6259))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6259)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6260 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6260) = g32p_row13_cosetRepresentatives 6260 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6260 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6260) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6260))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6260)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6260 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6260) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6260))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6260)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6261 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6261) = g32p_row13_cosetRepresentatives 6261 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6261 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6261) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6261))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6261)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6261 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6261) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6261))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6261)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6262 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6262) = g32p_row13_cosetRepresentatives 6262 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6262 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6262) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6262))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6262)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6262 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6262) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6262))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6262)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6263 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6263) = g32p_row13_cosetRepresentatives 6263 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6263 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6263) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6263))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6263)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6263 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6263) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6263))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6263)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6264 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6264) = g32p_row13_cosetRepresentatives 6264 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6264 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6264) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6264))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6264)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6264 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6264) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6264))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6264)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6265 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6265) = g32p_row13_cosetRepresentatives 6265 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6265 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6265) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6265))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6265)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6265 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6265) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6265))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6265)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6266 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6266) = g32p_row13_cosetRepresentatives 6266 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6266 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6266) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6266))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6266)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6266 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6266) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6266))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6266)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6267 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6267) = g32p_row13_cosetRepresentatives 6267 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6267 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6267) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6267))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6267)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6267 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6267) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6267))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6267)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6268 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6268) = g32p_row13_cosetRepresentatives 6268 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6268 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6268) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6268))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6268)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6268 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6268) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6268))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6268)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6269 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6269) = g32p_row13_cosetRepresentatives 6269 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6269 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6269) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6269))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6269)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6269 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6269) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6269))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6269)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6270 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6270) = g32p_row13_cosetRepresentatives 6270 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6270 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6270) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6270))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6270)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6270 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6270) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6270))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6270)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6271 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6271) = g32p_row13_cosetRepresentatives 6271 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6271 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6271) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6271))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6271)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6271 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6271) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6271))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6271)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0391 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 391 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 391 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6256
  · exact g32p_row13_cosetWord_6257
  · exact g32p_row13_cosetWord_6258
  · exact g32p_row13_cosetWord_6259
  · exact g32p_row13_cosetWord_6260
  · exact g32p_row13_cosetWord_6261
  · exact g32p_row13_cosetWord_6262
  · exact g32p_row13_cosetWord_6263
  · exact g32p_row13_cosetWord_6264
  · exact g32p_row13_cosetWord_6265
  · exact g32p_row13_cosetWord_6266
  · exact g32p_row13_cosetWord_6267
  · exact g32p_row13_cosetWord_6268
  · exact g32p_row13_cosetWord_6269
  · exact g32p_row13_cosetWord_6270
  · exact g32p_row13_cosetWord_6271

theorem g32p_row13_cosetGeneratorBlock_0391 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 391 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 391 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 391 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6256 s
  · exact g32p_row13_cosetGeneratorStep_6257 s
  · exact g32p_row13_cosetGeneratorStep_6258 s
  · exact g32p_row13_cosetGeneratorStep_6259 s
  · exact g32p_row13_cosetGeneratorStep_6260 s
  · exact g32p_row13_cosetGeneratorStep_6261 s
  · exact g32p_row13_cosetGeneratorStep_6262 s
  · exact g32p_row13_cosetGeneratorStep_6263 s
  · exact g32p_row13_cosetGeneratorStep_6264 s
  · exact g32p_row13_cosetGeneratorStep_6265 s
  · exact g32p_row13_cosetGeneratorStep_6266 s
  · exact g32p_row13_cosetGeneratorStep_6267 s
  · exact g32p_row13_cosetGeneratorStep_6268 s
  · exact g32p_row13_cosetGeneratorStep_6269 s
  · exact g32p_row13_cosetGeneratorStep_6270 s
  · exact g32p_row13_cosetGeneratorStep_6271 s

theorem g32p_row13_cosetBranchBlock_0391 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 391 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 391 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 391 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6256 s
  · exact g32p_row13_cosetBranchStep_6257 s
  · exact g32p_row13_cosetBranchStep_6258 s
  · exact g32p_row13_cosetBranchStep_6259 s
  · exact g32p_row13_cosetBranchStep_6260 s
  · exact g32p_row13_cosetBranchStep_6261 s
  · exact g32p_row13_cosetBranchStep_6262 s
  · exact g32p_row13_cosetBranchStep_6263 s
  · exact g32p_row13_cosetBranchStep_6264 s
  · exact g32p_row13_cosetBranchStep_6265 s
  · exact g32p_row13_cosetBranchStep_6266 s
  · exact g32p_row13_cosetBranchStep_6267 s
  · exact g32p_row13_cosetBranchStep_6268 s
  · exact g32p_row13_cosetBranchStep_6269 s
  · exact g32p_row13_cosetBranchStep_6270 s
  · exact g32p_row13_cosetBranchStep_6271 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6272 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6272) = g32p_row13_cosetRepresentatives 6272 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6272 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6272) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6272))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6272)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6272 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6272) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6272))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6272)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6273 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6273) = g32p_row13_cosetRepresentatives 6273 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6273 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6273) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6273))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6273)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6273 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6273) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6273))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6273)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6274 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6274) = g32p_row13_cosetRepresentatives 6274 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6274 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6274) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6274))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6274)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6274 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6274) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6274))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6274)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6275 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6275) = g32p_row13_cosetRepresentatives 6275 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6275 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6275) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6275))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6275)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6275 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6275) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6275))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6275)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6276 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6276) = g32p_row13_cosetRepresentatives 6276 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6276 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6276) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6276))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6276)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6276 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6276) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6276))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6276)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6277 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6277) = g32p_row13_cosetRepresentatives 6277 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6277 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6277) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6277))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6277)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6277 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6277) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6277))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6277)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6278 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6278) = g32p_row13_cosetRepresentatives 6278 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6278 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6278) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6278))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6278)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6278 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6278) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6278))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6278)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6279 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6279) = g32p_row13_cosetRepresentatives 6279 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6279 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6279) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6279))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6279)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6279 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6279) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6279))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6279)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6280 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6280) = g32p_row13_cosetRepresentatives 6280 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6280 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6280) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6280))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6280)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6280 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6280) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6280))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6280)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6281 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6281) = g32p_row13_cosetRepresentatives 6281 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6281 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6281) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6281))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6281)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6281 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6281) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6281))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6281)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6282 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6282) = g32p_row13_cosetRepresentatives 6282 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6282 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6282) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6282))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6282)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6282 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6282) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6282))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6282)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6283 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6283) = g32p_row13_cosetRepresentatives 6283 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6283 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6283) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6283))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6283)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6283 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6283) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6283))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6283)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6284 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6284) = g32p_row13_cosetRepresentatives 6284 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6284 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6284) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6284))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6284)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6284 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6284) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6284))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6284)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6285 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6285) = g32p_row13_cosetRepresentatives 6285 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6285 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6285) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6285))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6285)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6285 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6285) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6285))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6285)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6286 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6286) = g32p_row13_cosetRepresentatives 6286 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6286 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6286) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6286))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6286)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6286 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6286) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6286))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6286)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6287 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6287) = g32p_row13_cosetRepresentatives 6287 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6287 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6287) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6287))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6287)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6287 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6287) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6287))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6287)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0392 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 392 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 392 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6272
  · exact g32p_row13_cosetWord_6273
  · exact g32p_row13_cosetWord_6274
  · exact g32p_row13_cosetWord_6275
  · exact g32p_row13_cosetWord_6276
  · exact g32p_row13_cosetWord_6277
  · exact g32p_row13_cosetWord_6278
  · exact g32p_row13_cosetWord_6279
  · exact g32p_row13_cosetWord_6280
  · exact g32p_row13_cosetWord_6281
  · exact g32p_row13_cosetWord_6282
  · exact g32p_row13_cosetWord_6283
  · exact g32p_row13_cosetWord_6284
  · exact g32p_row13_cosetWord_6285
  · exact g32p_row13_cosetWord_6286
  · exact g32p_row13_cosetWord_6287

theorem g32p_row13_cosetGeneratorBlock_0392 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 392 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 392 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 392 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6272 s
  · exact g32p_row13_cosetGeneratorStep_6273 s
  · exact g32p_row13_cosetGeneratorStep_6274 s
  · exact g32p_row13_cosetGeneratorStep_6275 s
  · exact g32p_row13_cosetGeneratorStep_6276 s
  · exact g32p_row13_cosetGeneratorStep_6277 s
  · exact g32p_row13_cosetGeneratorStep_6278 s
  · exact g32p_row13_cosetGeneratorStep_6279 s
  · exact g32p_row13_cosetGeneratorStep_6280 s
  · exact g32p_row13_cosetGeneratorStep_6281 s
  · exact g32p_row13_cosetGeneratorStep_6282 s
  · exact g32p_row13_cosetGeneratorStep_6283 s
  · exact g32p_row13_cosetGeneratorStep_6284 s
  · exact g32p_row13_cosetGeneratorStep_6285 s
  · exact g32p_row13_cosetGeneratorStep_6286 s
  · exact g32p_row13_cosetGeneratorStep_6287 s

theorem g32p_row13_cosetBranchBlock_0392 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 392 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 392 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 392 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6272 s
  · exact g32p_row13_cosetBranchStep_6273 s
  · exact g32p_row13_cosetBranchStep_6274 s
  · exact g32p_row13_cosetBranchStep_6275 s
  · exact g32p_row13_cosetBranchStep_6276 s
  · exact g32p_row13_cosetBranchStep_6277 s
  · exact g32p_row13_cosetBranchStep_6278 s
  · exact g32p_row13_cosetBranchStep_6279 s
  · exact g32p_row13_cosetBranchStep_6280 s
  · exact g32p_row13_cosetBranchStep_6281 s
  · exact g32p_row13_cosetBranchStep_6282 s
  · exact g32p_row13_cosetBranchStep_6283 s
  · exact g32p_row13_cosetBranchStep_6284 s
  · exact g32p_row13_cosetBranchStep_6285 s
  · exact g32p_row13_cosetBranchStep_6286 s
  · exact g32p_row13_cosetBranchStep_6287 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6288 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6288) = g32p_row13_cosetRepresentatives 6288 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6288 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6288) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6288))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6288)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6288 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6288) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6288))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6288)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6289 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6289) = g32p_row13_cosetRepresentatives 6289 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6289 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6289) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6289))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6289)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6289 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6289) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6289))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6289)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6290 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6290) = g32p_row13_cosetRepresentatives 6290 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6290 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6290) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6290))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6290)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6290 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6290) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6290))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6290)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6291 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6291) = g32p_row13_cosetRepresentatives 6291 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6291 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6291) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6291))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6291)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6291 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6291) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6291))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6291)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6292 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6292) = g32p_row13_cosetRepresentatives 6292 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6292 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6292) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6292))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6292)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6292 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6292) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6292))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6292)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6293 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6293) = g32p_row13_cosetRepresentatives 6293 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6293 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6293) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6293))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6293)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6293 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6293) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6293))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6293)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6294 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6294) = g32p_row13_cosetRepresentatives 6294 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6294 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6294) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6294))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6294)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6294 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6294) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6294))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6294)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6295 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6295) = g32p_row13_cosetRepresentatives 6295 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6295 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6295) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6295))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6295)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6295 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6295) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6295))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6295)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6296 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6296) = g32p_row13_cosetRepresentatives 6296 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6296 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6296) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6296))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6296)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6296 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6296) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6296))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6296)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6297 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6297) = g32p_row13_cosetRepresentatives 6297 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6297 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6297) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6297))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6297)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6297 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6297) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6297))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6297)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6298 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6298) = g32p_row13_cosetRepresentatives 6298 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6298 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6298) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6298))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6298)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6298 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6298) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6298))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6298)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6299 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6299) = g32p_row13_cosetRepresentatives 6299 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6299 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6299) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6299))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6299)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6299 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6299) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6299))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6299)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6300 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6300) = g32p_row13_cosetRepresentatives 6300 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6300 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6300) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6300))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6300)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6300 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6300) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6300))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6300)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6301 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6301) = g32p_row13_cosetRepresentatives 6301 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6301 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6301) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6301))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6301)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6301 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6301) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6301))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6301)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6302 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6302) = g32p_row13_cosetRepresentatives 6302 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6302 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6302) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6302))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6302)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6302 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6302) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6302))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6302)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6303 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6303) = g32p_row13_cosetRepresentatives 6303 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6303 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6303) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6303))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6303)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6303 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6303) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6303))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6303)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0393 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 393 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 393 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6288
  · exact g32p_row13_cosetWord_6289
  · exact g32p_row13_cosetWord_6290
  · exact g32p_row13_cosetWord_6291
  · exact g32p_row13_cosetWord_6292
  · exact g32p_row13_cosetWord_6293
  · exact g32p_row13_cosetWord_6294
  · exact g32p_row13_cosetWord_6295
  · exact g32p_row13_cosetWord_6296
  · exact g32p_row13_cosetWord_6297
  · exact g32p_row13_cosetWord_6298
  · exact g32p_row13_cosetWord_6299
  · exact g32p_row13_cosetWord_6300
  · exact g32p_row13_cosetWord_6301
  · exact g32p_row13_cosetWord_6302
  · exact g32p_row13_cosetWord_6303

theorem g32p_row13_cosetGeneratorBlock_0393 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 393 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 393 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 393 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6288 s
  · exact g32p_row13_cosetGeneratorStep_6289 s
  · exact g32p_row13_cosetGeneratorStep_6290 s
  · exact g32p_row13_cosetGeneratorStep_6291 s
  · exact g32p_row13_cosetGeneratorStep_6292 s
  · exact g32p_row13_cosetGeneratorStep_6293 s
  · exact g32p_row13_cosetGeneratorStep_6294 s
  · exact g32p_row13_cosetGeneratorStep_6295 s
  · exact g32p_row13_cosetGeneratorStep_6296 s
  · exact g32p_row13_cosetGeneratorStep_6297 s
  · exact g32p_row13_cosetGeneratorStep_6298 s
  · exact g32p_row13_cosetGeneratorStep_6299 s
  · exact g32p_row13_cosetGeneratorStep_6300 s
  · exact g32p_row13_cosetGeneratorStep_6301 s
  · exact g32p_row13_cosetGeneratorStep_6302 s
  · exact g32p_row13_cosetGeneratorStep_6303 s

theorem g32p_row13_cosetBranchBlock_0393 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 393 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 393 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 393 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6288 s
  · exact g32p_row13_cosetBranchStep_6289 s
  · exact g32p_row13_cosetBranchStep_6290 s
  · exact g32p_row13_cosetBranchStep_6291 s
  · exact g32p_row13_cosetBranchStep_6292 s
  · exact g32p_row13_cosetBranchStep_6293 s
  · exact g32p_row13_cosetBranchStep_6294 s
  · exact g32p_row13_cosetBranchStep_6295 s
  · exact g32p_row13_cosetBranchStep_6296 s
  · exact g32p_row13_cosetBranchStep_6297 s
  · exact g32p_row13_cosetBranchStep_6298 s
  · exact g32p_row13_cosetBranchStep_6299 s
  · exact g32p_row13_cosetBranchStep_6300 s
  · exact g32p_row13_cosetBranchStep_6301 s
  · exact g32p_row13_cosetBranchStep_6302 s
  · exact g32p_row13_cosetBranchStep_6303 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6304 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6304) = g32p_row13_cosetRepresentatives 6304 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6304 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6304) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6304))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6304)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6304 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6304) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6304))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6304)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6305 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6305) = g32p_row13_cosetRepresentatives 6305 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6305 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6305) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6305))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6305)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6305 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6305) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6305))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6305)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6306 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6306) = g32p_row13_cosetRepresentatives 6306 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6306 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6306) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6306))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6306)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6306 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6306) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6306))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6306)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6307 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6307) = g32p_row13_cosetRepresentatives 6307 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6307 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6307) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6307))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6307)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6307 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6307) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6307))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6307)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6308 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6308) = g32p_row13_cosetRepresentatives 6308 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6308 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6308) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6308))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6308)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6308 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6308) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6308))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6308)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6309 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6309) = g32p_row13_cosetRepresentatives 6309 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6309 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6309) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6309))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6309)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6309 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6309) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6309))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6309)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6310 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6310) = g32p_row13_cosetRepresentatives 6310 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6310 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6310) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6310))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6310)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6310 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6310) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6310))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6310)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6311 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6311) = g32p_row13_cosetRepresentatives 6311 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6311 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6311) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6311))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6311)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6311 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6311) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6311))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6311)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6312 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6312) = g32p_row13_cosetRepresentatives 6312 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6312 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6312) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6312))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6312)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6312 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6312) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6312))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6312)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6313 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6313) = g32p_row13_cosetRepresentatives 6313 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6313 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6313) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6313))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6313)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6313 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6313) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6313))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6313)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6314 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6314) = g32p_row13_cosetRepresentatives 6314 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6314 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6314) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6314))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6314)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6314 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6314) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6314))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6314)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6315 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6315) = g32p_row13_cosetRepresentatives 6315 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6315 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6315) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6315))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6315)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6315 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6315) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6315))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6315)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6316 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6316) = g32p_row13_cosetRepresentatives 6316 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6316 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6316) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6316))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6316)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6316 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6316) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6316))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6316)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6317 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6317) = g32p_row13_cosetRepresentatives 6317 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6317 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6317) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6317))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6317)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6317 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6317) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6317))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6317)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6318 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6318) = g32p_row13_cosetRepresentatives 6318 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6318 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6318) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6318))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6318)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6318 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6318) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6318))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6318)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6319 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6319) = g32p_row13_cosetRepresentatives 6319 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6319 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6319) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6319))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6319)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6319 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6319) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6319))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6319)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0394 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 394 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 394 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6304
  · exact g32p_row13_cosetWord_6305
  · exact g32p_row13_cosetWord_6306
  · exact g32p_row13_cosetWord_6307
  · exact g32p_row13_cosetWord_6308
  · exact g32p_row13_cosetWord_6309
  · exact g32p_row13_cosetWord_6310
  · exact g32p_row13_cosetWord_6311
  · exact g32p_row13_cosetWord_6312
  · exact g32p_row13_cosetWord_6313
  · exact g32p_row13_cosetWord_6314
  · exact g32p_row13_cosetWord_6315
  · exact g32p_row13_cosetWord_6316
  · exact g32p_row13_cosetWord_6317
  · exact g32p_row13_cosetWord_6318
  · exact g32p_row13_cosetWord_6319

theorem g32p_row13_cosetGeneratorBlock_0394 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 394 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 394 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 394 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6304 s
  · exact g32p_row13_cosetGeneratorStep_6305 s
  · exact g32p_row13_cosetGeneratorStep_6306 s
  · exact g32p_row13_cosetGeneratorStep_6307 s
  · exact g32p_row13_cosetGeneratorStep_6308 s
  · exact g32p_row13_cosetGeneratorStep_6309 s
  · exact g32p_row13_cosetGeneratorStep_6310 s
  · exact g32p_row13_cosetGeneratorStep_6311 s
  · exact g32p_row13_cosetGeneratorStep_6312 s
  · exact g32p_row13_cosetGeneratorStep_6313 s
  · exact g32p_row13_cosetGeneratorStep_6314 s
  · exact g32p_row13_cosetGeneratorStep_6315 s
  · exact g32p_row13_cosetGeneratorStep_6316 s
  · exact g32p_row13_cosetGeneratorStep_6317 s
  · exact g32p_row13_cosetGeneratorStep_6318 s
  · exact g32p_row13_cosetGeneratorStep_6319 s

theorem g32p_row13_cosetBranchBlock_0394 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 394 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 394 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 394 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6304 s
  · exact g32p_row13_cosetBranchStep_6305 s
  · exact g32p_row13_cosetBranchStep_6306 s
  · exact g32p_row13_cosetBranchStep_6307 s
  · exact g32p_row13_cosetBranchStep_6308 s
  · exact g32p_row13_cosetBranchStep_6309 s
  · exact g32p_row13_cosetBranchStep_6310 s
  · exact g32p_row13_cosetBranchStep_6311 s
  · exact g32p_row13_cosetBranchStep_6312 s
  · exact g32p_row13_cosetBranchStep_6313 s
  · exact g32p_row13_cosetBranchStep_6314 s
  · exact g32p_row13_cosetBranchStep_6315 s
  · exact g32p_row13_cosetBranchStep_6316 s
  · exact g32p_row13_cosetBranchStep_6317 s
  · exact g32p_row13_cosetBranchStep_6318 s
  · exact g32p_row13_cosetBranchStep_6319 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6320 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6320) = g32p_row13_cosetRepresentatives 6320 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6320 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6320) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6320))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6320)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6320 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6320) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6320))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6320)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6321 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6321) = g32p_row13_cosetRepresentatives 6321 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6321 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6321) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6321))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6321)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6321 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6321) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6321))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6321)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6322 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6322) = g32p_row13_cosetRepresentatives 6322 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6322 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6322) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6322))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6322)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6322 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6322) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6322))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6322)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6323 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6323) = g32p_row13_cosetRepresentatives 6323 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6323 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6323) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6323))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6323)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6323 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6323) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6323))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6323)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6324 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6324) = g32p_row13_cosetRepresentatives 6324 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6324 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6324) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6324))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6324)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6324 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6324) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6324))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6324)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6325 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6325) = g32p_row13_cosetRepresentatives 6325 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6325 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6325) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6325))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6325)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6325 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6325) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6325))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6325)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6326 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6326) = g32p_row13_cosetRepresentatives 6326 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6326 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6326) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6326))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6326)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6326 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6326) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6326))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6326)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6327 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6327) = g32p_row13_cosetRepresentatives 6327 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6327 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6327) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6327))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6327)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6327 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6327) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6327))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6327)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6328 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6328) = g32p_row13_cosetRepresentatives 6328 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6328 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6328) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6328))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6328)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6328 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6328) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6328))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6328)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6329 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6329) = g32p_row13_cosetRepresentatives 6329 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6329 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6329) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6329))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6329)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6329 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6329) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6329))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6329)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6330 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6330) = g32p_row13_cosetRepresentatives 6330 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6330 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6330) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6330))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6330)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6330 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6330) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6330))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6330)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6331 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6331) = g32p_row13_cosetRepresentatives 6331 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6331 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6331) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6331))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6331)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6331 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6331) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6331))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6331)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6332 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6332) = g32p_row13_cosetRepresentatives 6332 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6332 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6332) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6332))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6332)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6332 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6332) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6332))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6332)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6333 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6333) = g32p_row13_cosetRepresentatives 6333 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6333 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6333) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6333))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6333)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6333 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6333) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6333))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6333)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6334 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6334) = g32p_row13_cosetRepresentatives 6334 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6334 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6334) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6334))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6334)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6334 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6334) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6334))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6334)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6335 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6335) = g32p_row13_cosetRepresentatives 6335 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6335 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6335) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6335))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6335)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6335 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6335) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6335))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6335)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0395 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 395 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 395 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6320
  · exact g32p_row13_cosetWord_6321
  · exact g32p_row13_cosetWord_6322
  · exact g32p_row13_cosetWord_6323
  · exact g32p_row13_cosetWord_6324
  · exact g32p_row13_cosetWord_6325
  · exact g32p_row13_cosetWord_6326
  · exact g32p_row13_cosetWord_6327
  · exact g32p_row13_cosetWord_6328
  · exact g32p_row13_cosetWord_6329
  · exact g32p_row13_cosetWord_6330
  · exact g32p_row13_cosetWord_6331
  · exact g32p_row13_cosetWord_6332
  · exact g32p_row13_cosetWord_6333
  · exact g32p_row13_cosetWord_6334
  · exact g32p_row13_cosetWord_6335

theorem g32p_row13_cosetGeneratorBlock_0395 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 395 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 395 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 395 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6320 s
  · exact g32p_row13_cosetGeneratorStep_6321 s
  · exact g32p_row13_cosetGeneratorStep_6322 s
  · exact g32p_row13_cosetGeneratorStep_6323 s
  · exact g32p_row13_cosetGeneratorStep_6324 s
  · exact g32p_row13_cosetGeneratorStep_6325 s
  · exact g32p_row13_cosetGeneratorStep_6326 s
  · exact g32p_row13_cosetGeneratorStep_6327 s
  · exact g32p_row13_cosetGeneratorStep_6328 s
  · exact g32p_row13_cosetGeneratorStep_6329 s
  · exact g32p_row13_cosetGeneratorStep_6330 s
  · exact g32p_row13_cosetGeneratorStep_6331 s
  · exact g32p_row13_cosetGeneratorStep_6332 s
  · exact g32p_row13_cosetGeneratorStep_6333 s
  · exact g32p_row13_cosetGeneratorStep_6334 s
  · exact g32p_row13_cosetGeneratorStep_6335 s

theorem g32p_row13_cosetBranchBlock_0395 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 395 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 395 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 395 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6320 s
  · exact g32p_row13_cosetBranchStep_6321 s
  · exact g32p_row13_cosetBranchStep_6322 s
  · exact g32p_row13_cosetBranchStep_6323 s
  · exact g32p_row13_cosetBranchStep_6324 s
  · exact g32p_row13_cosetBranchStep_6325 s
  · exact g32p_row13_cosetBranchStep_6326 s
  · exact g32p_row13_cosetBranchStep_6327 s
  · exact g32p_row13_cosetBranchStep_6328 s
  · exact g32p_row13_cosetBranchStep_6329 s
  · exact g32p_row13_cosetBranchStep_6330 s
  · exact g32p_row13_cosetBranchStep_6331 s
  · exact g32p_row13_cosetBranchStep_6332 s
  · exact g32p_row13_cosetBranchStep_6333 s
  · exact g32p_row13_cosetBranchStep_6334 s
  · exact g32p_row13_cosetBranchStep_6335 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6336 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6336) = g32p_row13_cosetRepresentatives 6336 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6336 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6336) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6336))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6336)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6336 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6336) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6336))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6336)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6337 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6337) = g32p_row13_cosetRepresentatives 6337 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6337 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6337) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6337))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6337)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6337 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6337) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6337))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6337)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6338 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6338) = g32p_row13_cosetRepresentatives 6338 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6338 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6338) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6338))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6338)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6338 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6338) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6338))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6338)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6339 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6339) = g32p_row13_cosetRepresentatives 6339 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6339 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6339) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6339))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6339)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6339 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6339) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6339))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6339)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6340 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6340) = g32p_row13_cosetRepresentatives 6340 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6340 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6340) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6340))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6340)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6340 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6340) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6340))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6340)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6341 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6341) = g32p_row13_cosetRepresentatives 6341 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6341 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6341) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6341))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6341)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6341 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6341) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6341))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6341)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6342 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6342) = g32p_row13_cosetRepresentatives 6342 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6342 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6342) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6342))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6342)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6342 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6342) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6342))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6342)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6343 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6343) = g32p_row13_cosetRepresentatives 6343 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6343 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6343) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6343))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6343)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6343 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6343) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6343))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6343)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6344 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6344) = g32p_row13_cosetRepresentatives 6344 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6344 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6344) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6344))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6344)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6344 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6344) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6344))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6344)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6345 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6345) = g32p_row13_cosetRepresentatives 6345 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6345 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6345) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6345))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6345)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6345 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6345) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6345))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6345)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6346 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6346) = g32p_row13_cosetRepresentatives 6346 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6346 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6346) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6346))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6346)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6346 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6346) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6346))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6346)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6347 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6347) = g32p_row13_cosetRepresentatives 6347 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6347 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6347) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6347))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6347)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6347 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6347) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6347))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6347)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6348 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6348) = g32p_row13_cosetRepresentatives 6348 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6348 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6348) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6348))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6348)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6348 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6348) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6348))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6348)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6349 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6349) = g32p_row13_cosetRepresentatives 6349 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6349 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6349) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6349))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6349)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6349 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6349) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6349))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6349)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6350 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6350) = g32p_row13_cosetRepresentatives 6350 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6350 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6350) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6350))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6350)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6350 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6350) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6350))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6350)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6351 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6351) = g32p_row13_cosetRepresentatives 6351 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6351 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6351) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6351))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6351)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6351 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6351) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6351))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6351)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0396 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 396 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 396 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6336
  · exact g32p_row13_cosetWord_6337
  · exact g32p_row13_cosetWord_6338
  · exact g32p_row13_cosetWord_6339
  · exact g32p_row13_cosetWord_6340
  · exact g32p_row13_cosetWord_6341
  · exact g32p_row13_cosetWord_6342
  · exact g32p_row13_cosetWord_6343
  · exact g32p_row13_cosetWord_6344
  · exact g32p_row13_cosetWord_6345
  · exact g32p_row13_cosetWord_6346
  · exact g32p_row13_cosetWord_6347
  · exact g32p_row13_cosetWord_6348
  · exact g32p_row13_cosetWord_6349
  · exact g32p_row13_cosetWord_6350
  · exact g32p_row13_cosetWord_6351

theorem g32p_row13_cosetGeneratorBlock_0396 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 396 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 396 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 396 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6336 s
  · exact g32p_row13_cosetGeneratorStep_6337 s
  · exact g32p_row13_cosetGeneratorStep_6338 s
  · exact g32p_row13_cosetGeneratorStep_6339 s
  · exact g32p_row13_cosetGeneratorStep_6340 s
  · exact g32p_row13_cosetGeneratorStep_6341 s
  · exact g32p_row13_cosetGeneratorStep_6342 s
  · exact g32p_row13_cosetGeneratorStep_6343 s
  · exact g32p_row13_cosetGeneratorStep_6344 s
  · exact g32p_row13_cosetGeneratorStep_6345 s
  · exact g32p_row13_cosetGeneratorStep_6346 s
  · exact g32p_row13_cosetGeneratorStep_6347 s
  · exact g32p_row13_cosetGeneratorStep_6348 s
  · exact g32p_row13_cosetGeneratorStep_6349 s
  · exact g32p_row13_cosetGeneratorStep_6350 s
  · exact g32p_row13_cosetGeneratorStep_6351 s

theorem g32p_row13_cosetBranchBlock_0396 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 396 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 396 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 396 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6336 s
  · exact g32p_row13_cosetBranchStep_6337 s
  · exact g32p_row13_cosetBranchStep_6338 s
  · exact g32p_row13_cosetBranchStep_6339 s
  · exact g32p_row13_cosetBranchStep_6340 s
  · exact g32p_row13_cosetBranchStep_6341 s
  · exact g32p_row13_cosetBranchStep_6342 s
  · exact g32p_row13_cosetBranchStep_6343 s
  · exact g32p_row13_cosetBranchStep_6344 s
  · exact g32p_row13_cosetBranchStep_6345 s
  · exact g32p_row13_cosetBranchStep_6346 s
  · exact g32p_row13_cosetBranchStep_6347 s
  · exact g32p_row13_cosetBranchStep_6348 s
  · exact g32p_row13_cosetBranchStep_6349 s
  · exact g32p_row13_cosetBranchStep_6350 s
  · exact g32p_row13_cosetBranchStep_6351 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6352 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6352) = g32p_row13_cosetRepresentatives 6352 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6352 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6352) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6352))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6352)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6352 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6352) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6352))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6352)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6353 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6353) = g32p_row13_cosetRepresentatives 6353 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6353 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6353) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6353))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6353)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6353 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6353) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6353))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6353)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6354 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6354) = g32p_row13_cosetRepresentatives 6354 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6354 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6354) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6354))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6354)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6354 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6354) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6354))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6354)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6355 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6355) = g32p_row13_cosetRepresentatives 6355 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6355 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6355) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6355))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6355)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6355 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6355) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6355))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6355)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6356 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6356) = g32p_row13_cosetRepresentatives 6356 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6356 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6356) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6356))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6356)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6356 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6356) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6356))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6356)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6357 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6357) = g32p_row13_cosetRepresentatives 6357 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6357 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6357) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6357))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6357)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6357 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6357) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6357))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6357)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6358 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6358) = g32p_row13_cosetRepresentatives 6358 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6358 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6358) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6358))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6358)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6358 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6358) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6358))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6358)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6359 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6359) = g32p_row13_cosetRepresentatives 6359 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6359 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6359) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6359))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6359)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6359 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6359) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6359))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6359)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6360 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6360) = g32p_row13_cosetRepresentatives 6360 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6360 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6360) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6360))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6360)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6360 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6360) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6360))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6360)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6361 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6361) = g32p_row13_cosetRepresentatives 6361 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6361 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6361) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6361))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6361)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6361 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6361) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6361))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6361)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6362 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6362) = g32p_row13_cosetRepresentatives 6362 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6362 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6362) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6362))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6362)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6362 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6362) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6362))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6362)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6363 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6363) = g32p_row13_cosetRepresentatives 6363 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6363 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6363) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6363))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6363)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6363 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6363) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6363))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6363)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6364 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6364) = g32p_row13_cosetRepresentatives 6364 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6364 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6364) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6364))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6364)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6364 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6364) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6364))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6364)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6365 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6365) = g32p_row13_cosetRepresentatives 6365 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6365 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6365) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6365))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6365)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6365 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6365) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6365))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6365)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6366 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6366) = g32p_row13_cosetRepresentatives 6366 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6366 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6366) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6366))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6366)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6366 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6366) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6366))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6366)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6367 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6367) = g32p_row13_cosetRepresentatives 6367 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6367 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6367) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6367))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6367)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6367 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6367) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6367))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6367)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0397 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 397 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 397 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6352
  · exact g32p_row13_cosetWord_6353
  · exact g32p_row13_cosetWord_6354
  · exact g32p_row13_cosetWord_6355
  · exact g32p_row13_cosetWord_6356
  · exact g32p_row13_cosetWord_6357
  · exact g32p_row13_cosetWord_6358
  · exact g32p_row13_cosetWord_6359
  · exact g32p_row13_cosetWord_6360
  · exact g32p_row13_cosetWord_6361
  · exact g32p_row13_cosetWord_6362
  · exact g32p_row13_cosetWord_6363
  · exact g32p_row13_cosetWord_6364
  · exact g32p_row13_cosetWord_6365
  · exact g32p_row13_cosetWord_6366
  · exact g32p_row13_cosetWord_6367

theorem g32p_row13_cosetGeneratorBlock_0397 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 397 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 397 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 397 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6352 s
  · exact g32p_row13_cosetGeneratorStep_6353 s
  · exact g32p_row13_cosetGeneratorStep_6354 s
  · exact g32p_row13_cosetGeneratorStep_6355 s
  · exact g32p_row13_cosetGeneratorStep_6356 s
  · exact g32p_row13_cosetGeneratorStep_6357 s
  · exact g32p_row13_cosetGeneratorStep_6358 s
  · exact g32p_row13_cosetGeneratorStep_6359 s
  · exact g32p_row13_cosetGeneratorStep_6360 s
  · exact g32p_row13_cosetGeneratorStep_6361 s
  · exact g32p_row13_cosetGeneratorStep_6362 s
  · exact g32p_row13_cosetGeneratorStep_6363 s
  · exact g32p_row13_cosetGeneratorStep_6364 s
  · exact g32p_row13_cosetGeneratorStep_6365 s
  · exact g32p_row13_cosetGeneratorStep_6366 s
  · exact g32p_row13_cosetGeneratorStep_6367 s

theorem g32p_row13_cosetBranchBlock_0397 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 397 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 397 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 397 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6352 s
  · exact g32p_row13_cosetBranchStep_6353 s
  · exact g32p_row13_cosetBranchStep_6354 s
  · exact g32p_row13_cosetBranchStep_6355 s
  · exact g32p_row13_cosetBranchStep_6356 s
  · exact g32p_row13_cosetBranchStep_6357 s
  · exact g32p_row13_cosetBranchStep_6358 s
  · exact g32p_row13_cosetBranchStep_6359 s
  · exact g32p_row13_cosetBranchStep_6360 s
  · exact g32p_row13_cosetBranchStep_6361 s
  · exact g32p_row13_cosetBranchStep_6362 s
  · exact g32p_row13_cosetBranchStep_6363 s
  · exact g32p_row13_cosetBranchStep_6364 s
  · exact g32p_row13_cosetBranchStep_6365 s
  · exact g32p_row13_cosetBranchStep_6366 s
  · exact g32p_row13_cosetBranchStep_6367 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6368 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6368) = g32p_row13_cosetRepresentatives 6368 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6368 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6368) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6368))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6368)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6368 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6368) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6368))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6368)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6369 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6369) = g32p_row13_cosetRepresentatives 6369 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6369 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6369) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6369))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6369)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6369 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6369) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6369))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6369)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6370 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6370) = g32p_row13_cosetRepresentatives 6370 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6370 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6370) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6370))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6370)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6370 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6370) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6370))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6370)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6371 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6371) = g32p_row13_cosetRepresentatives 6371 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6371 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6371) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6371))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6371)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6371 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6371) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6371))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6371)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6372 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6372) = g32p_row13_cosetRepresentatives 6372 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6372 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6372) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6372))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6372)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6372 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6372) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6372))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6372)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6373 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6373) = g32p_row13_cosetRepresentatives 6373 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6373 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6373) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6373))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6373)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6373 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6373) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6373))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6373)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6374 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6374) = g32p_row13_cosetRepresentatives 6374 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6374 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6374) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6374))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6374)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6374 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6374) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6374))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6374)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6375 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6375) = g32p_row13_cosetRepresentatives 6375 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6375 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6375) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6375))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6375)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6375 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6375) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6375))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6375)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6376 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6376) = g32p_row13_cosetRepresentatives 6376 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6376 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6376) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6376))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6376)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6376 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6376) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6376))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6376)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6377 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6377) = g32p_row13_cosetRepresentatives 6377 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6377 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6377) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6377))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6377)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6377 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6377) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6377))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6377)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6378 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6378) = g32p_row13_cosetRepresentatives 6378 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6378 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6378) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6378))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6378)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6378 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6378) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6378))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6378)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6379 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6379) = g32p_row13_cosetRepresentatives 6379 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6379 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6379) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6379))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6379)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6379 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6379) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6379))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6379)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6380 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6380) = g32p_row13_cosetRepresentatives 6380 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6380 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6380) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6380))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6380)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6380 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6380) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6380))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6380)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6381 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6381) = g32p_row13_cosetRepresentatives 6381 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6381 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6381) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6381))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6381)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6381 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6381) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6381))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6381)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6382 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6382) = g32p_row13_cosetRepresentatives 6382 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6382 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6382) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6382))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6382)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6382 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6382) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6382))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6382)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6383 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6383) = g32p_row13_cosetRepresentatives 6383 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6383 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6383) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6383))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6383)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6383 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6383) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6383))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6383)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0398 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 398 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 398 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6368
  · exact g32p_row13_cosetWord_6369
  · exact g32p_row13_cosetWord_6370
  · exact g32p_row13_cosetWord_6371
  · exact g32p_row13_cosetWord_6372
  · exact g32p_row13_cosetWord_6373
  · exact g32p_row13_cosetWord_6374
  · exact g32p_row13_cosetWord_6375
  · exact g32p_row13_cosetWord_6376
  · exact g32p_row13_cosetWord_6377
  · exact g32p_row13_cosetWord_6378
  · exact g32p_row13_cosetWord_6379
  · exact g32p_row13_cosetWord_6380
  · exact g32p_row13_cosetWord_6381
  · exact g32p_row13_cosetWord_6382
  · exact g32p_row13_cosetWord_6383

theorem g32p_row13_cosetGeneratorBlock_0398 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 398 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 398 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 398 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6368 s
  · exact g32p_row13_cosetGeneratorStep_6369 s
  · exact g32p_row13_cosetGeneratorStep_6370 s
  · exact g32p_row13_cosetGeneratorStep_6371 s
  · exact g32p_row13_cosetGeneratorStep_6372 s
  · exact g32p_row13_cosetGeneratorStep_6373 s
  · exact g32p_row13_cosetGeneratorStep_6374 s
  · exact g32p_row13_cosetGeneratorStep_6375 s
  · exact g32p_row13_cosetGeneratorStep_6376 s
  · exact g32p_row13_cosetGeneratorStep_6377 s
  · exact g32p_row13_cosetGeneratorStep_6378 s
  · exact g32p_row13_cosetGeneratorStep_6379 s
  · exact g32p_row13_cosetGeneratorStep_6380 s
  · exact g32p_row13_cosetGeneratorStep_6381 s
  · exact g32p_row13_cosetGeneratorStep_6382 s
  · exact g32p_row13_cosetGeneratorStep_6383 s

theorem g32p_row13_cosetBranchBlock_0398 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 398 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 398 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 398 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6368 s
  · exact g32p_row13_cosetBranchStep_6369 s
  · exact g32p_row13_cosetBranchStep_6370 s
  · exact g32p_row13_cosetBranchStep_6371 s
  · exact g32p_row13_cosetBranchStep_6372 s
  · exact g32p_row13_cosetBranchStep_6373 s
  · exact g32p_row13_cosetBranchStep_6374 s
  · exact g32p_row13_cosetBranchStep_6375 s
  · exact g32p_row13_cosetBranchStep_6376 s
  · exact g32p_row13_cosetBranchStep_6377 s
  · exact g32p_row13_cosetBranchStep_6378 s
  · exact g32p_row13_cosetBranchStep_6379 s
  · exact g32p_row13_cosetBranchStep_6380 s
  · exact g32p_row13_cosetBranchStep_6381 s
  · exact g32p_row13_cosetBranchStep_6382 s
  · exact g32p_row13_cosetBranchStep_6383 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_6384 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6384) = g32p_row13_cosetRepresentatives 6384 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6384 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6384) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6384))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6384)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6384 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6384) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6384))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6384)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6385 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6385) = g32p_row13_cosetRepresentatives 6385 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6385 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6385) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6385))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6385)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6385 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6385) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6385))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6385)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6386 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6386) = g32p_row13_cosetRepresentatives 6386 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6386 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6386) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6386))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6386)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6386 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6386) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6386))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6386)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6387 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6387) = g32p_row13_cosetRepresentatives 6387 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6387 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6387) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6387))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6387)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6387 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6387) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6387))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6387)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6388 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6388) = g32p_row13_cosetRepresentatives 6388 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6388 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6388) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6388))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6388)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6388 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6388) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6388))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6388)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6389 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6389) = g32p_row13_cosetRepresentatives 6389 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6389 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6389) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6389))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6389)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6389 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6389) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6389))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6389)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6390 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6390) = g32p_row13_cosetRepresentatives 6390 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6390 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6390) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6390))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6390)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6390 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6390) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6390))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6390)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6391 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6391) = g32p_row13_cosetRepresentatives 6391 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6391 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6391) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6391))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6391)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6391 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6391) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6391))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6391)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6392 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6392) = g32p_row13_cosetRepresentatives 6392 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6392 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6392) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6392))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6392)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6392 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6392) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6392))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6392)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6393 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6393) = g32p_row13_cosetRepresentatives 6393 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6393 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6393) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6393))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6393)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6393 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6393) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6393))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6393)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6394 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6394) = g32p_row13_cosetRepresentatives 6394 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6394 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6394) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6394))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6394)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6394 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6394) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6394))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6394)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6395 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6395) = g32p_row13_cosetRepresentatives 6395 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6395 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6395) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6395))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6395)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6395 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6395) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6395))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6395)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6396 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6396) = g32p_row13_cosetRepresentatives 6396 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6396 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6396) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6396))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6396)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6396 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6396) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6396))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6396)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6397 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6397) = g32p_row13_cosetRepresentatives 6397 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6397 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6397) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6397))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6397)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6397 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6397) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6397))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6397)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6398 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6398) = g32p_row13_cosetRepresentatives 6398 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6398 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6398) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6398))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6398)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6398 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6398) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6398))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6398)) := by
  decide +kernel

theorem g32p_row13_cosetWord_6399 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 6399) = g32p_row13_cosetRepresentatives 6399 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_6399 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 6399) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 6399))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 6399)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_6399 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 6399) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 6399))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 6399)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0399 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 399 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 399 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_6384
  · exact g32p_row13_cosetWord_6385
  · exact g32p_row13_cosetWord_6386
  · exact g32p_row13_cosetWord_6387
  · exact g32p_row13_cosetWord_6388
  · exact g32p_row13_cosetWord_6389
  · exact g32p_row13_cosetWord_6390
  · exact g32p_row13_cosetWord_6391
  · exact g32p_row13_cosetWord_6392
  · exact g32p_row13_cosetWord_6393
  · exact g32p_row13_cosetWord_6394
  · exact g32p_row13_cosetWord_6395
  · exact g32p_row13_cosetWord_6396
  · exact g32p_row13_cosetWord_6397
  · exact g32p_row13_cosetWord_6398
  · exact g32p_row13_cosetWord_6399

theorem g32p_row13_cosetGeneratorBlock_0399 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 399 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 399 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 399 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_6384 s
  · exact g32p_row13_cosetGeneratorStep_6385 s
  · exact g32p_row13_cosetGeneratorStep_6386 s
  · exact g32p_row13_cosetGeneratorStep_6387 s
  · exact g32p_row13_cosetGeneratorStep_6388 s
  · exact g32p_row13_cosetGeneratorStep_6389 s
  · exact g32p_row13_cosetGeneratorStep_6390 s
  · exact g32p_row13_cosetGeneratorStep_6391 s
  · exact g32p_row13_cosetGeneratorStep_6392 s
  · exact g32p_row13_cosetGeneratorStep_6393 s
  · exact g32p_row13_cosetGeneratorStep_6394 s
  · exact g32p_row13_cosetGeneratorStep_6395 s
  · exact g32p_row13_cosetGeneratorStep_6396 s
  · exact g32p_row13_cosetGeneratorStep_6397 s
  · exact g32p_row13_cosetGeneratorStep_6398 s
  · exact g32p_row13_cosetGeneratorStep_6399 s

theorem g32p_row13_cosetBranchBlock_0399 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 399 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 399 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 399 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_6384 s
  · exact g32p_row13_cosetBranchStep_6385 s
  · exact g32p_row13_cosetBranchStep_6386 s
  · exact g32p_row13_cosetBranchStep_6387 s
  · exact g32p_row13_cosetBranchStep_6388 s
  · exact g32p_row13_cosetBranchStep_6389 s
  · exact g32p_row13_cosetBranchStep_6390 s
  · exact g32p_row13_cosetBranchStep_6391 s
  · exact g32p_row13_cosetBranchStep_6392 s
  · exact g32p_row13_cosetBranchStep_6393 s
  · exact g32p_row13_cosetBranchStep_6394 s
  · exact g32p_row13_cosetBranchStep_6395 s
  · exact g32p_row13_cosetBranchStep_6396 s
  · exact g32p_row13_cosetBranchStep_6397 s
  · exact g32p_row13_cosetBranchStep_6398 s
  · exact g32p_row13_cosetBranchStep_6399 s


end HodgeLean.Foundations.Program

end
