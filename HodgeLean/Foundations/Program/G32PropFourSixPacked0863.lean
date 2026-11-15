import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0835

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6912 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6912) = g32p_row31_cosetRepresentatives 6912 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6912 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6912) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6912))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6912)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6912 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6912) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6912))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6912)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6913 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6913) = g32p_row31_cosetRepresentatives 6913 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6913 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6913) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6913))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6913)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6913 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6913) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6913))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6913)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6914 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6914) = g32p_row31_cosetRepresentatives 6914 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6914 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6914) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6914))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6914)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6914 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6914) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6914))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6914)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6915 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6915) = g32p_row31_cosetRepresentatives 6915 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6915 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6915) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6915))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6915)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6915 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6915) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6915))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6915)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6916 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6916) = g32p_row31_cosetRepresentatives 6916 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6916 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6916) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6916))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6916)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6916 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6916) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6916))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6916)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6917 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6917) = g32p_row31_cosetRepresentatives 6917 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6917 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6917) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6917))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6917)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6917 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6917) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6917))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6917)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6918 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6918) = g32p_row31_cosetRepresentatives 6918 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6918 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6918) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6918))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6918)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6918 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6918) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6918))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6918)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6919 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6919) = g32p_row31_cosetRepresentatives 6919 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6919 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6919) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6919))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6919)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6919 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6919) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6919))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6919)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6920 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6920) = g32p_row31_cosetRepresentatives 6920 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6920 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6920) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6920))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6920)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6920 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6920) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6920))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6920)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6921 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6921) = g32p_row31_cosetRepresentatives 6921 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6921 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6921) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6921))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6921)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6921 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6921) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6921))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6921)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6922 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6922) = g32p_row31_cosetRepresentatives 6922 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6922 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6922) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6922))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6922)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6922 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6922) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6922))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6922)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6923 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6923) = g32p_row31_cosetRepresentatives 6923 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6923 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6923) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6923))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6923)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6923 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6923) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6923))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6923)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6924 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6924) = g32p_row31_cosetRepresentatives 6924 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6924 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6924) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6924))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6924)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6924 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6924) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6924))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6924)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6925 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6925) = g32p_row31_cosetRepresentatives 6925 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6925 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6925) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6925))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6925)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6925 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6925) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6925))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6925)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6926 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6926) = g32p_row31_cosetRepresentatives 6926 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6926 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6926) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6926))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6926)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6926 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6926) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6926))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6926)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6927 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6927) = g32p_row31_cosetRepresentatives 6927 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6927 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6927) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6927))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6927)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6927 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6927) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6927))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6927)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0432 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 432 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 432 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6912
  · exact g32p_row31_cosetWord_6913
  · exact g32p_row31_cosetWord_6914
  · exact g32p_row31_cosetWord_6915
  · exact g32p_row31_cosetWord_6916
  · exact g32p_row31_cosetWord_6917
  · exact g32p_row31_cosetWord_6918
  · exact g32p_row31_cosetWord_6919
  · exact g32p_row31_cosetWord_6920
  · exact g32p_row31_cosetWord_6921
  · exact g32p_row31_cosetWord_6922
  · exact g32p_row31_cosetWord_6923
  · exact g32p_row31_cosetWord_6924
  · exact g32p_row31_cosetWord_6925
  · exact g32p_row31_cosetWord_6926
  · exact g32p_row31_cosetWord_6927

theorem g32p_row31_cosetGeneratorBlock_0432 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 432 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 432 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 432 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6912 s
  · exact g32p_row31_cosetGeneratorStep_6913 s
  · exact g32p_row31_cosetGeneratorStep_6914 s
  · exact g32p_row31_cosetGeneratorStep_6915 s
  · exact g32p_row31_cosetGeneratorStep_6916 s
  · exact g32p_row31_cosetGeneratorStep_6917 s
  · exact g32p_row31_cosetGeneratorStep_6918 s
  · exact g32p_row31_cosetGeneratorStep_6919 s
  · exact g32p_row31_cosetGeneratorStep_6920 s
  · exact g32p_row31_cosetGeneratorStep_6921 s
  · exact g32p_row31_cosetGeneratorStep_6922 s
  · exact g32p_row31_cosetGeneratorStep_6923 s
  · exact g32p_row31_cosetGeneratorStep_6924 s
  · exact g32p_row31_cosetGeneratorStep_6925 s
  · exact g32p_row31_cosetGeneratorStep_6926 s
  · exact g32p_row31_cosetGeneratorStep_6927 s

theorem g32p_row31_cosetBranchBlock_0432 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 432 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 432 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 432 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6912 s
  · exact g32p_row31_cosetBranchStep_6913 s
  · exact g32p_row31_cosetBranchStep_6914 s
  · exact g32p_row31_cosetBranchStep_6915 s
  · exact g32p_row31_cosetBranchStep_6916 s
  · exact g32p_row31_cosetBranchStep_6917 s
  · exact g32p_row31_cosetBranchStep_6918 s
  · exact g32p_row31_cosetBranchStep_6919 s
  · exact g32p_row31_cosetBranchStep_6920 s
  · exact g32p_row31_cosetBranchStep_6921 s
  · exact g32p_row31_cosetBranchStep_6922 s
  · exact g32p_row31_cosetBranchStep_6923 s
  · exact g32p_row31_cosetBranchStep_6924 s
  · exact g32p_row31_cosetBranchStep_6925 s
  · exact g32p_row31_cosetBranchStep_6926 s
  · exact g32p_row31_cosetBranchStep_6927 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6928 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6928) = g32p_row31_cosetRepresentatives 6928 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6928 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6928) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6928))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6928)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6928 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6928) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6928))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6928)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6929 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6929) = g32p_row31_cosetRepresentatives 6929 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6929 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6929) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6929))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6929)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6929 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6929) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6929))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6929)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6930 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6930) = g32p_row31_cosetRepresentatives 6930 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6930 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6930) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6930))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6930)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6930 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6930) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6930))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6930)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6931 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6931) = g32p_row31_cosetRepresentatives 6931 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6931 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6931) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6931))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6931)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6931 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6931) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6931))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6931)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6932 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6932) = g32p_row31_cosetRepresentatives 6932 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6932 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6932) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6932))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6932)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6932 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6932) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6932))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6932)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6933 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6933) = g32p_row31_cosetRepresentatives 6933 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6933 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6933) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6933))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6933)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6933 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6933) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6933))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6933)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6934 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6934) = g32p_row31_cosetRepresentatives 6934 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6934 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6934) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6934))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6934)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6934 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6934) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6934))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6934)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6935 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6935) = g32p_row31_cosetRepresentatives 6935 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6935 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6935) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6935))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6935)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6935 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6935) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6935))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6935)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6936 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6936) = g32p_row31_cosetRepresentatives 6936 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6936 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6936) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6936))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6936)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6936 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6936) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6936))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6936)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6937 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6937) = g32p_row31_cosetRepresentatives 6937 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6937 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6937) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6937))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6937)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6937 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6937) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6937))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6937)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6938 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6938) = g32p_row31_cosetRepresentatives 6938 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6938 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6938) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6938))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6938)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6938 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6938) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6938))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6938)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6939 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6939) = g32p_row31_cosetRepresentatives 6939 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6939 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6939) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6939))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6939)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6939 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6939) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6939))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6939)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6940 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6940) = g32p_row31_cosetRepresentatives 6940 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6940 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6940) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6940))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6940)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6940 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6940) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6940))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6940)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6941 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6941) = g32p_row31_cosetRepresentatives 6941 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6941 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6941) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6941))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6941)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6941 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6941) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6941))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6941)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6942 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6942) = g32p_row31_cosetRepresentatives 6942 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6942 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6942) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6942))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6942)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6942 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6942) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6942))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6942)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6943 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6943) = g32p_row31_cosetRepresentatives 6943 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6943 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6943) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6943))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6943)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6943 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6943) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6943))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6943)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0433 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 433 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 433 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6928
  · exact g32p_row31_cosetWord_6929
  · exact g32p_row31_cosetWord_6930
  · exact g32p_row31_cosetWord_6931
  · exact g32p_row31_cosetWord_6932
  · exact g32p_row31_cosetWord_6933
  · exact g32p_row31_cosetWord_6934
  · exact g32p_row31_cosetWord_6935
  · exact g32p_row31_cosetWord_6936
  · exact g32p_row31_cosetWord_6937
  · exact g32p_row31_cosetWord_6938
  · exact g32p_row31_cosetWord_6939
  · exact g32p_row31_cosetWord_6940
  · exact g32p_row31_cosetWord_6941
  · exact g32p_row31_cosetWord_6942
  · exact g32p_row31_cosetWord_6943

theorem g32p_row31_cosetGeneratorBlock_0433 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 433 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 433 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 433 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6928 s
  · exact g32p_row31_cosetGeneratorStep_6929 s
  · exact g32p_row31_cosetGeneratorStep_6930 s
  · exact g32p_row31_cosetGeneratorStep_6931 s
  · exact g32p_row31_cosetGeneratorStep_6932 s
  · exact g32p_row31_cosetGeneratorStep_6933 s
  · exact g32p_row31_cosetGeneratorStep_6934 s
  · exact g32p_row31_cosetGeneratorStep_6935 s
  · exact g32p_row31_cosetGeneratorStep_6936 s
  · exact g32p_row31_cosetGeneratorStep_6937 s
  · exact g32p_row31_cosetGeneratorStep_6938 s
  · exact g32p_row31_cosetGeneratorStep_6939 s
  · exact g32p_row31_cosetGeneratorStep_6940 s
  · exact g32p_row31_cosetGeneratorStep_6941 s
  · exact g32p_row31_cosetGeneratorStep_6942 s
  · exact g32p_row31_cosetGeneratorStep_6943 s

theorem g32p_row31_cosetBranchBlock_0433 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 433 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 433 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 433 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6928 s
  · exact g32p_row31_cosetBranchStep_6929 s
  · exact g32p_row31_cosetBranchStep_6930 s
  · exact g32p_row31_cosetBranchStep_6931 s
  · exact g32p_row31_cosetBranchStep_6932 s
  · exact g32p_row31_cosetBranchStep_6933 s
  · exact g32p_row31_cosetBranchStep_6934 s
  · exact g32p_row31_cosetBranchStep_6935 s
  · exact g32p_row31_cosetBranchStep_6936 s
  · exact g32p_row31_cosetBranchStep_6937 s
  · exact g32p_row31_cosetBranchStep_6938 s
  · exact g32p_row31_cosetBranchStep_6939 s
  · exact g32p_row31_cosetBranchStep_6940 s
  · exact g32p_row31_cosetBranchStep_6941 s
  · exact g32p_row31_cosetBranchStep_6942 s
  · exact g32p_row31_cosetBranchStep_6943 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6944 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6944) = g32p_row31_cosetRepresentatives 6944 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6944 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6944) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6944))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6944)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6944 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6944) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6944))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6944)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6945 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6945) = g32p_row31_cosetRepresentatives 6945 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6945 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6945) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6945))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6945)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6945 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6945) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6945))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6945)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6946 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6946) = g32p_row31_cosetRepresentatives 6946 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6946 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6946) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6946))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6946)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6946 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6946) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6946))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6946)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6947 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6947) = g32p_row31_cosetRepresentatives 6947 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6947 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6947) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6947))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6947)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6947 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6947) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6947))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6947)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6948 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6948) = g32p_row31_cosetRepresentatives 6948 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6948 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6948) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6948))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6948)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6948 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6948) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6948))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6948)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6949 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6949) = g32p_row31_cosetRepresentatives 6949 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6949 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6949) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6949))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6949)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6949 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6949) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6949))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6949)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6950 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6950) = g32p_row31_cosetRepresentatives 6950 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6950 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6950) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6950))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6950)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6950 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6950) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6950))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6950)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6951 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6951) = g32p_row31_cosetRepresentatives 6951 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6951 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6951) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6951))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6951)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6951 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6951) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6951))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6951)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6952 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6952) = g32p_row31_cosetRepresentatives 6952 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6952 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6952) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6952))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6952)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6952 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6952) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6952))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6952)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6953 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6953) = g32p_row31_cosetRepresentatives 6953 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6953 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6953) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6953))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6953)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6953 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6953) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6953))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6953)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6954 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6954) = g32p_row31_cosetRepresentatives 6954 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6954 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6954) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6954))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6954)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6954 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6954) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6954))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6954)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6955 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6955) = g32p_row31_cosetRepresentatives 6955 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6955 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6955) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6955))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6955)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6955 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6955) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6955))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6955)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6956 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6956) = g32p_row31_cosetRepresentatives 6956 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6956 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6956) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6956))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6956)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6956 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6956) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6956))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6956)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6957 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6957) = g32p_row31_cosetRepresentatives 6957 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6957 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6957) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6957))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6957)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6957 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6957) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6957))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6957)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6958 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6958) = g32p_row31_cosetRepresentatives 6958 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6958 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6958) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6958))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6958)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6958 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6958) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6958))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6958)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6959 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6959) = g32p_row31_cosetRepresentatives 6959 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6959 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6959) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6959))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6959)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6959 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6959) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6959))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6959)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0434 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 434 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 434 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6944
  · exact g32p_row31_cosetWord_6945
  · exact g32p_row31_cosetWord_6946
  · exact g32p_row31_cosetWord_6947
  · exact g32p_row31_cosetWord_6948
  · exact g32p_row31_cosetWord_6949
  · exact g32p_row31_cosetWord_6950
  · exact g32p_row31_cosetWord_6951
  · exact g32p_row31_cosetWord_6952
  · exact g32p_row31_cosetWord_6953
  · exact g32p_row31_cosetWord_6954
  · exact g32p_row31_cosetWord_6955
  · exact g32p_row31_cosetWord_6956
  · exact g32p_row31_cosetWord_6957
  · exact g32p_row31_cosetWord_6958
  · exact g32p_row31_cosetWord_6959

theorem g32p_row31_cosetGeneratorBlock_0434 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 434 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 434 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 434 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6944 s
  · exact g32p_row31_cosetGeneratorStep_6945 s
  · exact g32p_row31_cosetGeneratorStep_6946 s
  · exact g32p_row31_cosetGeneratorStep_6947 s
  · exact g32p_row31_cosetGeneratorStep_6948 s
  · exact g32p_row31_cosetGeneratorStep_6949 s
  · exact g32p_row31_cosetGeneratorStep_6950 s
  · exact g32p_row31_cosetGeneratorStep_6951 s
  · exact g32p_row31_cosetGeneratorStep_6952 s
  · exact g32p_row31_cosetGeneratorStep_6953 s
  · exact g32p_row31_cosetGeneratorStep_6954 s
  · exact g32p_row31_cosetGeneratorStep_6955 s
  · exact g32p_row31_cosetGeneratorStep_6956 s
  · exact g32p_row31_cosetGeneratorStep_6957 s
  · exact g32p_row31_cosetGeneratorStep_6958 s
  · exact g32p_row31_cosetGeneratorStep_6959 s

theorem g32p_row31_cosetBranchBlock_0434 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 434 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 434 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 434 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6944 s
  · exact g32p_row31_cosetBranchStep_6945 s
  · exact g32p_row31_cosetBranchStep_6946 s
  · exact g32p_row31_cosetBranchStep_6947 s
  · exact g32p_row31_cosetBranchStep_6948 s
  · exact g32p_row31_cosetBranchStep_6949 s
  · exact g32p_row31_cosetBranchStep_6950 s
  · exact g32p_row31_cosetBranchStep_6951 s
  · exact g32p_row31_cosetBranchStep_6952 s
  · exact g32p_row31_cosetBranchStep_6953 s
  · exact g32p_row31_cosetBranchStep_6954 s
  · exact g32p_row31_cosetBranchStep_6955 s
  · exact g32p_row31_cosetBranchStep_6956 s
  · exact g32p_row31_cosetBranchStep_6957 s
  · exact g32p_row31_cosetBranchStep_6958 s
  · exact g32p_row31_cosetBranchStep_6959 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6960 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6960) = g32p_row31_cosetRepresentatives 6960 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6960 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6960) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6960))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6960)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6960 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6960) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6960))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6960)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6961 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6961) = g32p_row31_cosetRepresentatives 6961 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6961 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6961) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6961))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6961)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6961 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6961) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6961))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6961)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6962 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6962) = g32p_row31_cosetRepresentatives 6962 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6962 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6962) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6962))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6962)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6962 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6962) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6962))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6962)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6963 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6963) = g32p_row31_cosetRepresentatives 6963 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6963 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6963) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6963))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6963)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6963 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6963) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6963))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6963)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6964 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6964) = g32p_row31_cosetRepresentatives 6964 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6964 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6964) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6964))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6964)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6964 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6964) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6964))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6964)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6965 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6965) = g32p_row31_cosetRepresentatives 6965 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6965 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6965) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6965))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6965)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6965 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6965) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6965))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6965)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6966 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6966) = g32p_row31_cosetRepresentatives 6966 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6966 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6966) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6966))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6966)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6966 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6966) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6966))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6966)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6967 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6967) = g32p_row31_cosetRepresentatives 6967 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6967 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6967) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6967))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6967)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6967 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6967) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6967))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6967)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6968 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6968) = g32p_row31_cosetRepresentatives 6968 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6968 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6968) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6968))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6968)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6968 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6968) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6968))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6968)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6969 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6969) = g32p_row31_cosetRepresentatives 6969 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6969 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6969) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6969))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6969)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6969 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6969) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6969))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6969)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6970 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6970) = g32p_row31_cosetRepresentatives 6970 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6970 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6970) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6970))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6970)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6970 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6970) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6970))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6970)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6971 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6971) = g32p_row31_cosetRepresentatives 6971 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6971 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6971) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6971))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6971)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6971 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6971) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6971))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6971)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6972 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6972) = g32p_row31_cosetRepresentatives 6972 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6972 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6972) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6972))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6972)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6972 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6972) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6972))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6972)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6973 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6973) = g32p_row31_cosetRepresentatives 6973 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6973 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6973) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6973))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6973)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6973 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6973) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6973))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6973)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6974 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6974) = g32p_row31_cosetRepresentatives 6974 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6974 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6974) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6974))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6974)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6974 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6974) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6974))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6974)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6975 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6975) = g32p_row31_cosetRepresentatives 6975 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6975 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6975) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6975))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6975)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6975 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6975) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6975))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6975)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0435 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 435 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 435 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6960
  · exact g32p_row31_cosetWord_6961
  · exact g32p_row31_cosetWord_6962
  · exact g32p_row31_cosetWord_6963
  · exact g32p_row31_cosetWord_6964
  · exact g32p_row31_cosetWord_6965
  · exact g32p_row31_cosetWord_6966
  · exact g32p_row31_cosetWord_6967
  · exact g32p_row31_cosetWord_6968
  · exact g32p_row31_cosetWord_6969
  · exact g32p_row31_cosetWord_6970
  · exact g32p_row31_cosetWord_6971
  · exact g32p_row31_cosetWord_6972
  · exact g32p_row31_cosetWord_6973
  · exact g32p_row31_cosetWord_6974
  · exact g32p_row31_cosetWord_6975

theorem g32p_row31_cosetGeneratorBlock_0435 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 435 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 435 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 435 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6960 s
  · exact g32p_row31_cosetGeneratorStep_6961 s
  · exact g32p_row31_cosetGeneratorStep_6962 s
  · exact g32p_row31_cosetGeneratorStep_6963 s
  · exact g32p_row31_cosetGeneratorStep_6964 s
  · exact g32p_row31_cosetGeneratorStep_6965 s
  · exact g32p_row31_cosetGeneratorStep_6966 s
  · exact g32p_row31_cosetGeneratorStep_6967 s
  · exact g32p_row31_cosetGeneratorStep_6968 s
  · exact g32p_row31_cosetGeneratorStep_6969 s
  · exact g32p_row31_cosetGeneratorStep_6970 s
  · exact g32p_row31_cosetGeneratorStep_6971 s
  · exact g32p_row31_cosetGeneratorStep_6972 s
  · exact g32p_row31_cosetGeneratorStep_6973 s
  · exact g32p_row31_cosetGeneratorStep_6974 s
  · exact g32p_row31_cosetGeneratorStep_6975 s

theorem g32p_row31_cosetBranchBlock_0435 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 435 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 435 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 435 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6960 s
  · exact g32p_row31_cosetBranchStep_6961 s
  · exact g32p_row31_cosetBranchStep_6962 s
  · exact g32p_row31_cosetBranchStep_6963 s
  · exact g32p_row31_cosetBranchStep_6964 s
  · exact g32p_row31_cosetBranchStep_6965 s
  · exact g32p_row31_cosetBranchStep_6966 s
  · exact g32p_row31_cosetBranchStep_6967 s
  · exact g32p_row31_cosetBranchStep_6968 s
  · exact g32p_row31_cosetBranchStep_6969 s
  · exact g32p_row31_cosetBranchStep_6970 s
  · exact g32p_row31_cosetBranchStep_6971 s
  · exact g32p_row31_cosetBranchStep_6972 s
  · exact g32p_row31_cosetBranchStep_6973 s
  · exact g32p_row31_cosetBranchStep_6974 s
  · exact g32p_row31_cosetBranchStep_6975 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6976 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6976) = g32p_row31_cosetRepresentatives 6976 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6976 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6976) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6976))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6976)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6976 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6976) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6976))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6976)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6977 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6977) = g32p_row31_cosetRepresentatives 6977 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6977 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6977) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6977))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6977)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6977 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6977) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6977))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6977)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6978 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6978) = g32p_row31_cosetRepresentatives 6978 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6978 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6978) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6978))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6978)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6978 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6978) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6978))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6978)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6979 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6979) = g32p_row31_cosetRepresentatives 6979 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6979 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6979) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6979))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6979)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6979 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6979) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6979))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6979)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6980 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6980) = g32p_row31_cosetRepresentatives 6980 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6980 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6980) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6980))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6980)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6980 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6980) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6980))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6980)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6981 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6981) = g32p_row31_cosetRepresentatives 6981 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6981 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6981) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6981))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6981)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6981 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6981) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6981))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6981)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6982 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6982) = g32p_row31_cosetRepresentatives 6982 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6982 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6982) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6982))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6982)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6982 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6982) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6982))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6982)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6983 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6983) = g32p_row31_cosetRepresentatives 6983 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6983 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6983) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6983))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6983)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6983 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6983) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6983))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6983)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6984 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6984) = g32p_row31_cosetRepresentatives 6984 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6984 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6984) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6984))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6984)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6984 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6984) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6984))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6984)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6985 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6985) = g32p_row31_cosetRepresentatives 6985 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6985 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6985) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6985))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6985)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6985 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6985) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6985))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6985)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6986 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6986) = g32p_row31_cosetRepresentatives 6986 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6986 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6986) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6986))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6986)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6986 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6986) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6986))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6986)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6987 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6987) = g32p_row31_cosetRepresentatives 6987 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6987 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6987) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6987))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6987)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6987 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6987) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6987))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6987)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6988 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6988) = g32p_row31_cosetRepresentatives 6988 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6988 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6988) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6988))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6988)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6988 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6988) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6988))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6988)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6989 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6989) = g32p_row31_cosetRepresentatives 6989 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6989 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6989) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6989))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6989)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6989 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6989) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6989))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6989)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6990 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6990) = g32p_row31_cosetRepresentatives 6990 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6990 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6990) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6990))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6990)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6990 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6990) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6990))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6990)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6991 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6991) = g32p_row31_cosetRepresentatives 6991 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6991 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6991) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6991))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6991)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6991 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6991) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6991))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6991)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0436 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 436 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 436 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6976
  · exact g32p_row31_cosetWord_6977
  · exact g32p_row31_cosetWord_6978
  · exact g32p_row31_cosetWord_6979
  · exact g32p_row31_cosetWord_6980
  · exact g32p_row31_cosetWord_6981
  · exact g32p_row31_cosetWord_6982
  · exact g32p_row31_cosetWord_6983
  · exact g32p_row31_cosetWord_6984
  · exact g32p_row31_cosetWord_6985
  · exact g32p_row31_cosetWord_6986
  · exact g32p_row31_cosetWord_6987
  · exact g32p_row31_cosetWord_6988
  · exact g32p_row31_cosetWord_6989
  · exact g32p_row31_cosetWord_6990
  · exact g32p_row31_cosetWord_6991

theorem g32p_row31_cosetGeneratorBlock_0436 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 436 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 436 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 436 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6976 s
  · exact g32p_row31_cosetGeneratorStep_6977 s
  · exact g32p_row31_cosetGeneratorStep_6978 s
  · exact g32p_row31_cosetGeneratorStep_6979 s
  · exact g32p_row31_cosetGeneratorStep_6980 s
  · exact g32p_row31_cosetGeneratorStep_6981 s
  · exact g32p_row31_cosetGeneratorStep_6982 s
  · exact g32p_row31_cosetGeneratorStep_6983 s
  · exact g32p_row31_cosetGeneratorStep_6984 s
  · exact g32p_row31_cosetGeneratorStep_6985 s
  · exact g32p_row31_cosetGeneratorStep_6986 s
  · exact g32p_row31_cosetGeneratorStep_6987 s
  · exact g32p_row31_cosetGeneratorStep_6988 s
  · exact g32p_row31_cosetGeneratorStep_6989 s
  · exact g32p_row31_cosetGeneratorStep_6990 s
  · exact g32p_row31_cosetGeneratorStep_6991 s

theorem g32p_row31_cosetBranchBlock_0436 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 436 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 436 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 436 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6976 s
  · exact g32p_row31_cosetBranchStep_6977 s
  · exact g32p_row31_cosetBranchStep_6978 s
  · exact g32p_row31_cosetBranchStep_6979 s
  · exact g32p_row31_cosetBranchStep_6980 s
  · exact g32p_row31_cosetBranchStep_6981 s
  · exact g32p_row31_cosetBranchStep_6982 s
  · exact g32p_row31_cosetBranchStep_6983 s
  · exact g32p_row31_cosetBranchStep_6984 s
  · exact g32p_row31_cosetBranchStep_6985 s
  · exact g32p_row31_cosetBranchStep_6986 s
  · exact g32p_row31_cosetBranchStep_6987 s
  · exact g32p_row31_cosetBranchStep_6988 s
  · exact g32p_row31_cosetBranchStep_6989 s
  · exact g32p_row31_cosetBranchStep_6990 s
  · exact g32p_row31_cosetBranchStep_6991 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_6992 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6992) = g32p_row31_cosetRepresentatives 6992 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6992 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6992) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6992))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6992)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6992 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6992) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6992))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6992)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6993 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6993) = g32p_row31_cosetRepresentatives 6993 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6993 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6993) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6993))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6993)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6993 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6993) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6993))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6993)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6994 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6994) = g32p_row31_cosetRepresentatives 6994 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6994 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6994) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6994))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6994)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6994 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6994) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6994))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6994)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6995 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6995) = g32p_row31_cosetRepresentatives 6995 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6995 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6995) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6995))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6995)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6995 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6995) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6995))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6995)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6996 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6996) = g32p_row31_cosetRepresentatives 6996 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6996 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6996) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6996))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6996)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6996 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6996) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6996))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6996)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6997 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6997) = g32p_row31_cosetRepresentatives 6997 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6997 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6997) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6997))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6997)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6997 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6997) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6997))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6997)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6998 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6998) = g32p_row31_cosetRepresentatives 6998 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6998 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6998) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6998))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6998)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6998 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6998) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6998))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6998)) := by
  decide +kernel

theorem g32p_row31_cosetWord_6999 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 6999) = g32p_row31_cosetRepresentatives 6999 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_6999 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 6999) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 6999))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 6999)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_6999 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 6999) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 6999))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 6999)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7000 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7000) = g32p_row31_cosetRepresentatives 7000 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7000 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7000) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7000))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7000)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7000 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7000) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7000))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7000)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7001 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7001) = g32p_row31_cosetRepresentatives 7001 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7001 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7001) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7001))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7001)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7001 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7001) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7001))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7001)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7002 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7002) = g32p_row31_cosetRepresentatives 7002 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7002 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7002) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7002))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7002)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7002 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7002) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7002))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7002)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7003 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7003) = g32p_row31_cosetRepresentatives 7003 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7003 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7003) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7003))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7003)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7003 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7003) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7003))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7003)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7004 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7004) = g32p_row31_cosetRepresentatives 7004 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7004 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7004) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7004))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7004)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7004 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7004) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7004))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7004)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7005 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7005) = g32p_row31_cosetRepresentatives 7005 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7005 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7005) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7005))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7005)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7005 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7005) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7005))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7005)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7006 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7006) = g32p_row31_cosetRepresentatives 7006 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7006 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7006) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7006))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7006)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7006 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7006) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7006))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7006)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7007 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7007) = g32p_row31_cosetRepresentatives 7007 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7007 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7007) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7007))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7007)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7007 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7007) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7007))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7007)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0437 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 437 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 437 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_6992
  · exact g32p_row31_cosetWord_6993
  · exact g32p_row31_cosetWord_6994
  · exact g32p_row31_cosetWord_6995
  · exact g32p_row31_cosetWord_6996
  · exact g32p_row31_cosetWord_6997
  · exact g32p_row31_cosetWord_6998
  · exact g32p_row31_cosetWord_6999
  · exact g32p_row31_cosetWord_7000
  · exact g32p_row31_cosetWord_7001
  · exact g32p_row31_cosetWord_7002
  · exact g32p_row31_cosetWord_7003
  · exact g32p_row31_cosetWord_7004
  · exact g32p_row31_cosetWord_7005
  · exact g32p_row31_cosetWord_7006
  · exact g32p_row31_cosetWord_7007

theorem g32p_row31_cosetGeneratorBlock_0437 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 437 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 437 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 437 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_6992 s
  · exact g32p_row31_cosetGeneratorStep_6993 s
  · exact g32p_row31_cosetGeneratorStep_6994 s
  · exact g32p_row31_cosetGeneratorStep_6995 s
  · exact g32p_row31_cosetGeneratorStep_6996 s
  · exact g32p_row31_cosetGeneratorStep_6997 s
  · exact g32p_row31_cosetGeneratorStep_6998 s
  · exact g32p_row31_cosetGeneratorStep_6999 s
  · exact g32p_row31_cosetGeneratorStep_7000 s
  · exact g32p_row31_cosetGeneratorStep_7001 s
  · exact g32p_row31_cosetGeneratorStep_7002 s
  · exact g32p_row31_cosetGeneratorStep_7003 s
  · exact g32p_row31_cosetGeneratorStep_7004 s
  · exact g32p_row31_cosetGeneratorStep_7005 s
  · exact g32p_row31_cosetGeneratorStep_7006 s
  · exact g32p_row31_cosetGeneratorStep_7007 s

theorem g32p_row31_cosetBranchBlock_0437 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 437 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 437 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 437 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_6992 s
  · exact g32p_row31_cosetBranchStep_6993 s
  · exact g32p_row31_cosetBranchStep_6994 s
  · exact g32p_row31_cosetBranchStep_6995 s
  · exact g32p_row31_cosetBranchStep_6996 s
  · exact g32p_row31_cosetBranchStep_6997 s
  · exact g32p_row31_cosetBranchStep_6998 s
  · exact g32p_row31_cosetBranchStep_6999 s
  · exact g32p_row31_cosetBranchStep_7000 s
  · exact g32p_row31_cosetBranchStep_7001 s
  · exact g32p_row31_cosetBranchStep_7002 s
  · exact g32p_row31_cosetBranchStep_7003 s
  · exact g32p_row31_cosetBranchStep_7004 s
  · exact g32p_row31_cosetBranchStep_7005 s
  · exact g32p_row31_cosetBranchStep_7006 s
  · exact g32p_row31_cosetBranchStep_7007 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7008 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7008) = g32p_row31_cosetRepresentatives 7008 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7008 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7008) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7008))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7008)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7008 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7008) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7008))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7008)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7009 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7009) = g32p_row31_cosetRepresentatives 7009 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7009 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7009) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7009))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7009)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7009 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7009) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7009))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7009)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7010 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7010) = g32p_row31_cosetRepresentatives 7010 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7010 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7010) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7010))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7010)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7010 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7010) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7010))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7010)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7011 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7011) = g32p_row31_cosetRepresentatives 7011 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7011 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7011) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7011))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7011)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7011 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7011) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7011))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7011)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7012 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7012) = g32p_row31_cosetRepresentatives 7012 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7012 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7012) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7012))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7012)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7012 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7012) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7012))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7012)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7013 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7013) = g32p_row31_cosetRepresentatives 7013 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7013 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7013) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7013))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7013)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7013 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7013) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7013))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7013)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7014 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7014) = g32p_row31_cosetRepresentatives 7014 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7014 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7014) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7014))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7014)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7014 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7014) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7014))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7014)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7015 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7015) = g32p_row31_cosetRepresentatives 7015 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7015 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7015) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7015))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7015)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7015 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7015) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7015))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7015)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7016 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7016) = g32p_row31_cosetRepresentatives 7016 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7016 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7016) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7016))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7016)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7016 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7016) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7016))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7016)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7017 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7017) = g32p_row31_cosetRepresentatives 7017 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7017 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7017) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7017))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7017)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7017 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7017) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7017))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7017)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7018 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7018) = g32p_row31_cosetRepresentatives 7018 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7018 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7018) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7018))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7018)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7018 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7018) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7018))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7018)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7019 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7019) = g32p_row31_cosetRepresentatives 7019 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7019 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7019) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7019))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7019)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7019 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7019) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7019))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7019)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7020 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7020) = g32p_row31_cosetRepresentatives 7020 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7020 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7020) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7020))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7020)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7020 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7020) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7020))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7020)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7021 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7021) = g32p_row31_cosetRepresentatives 7021 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7021 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7021) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7021))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7021)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7021 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7021) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7021))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7021)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7022 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7022) = g32p_row31_cosetRepresentatives 7022 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7022 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7022) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7022))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7022)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7022 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7022) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7022))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7022)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7023 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7023) = g32p_row31_cosetRepresentatives 7023 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7023 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7023) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7023))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7023)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7023 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7023) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7023))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7023)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0438 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 438 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 438 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7008
  · exact g32p_row31_cosetWord_7009
  · exact g32p_row31_cosetWord_7010
  · exact g32p_row31_cosetWord_7011
  · exact g32p_row31_cosetWord_7012
  · exact g32p_row31_cosetWord_7013
  · exact g32p_row31_cosetWord_7014
  · exact g32p_row31_cosetWord_7015
  · exact g32p_row31_cosetWord_7016
  · exact g32p_row31_cosetWord_7017
  · exact g32p_row31_cosetWord_7018
  · exact g32p_row31_cosetWord_7019
  · exact g32p_row31_cosetWord_7020
  · exact g32p_row31_cosetWord_7021
  · exact g32p_row31_cosetWord_7022
  · exact g32p_row31_cosetWord_7023

theorem g32p_row31_cosetGeneratorBlock_0438 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 438 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 438 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 438 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7008 s
  · exact g32p_row31_cosetGeneratorStep_7009 s
  · exact g32p_row31_cosetGeneratorStep_7010 s
  · exact g32p_row31_cosetGeneratorStep_7011 s
  · exact g32p_row31_cosetGeneratorStep_7012 s
  · exact g32p_row31_cosetGeneratorStep_7013 s
  · exact g32p_row31_cosetGeneratorStep_7014 s
  · exact g32p_row31_cosetGeneratorStep_7015 s
  · exact g32p_row31_cosetGeneratorStep_7016 s
  · exact g32p_row31_cosetGeneratorStep_7017 s
  · exact g32p_row31_cosetGeneratorStep_7018 s
  · exact g32p_row31_cosetGeneratorStep_7019 s
  · exact g32p_row31_cosetGeneratorStep_7020 s
  · exact g32p_row31_cosetGeneratorStep_7021 s
  · exact g32p_row31_cosetGeneratorStep_7022 s
  · exact g32p_row31_cosetGeneratorStep_7023 s

theorem g32p_row31_cosetBranchBlock_0438 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 438 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 438 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 438 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7008 s
  · exact g32p_row31_cosetBranchStep_7009 s
  · exact g32p_row31_cosetBranchStep_7010 s
  · exact g32p_row31_cosetBranchStep_7011 s
  · exact g32p_row31_cosetBranchStep_7012 s
  · exact g32p_row31_cosetBranchStep_7013 s
  · exact g32p_row31_cosetBranchStep_7014 s
  · exact g32p_row31_cosetBranchStep_7015 s
  · exact g32p_row31_cosetBranchStep_7016 s
  · exact g32p_row31_cosetBranchStep_7017 s
  · exact g32p_row31_cosetBranchStep_7018 s
  · exact g32p_row31_cosetBranchStep_7019 s
  · exact g32p_row31_cosetBranchStep_7020 s
  · exact g32p_row31_cosetBranchStep_7021 s
  · exact g32p_row31_cosetBranchStep_7022 s
  · exact g32p_row31_cosetBranchStep_7023 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7024 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7024) = g32p_row31_cosetRepresentatives 7024 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7024 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7024) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7024))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7024)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7024 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7024) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7024))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7024)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7025 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7025) = g32p_row31_cosetRepresentatives 7025 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7025 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7025) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7025))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7025)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7025 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7025) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7025))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7025)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7026 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7026) = g32p_row31_cosetRepresentatives 7026 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7026 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7026) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7026))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7026)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7026 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7026) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7026))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7026)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7027 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7027) = g32p_row31_cosetRepresentatives 7027 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7027 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7027) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7027))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7027)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7027 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7027) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7027))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7027)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7028 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7028) = g32p_row31_cosetRepresentatives 7028 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7028 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7028) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7028))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7028)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7028 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7028) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7028))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7028)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7029 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7029) = g32p_row31_cosetRepresentatives 7029 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7029 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7029) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7029))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7029)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7029 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7029) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7029))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7029)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7030 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7030) = g32p_row31_cosetRepresentatives 7030 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7030 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7030) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7030))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7030)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7030 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7030) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7030))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7030)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7031 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7031) = g32p_row31_cosetRepresentatives 7031 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7031 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7031) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7031))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7031)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7031 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7031) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7031))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7031)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7032 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7032) = g32p_row31_cosetRepresentatives 7032 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7032 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7032) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7032))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7032)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7032 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7032) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7032))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7032)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7033 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7033) = g32p_row31_cosetRepresentatives 7033 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7033 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7033) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7033))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7033)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7033 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7033) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7033))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7033)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7034 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7034) = g32p_row31_cosetRepresentatives 7034 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7034 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7034) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7034))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7034)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7034 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7034) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7034))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7034)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7035 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7035) = g32p_row31_cosetRepresentatives 7035 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7035 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7035) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7035))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7035)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7035 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7035) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7035))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7035)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7036 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7036) = g32p_row31_cosetRepresentatives 7036 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7036 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7036) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7036))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7036)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7036 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7036) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7036))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7036)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7037 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7037) = g32p_row31_cosetRepresentatives 7037 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7037 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7037) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7037))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7037)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7037 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7037) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7037))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7037)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7038 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7038) = g32p_row31_cosetRepresentatives 7038 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7038 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7038) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7038))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7038)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7038 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7038) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7038))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7038)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7039 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7039) = g32p_row31_cosetRepresentatives 7039 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7039 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7039) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7039))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7039)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7039 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7039) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7039))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7039)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0439 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 439 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 439 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7024
  · exact g32p_row31_cosetWord_7025
  · exact g32p_row31_cosetWord_7026
  · exact g32p_row31_cosetWord_7027
  · exact g32p_row31_cosetWord_7028
  · exact g32p_row31_cosetWord_7029
  · exact g32p_row31_cosetWord_7030
  · exact g32p_row31_cosetWord_7031
  · exact g32p_row31_cosetWord_7032
  · exact g32p_row31_cosetWord_7033
  · exact g32p_row31_cosetWord_7034
  · exact g32p_row31_cosetWord_7035
  · exact g32p_row31_cosetWord_7036
  · exact g32p_row31_cosetWord_7037
  · exact g32p_row31_cosetWord_7038
  · exact g32p_row31_cosetWord_7039

theorem g32p_row31_cosetGeneratorBlock_0439 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 439 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 439 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 439 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7024 s
  · exact g32p_row31_cosetGeneratorStep_7025 s
  · exact g32p_row31_cosetGeneratorStep_7026 s
  · exact g32p_row31_cosetGeneratorStep_7027 s
  · exact g32p_row31_cosetGeneratorStep_7028 s
  · exact g32p_row31_cosetGeneratorStep_7029 s
  · exact g32p_row31_cosetGeneratorStep_7030 s
  · exact g32p_row31_cosetGeneratorStep_7031 s
  · exact g32p_row31_cosetGeneratorStep_7032 s
  · exact g32p_row31_cosetGeneratorStep_7033 s
  · exact g32p_row31_cosetGeneratorStep_7034 s
  · exact g32p_row31_cosetGeneratorStep_7035 s
  · exact g32p_row31_cosetGeneratorStep_7036 s
  · exact g32p_row31_cosetGeneratorStep_7037 s
  · exact g32p_row31_cosetGeneratorStep_7038 s
  · exact g32p_row31_cosetGeneratorStep_7039 s

theorem g32p_row31_cosetBranchBlock_0439 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 439 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 439 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 439 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7024 s
  · exact g32p_row31_cosetBranchStep_7025 s
  · exact g32p_row31_cosetBranchStep_7026 s
  · exact g32p_row31_cosetBranchStep_7027 s
  · exact g32p_row31_cosetBranchStep_7028 s
  · exact g32p_row31_cosetBranchStep_7029 s
  · exact g32p_row31_cosetBranchStep_7030 s
  · exact g32p_row31_cosetBranchStep_7031 s
  · exact g32p_row31_cosetBranchStep_7032 s
  · exact g32p_row31_cosetBranchStep_7033 s
  · exact g32p_row31_cosetBranchStep_7034 s
  · exact g32p_row31_cosetBranchStep_7035 s
  · exact g32p_row31_cosetBranchStep_7036 s
  · exact g32p_row31_cosetBranchStep_7037 s
  · exact g32p_row31_cosetBranchStep_7038 s
  · exact g32p_row31_cosetBranchStep_7039 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7040 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7040) = g32p_row31_cosetRepresentatives 7040 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7040 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7040) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7040))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7040)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7040 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7040) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7040))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7040)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7041 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7041) = g32p_row31_cosetRepresentatives 7041 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7041 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7041) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7041))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7041)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7041 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7041) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7041))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7041)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7042 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7042) = g32p_row31_cosetRepresentatives 7042 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7042 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7042) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7042))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7042)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7042 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7042) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7042))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7042)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7043 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7043) = g32p_row31_cosetRepresentatives 7043 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7043 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7043) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7043))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7043)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7043 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7043) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7043))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7043)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7044 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7044) = g32p_row31_cosetRepresentatives 7044 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7044 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7044) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7044))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7044)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7044 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7044) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7044))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7044)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7045 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7045) = g32p_row31_cosetRepresentatives 7045 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7045 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7045) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7045))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7045)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7045 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7045) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7045))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7045)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7046 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7046) = g32p_row31_cosetRepresentatives 7046 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7046 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7046) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7046))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7046)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7046 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7046) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7046))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7046)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7047 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7047) = g32p_row31_cosetRepresentatives 7047 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7047 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7047) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7047))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7047)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7047 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7047) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7047))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7047)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7048 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7048) = g32p_row31_cosetRepresentatives 7048 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7048 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7048) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7048))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7048)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7048 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7048) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7048))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7048)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7049 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7049) = g32p_row31_cosetRepresentatives 7049 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7049 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7049) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7049))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7049)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7049 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7049) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7049))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7049)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7050 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7050) = g32p_row31_cosetRepresentatives 7050 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7050 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7050) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7050))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7050)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7050 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7050) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7050))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7050)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7051 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7051) = g32p_row31_cosetRepresentatives 7051 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7051 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7051) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7051))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7051)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7051 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7051) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7051))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7051)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7052 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7052) = g32p_row31_cosetRepresentatives 7052 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7052 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7052) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7052))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7052)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7052 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7052) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7052))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7052)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7053 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7053) = g32p_row31_cosetRepresentatives 7053 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7053 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7053) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7053))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7053)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7053 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7053) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7053))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7053)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7054 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7054) = g32p_row31_cosetRepresentatives 7054 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7054 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7054) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7054))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7054)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7054 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7054) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7054))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7054)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7055 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7055) = g32p_row31_cosetRepresentatives 7055 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7055 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7055) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7055))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7055)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7055 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7055) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7055))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7055)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0440 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 440 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 440 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7040
  · exact g32p_row31_cosetWord_7041
  · exact g32p_row31_cosetWord_7042
  · exact g32p_row31_cosetWord_7043
  · exact g32p_row31_cosetWord_7044
  · exact g32p_row31_cosetWord_7045
  · exact g32p_row31_cosetWord_7046
  · exact g32p_row31_cosetWord_7047
  · exact g32p_row31_cosetWord_7048
  · exact g32p_row31_cosetWord_7049
  · exact g32p_row31_cosetWord_7050
  · exact g32p_row31_cosetWord_7051
  · exact g32p_row31_cosetWord_7052
  · exact g32p_row31_cosetWord_7053
  · exact g32p_row31_cosetWord_7054
  · exact g32p_row31_cosetWord_7055

theorem g32p_row31_cosetGeneratorBlock_0440 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 440 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 440 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 440 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7040 s
  · exact g32p_row31_cosetGeneratorStep_7041 s
  · exact g32p_row31_cosetGeneratorStep_7042 s
  · exact g32p_row31_cosetGeneratorStep_7043 s
  · exact g32p_row31_cosetGeneratorStep_7044 s
  · exact g32p_row31_cosetGeneratorStep_7045 s
  · exact g32p_row31_cosetGeneratorStep_7046 s
  · exact g32p_row31_cosetGeneratorStep_7047 s
  · exact g32p_row31_cosetGeneratorStep_7048 s
  · exact g32p_row31_cosetGeneratorStep_7049 s
  · exact g32p_row31_cosetGeneratorStep_7050 s
  · exact g32p_row31_cosetGeneratorStep_7051 s
  · exact g32p_row31_cosetGeneratorStep_7052 s
  · exact g32p_row31_cosetGeneratorStep_7053 s
  · exact g32p_row31_cosetGeneratorStep_7054 s
  · exact g32p_row31_cosetGeneratorStep_7055 s

theorem g32p_row31_cosetBranchBlock_0440 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 440 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 440 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 440 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7040 s
  · exact g32p_row31_cosetBranchStep_7041 s
  · exact g32p_row31_cosetBranchStep_7042 s
  · exact g32p_row31_cosetBranchStep_7043 s
  · exact g32p_row31_cosetBranchStep_7044 s
  · exact g32p_row31_cosetBranchStep_7045 s
  · exact g32p_row31_cosetBranchStep_7046 s
  · exact g32p_row31_cosetBranchStep_7047 s
  · exact g32p_row31_cosetBranchStep_7048 s
  · exact g32p_row31_cosetBranchStep_7049 s
  · exact g32p_row31_cosetBranchStep_7050 s
  · exact g32p_row31_cosetBranchStep_7051 s
  · exact g32p_row31_cosetBranchStep_7052 s
  · exact g32p_row31_cosetBranchStep_7053 s
  · exact g32p_row31_cosetBranchStep_7054 s
  · exact g32p_row31_cosetBranchStep_7055 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7056 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7056) = g32p_row31_cosetRepresentatives 7056 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7056 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7056) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7056))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7056)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7056 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7056) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7056))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7056)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7057 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7057) = g32p_row31_cosetRepresentatives 7057 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7057 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7057) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7057))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7057)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7057 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7057) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7057))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7057)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7058 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7058) = g32p_row31_cosetRepresentatives 7058 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7058 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7058) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7058))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7058)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7058 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7058) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7058))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7058)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7059 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7059) = g32p_row31_cosetRepresentatives 7059 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7059 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7059) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7059))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7059)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7059 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7059) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7059))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7059)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7060 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7060) = g32p_row31_cosetRepresentatives 7060 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7060 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7060) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7060))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7060)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7060 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7060) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7060))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7060)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7061 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7061) = g32p_row31_cosetRepresentatives 7061 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7061 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7061) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7061))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7061)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7061 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7061) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7061))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7061)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7062 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7062) = g32p_row31_cosetRepresentatives 7062 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7062 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7062) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7062))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7062)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7062 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7062) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7062))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7062)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7063 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7063) = g32p_row31_cosetRepresentatives 7063 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7063 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7063) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7063))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7063)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7063 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7063) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7063))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7063)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7064 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7064) = g32p_row31_cosetRepresentatives 7064 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7064 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7064) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7064))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7064)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7064 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7064) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7064))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7064)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7065 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7065) = g32p_row31_cosetRepresentatives 7065 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7065 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7065) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7065))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7065)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7065 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7065) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7065))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7065)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7066 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7066) = g32p_row31_cosetRepresentatives 7066 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7066 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7066) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7066))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7066)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7066 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7066) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7066))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7066)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7067 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7067) = g32p_row31_cosetRepresentatives 7067 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7067 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7067) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7067))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7067)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7067 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7067) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7067))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7067)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7068 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7068) = g32p_row31_cosetRepresentatives 7068 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7068 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7068) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7068))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7068)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7068 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7068) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7068))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7068)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7069 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7069) = g32p_row31_cosetRepresentatives 7069 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7069 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7069) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7069))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7069)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7069 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7069) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7069))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7069)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7070 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7070) = g32p_row31_cosetRepresentatives 7070 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7070 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7070) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7070))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7070)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7070 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7070) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7070))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7070)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7071 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7071) = g32p_row31_cosetRepresentatives 7071 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7071 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7071) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7071))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7071)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7071 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7071) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7071))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7071)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0441 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 441 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 441 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7056
  · exact g32p_row31_cosetWord_7057
  · exact g32p_row31_cosetWord_7058
  · exact g32p_row31_cosetWord_7059
  · exact g32p_row31_cosetWord_7060
  · exact g32p_row31_cosetWord_7061
  · exact g32p_row31_cosetWord_7062
  · exact g32p_row31_cosetWord_7063
  · exact g32p_row31_cosetWord_7064
  · exact g32p_row31_cosetWord_7065
  · exact g32p_row31_cosetWord_7066
  · exact g32p_row31_cosetWord_7067
  · exact g32p_row31_cosetWord_7068
  · exact g32p_row31_cosetWord_7069
  · exact g32p_row31_cosetWord_7070
  · exact g32p_row31_cosetWord_7071

theorem g32p_row31_cosetGeneratorBlock_0441 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 441 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 441 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 441 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7056 s
  · exact g32p_row31_cosetGeneratorStep_7057 s
  · exact g32p_row31_cosetGeneratorStep_7058 s
  · exact g32p_row31_cosetGeneratorStep_7059 s
  · exact g32p_row31_cosetGeneratorStep_7060 s
  · exact g32p_row31_cosetGeneratorStep_7061 s
  · exact g32p_row31_cosetGeneratorStep_7062 s
  · exact g32p_row31_cosetGeneratorStep_7063 s
  · exact g32p_row31_cosetGeneratorStep_7064 s
  · exact g32p_row31_cosetGeneratorStep_7065 s
  · exact g32p_row31_cosetGeneratorStep_7066 s
  · exact g32p_row31_cosetGeneratorStep_7067 s
  · exact g32p_row31_cosetGeneratorStep_7068 s
  · exact g32p_row31_cosetGeneratorStep_7069 s
  · exact g32p_row31_cosetGeneratorStep_7070 s
  · exact g32p_row31_cosetGeneratorStep_7071 s

theorem g32p_row31_cosetBranchBlock_0441 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 441 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 441 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 441 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7056 s
  · exact g32p_row31_cosetBranchStep_7057 s
  · exact g32p_row31_cosetBranchStep_7058 s
  · exact g32p_row31_cosetBranchStep_7059 s
  · exact g32p_row31_cosetBranchStep_7060 s
  · exact g32p_row31_cosetBranchStep_7061 s
  · exact g32p_row31_cosetBranchStep_7062 s
  · exact g32p_row31_cosetBranchStep_7063 s
  · exact g32p_row31_cosetBranchStep_7064 s
  · exact g32p_row31_cosetBranchStep_7065 s
  · exact g32p_row31_cosetBranchStep_7066 s
  · exact g32p_row31_cosetBranchStep_7067 s
  · exact g32p_row31_cosetBranchStep_7068 s
  · exact g32p_row31_cosetBranchStep_7069 s
  · exact g32p_row31_cosetBranchStep_7070 s
  · exact g32p_row31_cosetBranchStep_7071 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7072 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7072) = g32p_row31_cosetRepresentatives 7072 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7072 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7072) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7072))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7072)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7072 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7072) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7072))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7072)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7073 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7073) = g32p_row31_cosetRepresentatives 7073 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7073 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7073) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7073))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7073)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7073 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7073) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7073))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7073)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7074 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7074) = g32p_row31_cosetRepresentatives 7074 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7074 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7074) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7074))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7074)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7074 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7074) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7074))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7074)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7075 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7075) = g32p_row31_cosetRepresentatives 7075 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7075 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7075) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7075))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7075)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7075 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7075) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7075))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7075)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7076 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7076) = g32p_row31_cosetRepresentatives 7076 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7076 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7076) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7076))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7076)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7076 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7076) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7076))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7076)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7077 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7077) = g32p_row31_cosetRepresentatives 7077 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7077 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7077) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7077))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7077)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7077 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7077) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7077))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7077)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7078 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7078) = g32p_row31_cosetRepresentatives 7078 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7078 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7078) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7078))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7078)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7078 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7078) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7078))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7078)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7079 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7079) = g32p_row31_cosetRepresentatives 7079 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7079 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7079) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7079))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7079)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7079 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7079) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7079))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7079)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7080 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7080) = g32p_row31_cosetRepresentatives 7080 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7080 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7080) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7080))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7080)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7080 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7080) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7080))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7080)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7081 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7081) = g32p_row31_cosetRepresentatives 7081 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7081 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7081) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7081))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7081)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7081 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7081) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7081))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7081)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7082 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7082) = g32p_row31_cosetRepresentatives 7082 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7082 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7082) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7082))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7082)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7082 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7082) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7082))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7082)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7083 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7083) = g32p_row31_cosetRepresentatives 7083 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7083 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7083) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7083))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7083)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7083 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7083) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7083))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7083)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7084 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7084) = g32p_row31_cosetRepresentatives 7084 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7084 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7084) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7084))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7084)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7084 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7084) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7084))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7084)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7085 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7085) = g32p_row31_cosetRepresentatives 7085 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7085 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7085) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7085))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7085)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7085 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7085) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7085))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7085)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7086 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7086) = g32p_row31_cosetRepresentatives 7086 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7086 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7086) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7086))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7086)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7086 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7086) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7086))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7086)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7087 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7087) = g32p_row31_cosetRepresentatives 7087 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7087 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7087) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7087))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7087)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7087 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7087) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7087))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7087)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0442 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 442 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 442 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7072
  · exact g32p_row31_cosetWord_7073
  · exact g32p_row31_cosetWord_7074
  · exact g32p_row31_cosetWord_7075
  · exact g32p_row31_cosetWord_7076
  · exact g32p_row31_cosetWord_7077
  · exact g32p_row31_cosetWord_7078
  · exact g32p_row31_cosetWord_7079
  · exact g32p_row31_cosetWord_7080
  · exact g32p_row31_cosetWord_7081
  · exact g32p_row31_cosetWord_7082
  · exact g32p_row31_cosetWord_7083
  · exact g32p_row31_cosetWord_7084
  · exact g32p_row31_cosetWord_7085
  · exact g32p_row31_cosetWord_7086
  · exact g32p_row31_cosetWord_7087

theorem g32p_row31_cosetGeneratorBlock_0442 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 442 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 442 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 442 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7072 s
  · exact g32p_row31_cosetGeneratorStep_7073 s
  · exact g32p_row31_cosetGeneratorStep_7074 s
  · exact g32p_row31_cosetGeneratorStep_7075 s
  · exact g32p_row31_cosetGeneratorStep_7076 s
  · exact g32p_row31_cosetGeneratorStep_7077 s
  · exact g32p_row31_cosetGeneratorStep_7078 s
  · exact g32p_row31_cosetGeneratorStep_7079 s
  · exact g32p_row31_cosetGeneratorStep_7080 s
  · exact g32p_row31_cosetGeneratorStep_7081 s
  · exact g32p_row31_cosetGeneratorStep_7082 s
  · exact g32p_row31_cosetGeneratorStep_7083 s
  · exact g32p_row31_cosetGeneratorStep_7084 s
  · exact g32p_row31_cosetGeneratorStep_7085 s
  · exact g32p_row31_cosetGeneratorStep_7086 s
  · exact g32p_row31_cosetGeneratorStep_7087 s

theorem g32p_row31_cosetBranchBlock_0442 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 442 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 442 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 442 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7072 s
  · exact g32p_row31_cosetBranchStep_7073 s
  · exact g32p_row31_cosetBranchStep_7074 s
  · exact g32p_row31_cosetBranchStep_7075 s
  · exact g32p_row31_cosetBranchStep_7076 s
  · exact g32p_row31_cosetBranchStep_7077 s
  · exact g32p_row31_cosetBranchStep_7078 s
  · exact g32p_row31_cosetBranchStep_7079 s
  · exact g32p_row31_cosetBranchStep_7080 s
  · exact g32p_row31_cosetBranchStep_7081 s
  · exact g32p_row31_cosetBranchStep_7082 s
  · exact g32p_row31_cosetBranchStep_7083 s
  · exact g32p_row31_cosetBranchStep_7084 s
  · exact g32p_row31_cosetBranchStep_7085 s
  · exact g32p_row31_cosetBranchStep_7086 s
  · exact g32p_row31_cosetBranchStep_7087 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7088 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7088) = g32p_row31_cosetRepresentatives 7088 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7088 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7088) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7088))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7088)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7088 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7088) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7088))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7088)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7089 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7089) = g32p_row31_cosetRepresentatives 7089 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7089 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7089) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7089))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7089)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7089 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7089) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7089))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7089)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7090 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7090) = g32p_row31_cosetRepresentatives 7090 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7090 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7090) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7090))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7090)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7090 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7090) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7090))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7090)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7091 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7091) = g32p_row31_cosetRepresentatives 7091 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7091 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7091) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7091))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7091)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7091 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7091) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7091))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7091)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7092 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7092) = g32p_row31_cosetRepresentatives 7092 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7092 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7092) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7092))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7092)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7092 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7092) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7092))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7092)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7093 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7093) = g32p_row31_cosetRepresentatives 7093 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7093 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7093) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7093))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7093)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7093 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7093) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7093))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7093)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7094 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7094) = g32p_row31_cosetRepresentatives 7094 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7094 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7094) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7094))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7094)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7094 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7094) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7094))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7094)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7095 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7095) = g32p_row31_cosetRepresentatives 7095 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7095 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7095) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7095))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7095)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7095 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7095) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7095))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7095)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7096 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7096) = g32p_row31_cosetRepresentatives 7096 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7096 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7096) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7096))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7096)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7096 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7096) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7096))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7096)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7097 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7097) = g32p_row31_cosetRepresentatives 7097 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7097 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7097) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7097))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7097)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7097 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7097) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7097))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7097)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7098 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7098) = g32p_row31_cosetRepresentatives 7098 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7098 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7098) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7098))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7098)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7098 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7098) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7098))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7098)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7099 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7099) = g32p_row31_cosetRepresentatives 7099 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7099 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7099) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7099))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7099)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7099 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7099) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7099))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7099)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7100 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7100) = g32p_row31_cosetRepresentatives 7100 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7100 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7100) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7100))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7100)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7100 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7100) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7100))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7100)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7101 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7101) = g32p_row31_cosetRepresentatives 7101 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7101 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7101) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7101))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7101)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7101 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7101) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7101))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7101)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7102 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7102) = g32p_row31_cosetRepresentatives 7102 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7102 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7102) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7102))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7102)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7102 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7102) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7102))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7102)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7103 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7103) = g32p_row31_cosetRepresentatives 7103 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7103 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7103) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7103))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7103)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7103 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7103) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7103))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7103)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0443 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 443 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 443 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7088
  · exact g32p_row31_cosetWord_7089
  · exact g32p_row31_cosetWord_7090
  · exact g32p_row31_cosetWord_7091
  · exact g32p_row31_cosetWord_7092
  · exact g32p_row31_cosetWord_7093
  · exact g32p_row31_cosetWord_7094
  · exact g32p_row31_cosetWord_7095
  · exact g32p_row31_cosetWord_7096
  · exact g32p_row31_cosetWord_7097
  · exact g32p_row31_cosetWord_7098
  · exact g32p_row31_cosetWord_7099
  · exact g32p_row31_cosetWord_7100
  · exact g32p_row31_cosetWord_7101
  · exact g32p_row31_cosetWord_7102
  · exact g32p_row31_cosetWord_7103

theorem g32p_row31_cosetGeneratorBlock_0443 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 443 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 443 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 443 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7088 s
  · exact g32p_row31_cosetGeneratorStep_7089 s
  · exact g32p_row31_cosetGeneratorStep_7090 s
  · exact g32p_row31_cosetGeneratorStep_7091 s
  · exact g32p_row31_cosetGeneratorStep_7092 s
  · exact g32p_row31_cosetGeneratorStep_7093 s
  · exact g32p_row31_cosetGeneratorStep_7094 s
  · exact g32p_row31_cosetGeneratorStep_7095 s
  · exact g32p_row31_cosetGeneratorStep_7096 s
  · exact g32p_row31_cosetGeneratorStep_7097 s
  · exact g32p_row31_cosetGeneratorStep_7098 s
  · exact g32p_row31_cosetGeneratorStep_7099 s
  · exact g32p_row31_cosetGeneratorStep_7100 s
  · exact g32p_row31_cosetGeneratorStep_7101 s
  · exact g32p_row31_cosetGeneratorStep_7102 s
  · exact g32p_row31_cosetGeneratorStep_7103 s

theorem g32p_row31_cosetBranchBlock_0443 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 443 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 443 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 443 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7088 s
  · exact g32p_row31_cosetBranchStep_7089 s
  · exact g32p_row31_cosetBranchStep_7090 s
  · exact g32p_row31_cosetBranchStep_7091 s
  · exact g32p_row31_cosetBranchStep_7092 s
  · exact g32p_row31_cosetBranchStep_7093 s
  · exact g32p_row31_cosetBranchStep_7094 s
  · exact g32p_row31_cosetBranchStep_7095 s
  · exact g32p_row31_cosetBranchStep_7096 s
  · exact g32p_row31_cosetBranchStep_7097 s
  · exact g32p_row31_cosetBranchStep_7098 s
  · exact g32p_row31_cosetBranchStep_7099 s
  · exact g32p_row31_cosetBranchStep_7100 s
  · exact g32p_row31_cosetBranchStep_7101 s
  · exact g32p_row31_cosetBranchStep_7102 s
  · exact g32p_row31_cosetBranchStep_7103 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7104 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7104) = g32p_row31_cosetRepresentatives 7104 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7104 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7104) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7104))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7104)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7104 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7104) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7104))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7104)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7105 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7105) = g32p_row31_cosetRepresentatives 7105 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7105 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7105) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7105))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7105)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7105 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7105) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7105))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7105)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7106 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7106) = g32p_row31_cosetRepresentatives 7106 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7106 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7106) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7106))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7106)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7106 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7106) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7106))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7106)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7107 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7107) = g32p_row31_cosetRepresentatives 7107 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7107 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7107) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7107))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7107)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7107 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7107) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7107))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7107)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7108 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7108) = g32p_row31_cosetRepresentatives 7108 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7108 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7108) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7108))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7108)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7108 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7108) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7108))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7108)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7109 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7109) = g32p_row31_cosetRepresentatives 7109 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7109 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7109) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7109))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7109)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7109 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7109) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7109))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7109)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7110 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7110) = g32p_row31_cosetRepresentatives 7110 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7110 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7110) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7110))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7110)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7110 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7110) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7110))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7110)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7111 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7111) = g32p_row31_cosetRepresentatives 7111 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7111 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7111) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7111))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7111)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7111 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7111) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7111))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7111)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7112 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7112) = g32p_row31_cosetRepresentatives 7112 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7112 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7112) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7112))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7112)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7112 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7112) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7112))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7112)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7113 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7113) = g32p_row31_cosetRepresentatives 7113 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7113 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7113) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7113))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7113)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7113 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7113) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7113))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7113)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7114 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7114) = g32p_row31_cosetRepresentatives 7114 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7114 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7114) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7114))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7114)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7114 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7114) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7114))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7114)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7115 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7115) = g32p_row31_cosetRepresentatives 7115 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7115 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7115) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7115))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7115)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7115 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7115) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7115))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7115)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7116 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7116) = g32p_row31_cosetRepresentatives 7116 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7116 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7116) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7116))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7116)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7116 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7116) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7116))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7116)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7117 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7117) = g32p_row31_cosetRepresentatives 7117 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7117 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7117) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7117))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7117)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7117 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7117) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7117))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7117)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7118 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7118) = g32p_row31_cosetRepresentatives 7118 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7118 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7118) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7118))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7118)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7118 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7118) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7118))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7118)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7119 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7119) = g32p_row31_cosetRepresentatives 7119 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7119 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7119) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7119))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7119)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7119 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7119) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7119))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7119)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0444 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 444 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 444 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7104
  · exact g32p_row31_cosetWord_7105
  · exact g32p_row31_cosetWord_7106
  · exact g32p_row31_cosetWord_7107
  · exact g32p_row31_cosetWord_7108
  · exact g32p_row31_cosetWord_7109
  · exact g32p_row31_cosetWord_7110
  · exact g32p_row31_cosetWord_7111
  · exact g32p_row31_cosetWord_7112
  · exact g32p_row31_cosetWord_7113
  · exact g32p_row31_cosetWord_7114
  · exact g32p_row31_cosetWord_7115
  · exact g32p_row31_cosetWord_7116
  · exact g32p_row31_cosetWord_7117
  · exact g32p_row31_cosetWord_7118
  · exact g32p_row31_cosetWord_7119

theorem g32p_row31_cosetGeneratorBlock_0444 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 444 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 444 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 444 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7104 s
  · exact g32p_row31_cosetGeneratorStep_7105 s
  · exact g32p_row31_cosetGeneratorStep_7106 s
  · exact g32p_row31_cosetGeneratorStep_7107 s
  · exact g32p_row31_cosetGeneratorStep_7108 s
  · exact g32p_row31_cosetGeneratorStep_7109 s
  · exact g32p_row31_cosetGeneratorStep_7110 s
  · exact g32p_row31_cosetGeneratorStep_7111 s
  · exact g32p_row31_cosetGeneratorStep_7112 s
  · exact g32p_row31_cosetGeneratorStep_7113 s
  · exact g32p_row31_cosetGeneratorStep_7114 s
  · exact g32p_row31_cosetGeneratorStep_7115 s
  · exact g32p_row31_cosetGeneratorStep_7116 s
  · exact g32p_row31_cosetGeneratorStep_7117 s
  · exact g32p_row31_cosetGeneratorStep_7118 s
  · exact g32p_row31_cosetGeneratorStep_7119 s

theorem g32p_row31_cosetBranchBlock_0444 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 444 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 444 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 444 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7104 s
  · exact g32p_row31_cosetBranchStep_7105 s
  · exact g32p_row31_cosetBranchStep_7106 s
  · exact g32p_row31_cosetBranchStep_7107 s
  · exact g32p_row31_cosetBranchStep_7108 s
  · exact g32p_row31_cosetBranchStep_7109 s
  · exact g32p_row31_cosetBranchStep_7110 s
  · exact g32p_row31_cosetBranchStep_7111 s
  · exact g32p_row31_cosetBranchStep_7112 s
  · exact g32p_row31_cosetBranchStep_7113 s
  · exact g32p_row31_cosetBranchStep_7114 s
  · exact g32p_row31_cosetBranchStep_7115 s
  · exact g32p_row31_cosetBranchStep_7116 s
  · exact g32p_row31_cosetBranchStep_7117 s
  · exact g32p_row31_cosetBranchStep_7118 s
  · exact g32p_row31_cosetBranchStep_7119 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7120 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7120) = g32p_row31_cosetRepresentatives 7120 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7120 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7120) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7120))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7120)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7120 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7120) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7120))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7120)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7121 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7121) = g32p_row31_cosetRepresentatives 7121 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7121 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7121) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7121))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7121)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7121 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7121) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7121))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7121)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7122 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7122) = g32p_row31_cosetRepresentatives 7122 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7122 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7122) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7122))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7122)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7122 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7122) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7122))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7122)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7123 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7123) = g32p_row31_cosetRepresentatives 7123 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7123 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7123) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7123))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7123)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7123 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7123) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7123))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7123)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7124 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7124) = g32p_row31_cosetRepresentatives 7124 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7124 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7124) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7124))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7124)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7124 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7124) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7124))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7124)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7125 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7125) = g32p_row31_cosetRepresentatives 7125 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7125 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7125) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7125))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7125)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7125 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7125) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7125))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7125)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7126 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7126) = g32p_row31_cosetRepresentatives 7126 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7126 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7126) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7126))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7126)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7126 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7126) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7126))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7126)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7127 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7127) = g32p_row31_cosetRepresentatives 7127 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7127 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7127) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7127))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7127)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7127 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7127) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7127))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7127)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7128 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7128) = g32p_row31_cosetRepresentatives 7128 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7128 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7128) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7128))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7128)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7128 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7128) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7128))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7128)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7129 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7129) = g32p_row31_cosetRepresentatives 7129 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7129 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7129) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7129))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7129)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7129 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7129) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7129))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7129)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7130 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7130) = g32p_row31_cosetRepresentatives 7130 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7130 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7130) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7130))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7130)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7130 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7130) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7130))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7130)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7131 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7131) = g32p_row31_cosetRepresentatives 7131 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7131 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7131) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7131))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7131)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7131 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7131) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7131))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7131)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7132 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7132) = g32p_row31_cosetRepresentatives 7132 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7132 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7132) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7132))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7132)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7132 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7132) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7132))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7132)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7133 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7133) = g32p_row31_cosetRepresentatives 7133 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7133 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7133) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7133))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7133)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7133 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7133) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7133))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7133)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7134 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7134) = g32p_row31_cosetRepresentatives 7134 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7134 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7134) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7134))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7134)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7134 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7134) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7134))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7134)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7135 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7135) = g32p_row31_cosetRepresentatives 7135 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7135 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7135) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7135))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7135)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7135 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7135) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7135))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7135)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0445 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 445 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 445 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7120
  · exact g32p_row31_cosetWord_7121
  · exact g32p_row31_cosetWord_7122
  · exact g32p_row31_cosetWord_7123
  · exact g32p_row31_cosetWord_7124
  · exact g32p_row31_cosetWord_7125
  · exact g32p_row31_cosetWord_7126
  · exact g32p_row31_cosetWord_7127
  · exact g32p_row31_cosetWord_7128
  · exact g32p_row31_cosetWord_7129
  · exact g32p_row31_cosetWord_7130
  · exact g32p_row31_cosetWord_7131
  · exact g32p_row31_cosetWord_7132
  · exact g32p_row31_cosetWord_7133
  · exact g32p_row31_cosetWord_7134
  · exact g32p_row31_cosetWord_7135

theorem g32p_row31_cosetGeneratorBlock_0445 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 445 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 445 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 445 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7120 s
  · exact g32p_row31_cosetGeneratorStep_7121 s
  · exact g32p_row31_cosetGeneratorStep_7122 s
  · exact g32p_row31_cosetGeneratorStep_7123 s
  · exact g32p_row31_cosetGeneratorStep_7124 s
  · exact g32p_row31_cosetGeneratorStep_7125 s
  · exact g32p_row31_cosetGeneratorStep_7126 s
  · exact g32p_row31_cosetGeneratorStep_7127 s
  · exact g32p_row31_cosetGeneratorStep_7128 s
  · exact g32p_row31_cosetGeneratorStep_7129 s
  · exact g32p_row31_cosetGeneratorStep_7130 s
  · exact g32p_row31_cosetGeneratorStep_7131 s
  · exact g32p_row31_cosetGeneratorStep_7132 s
  · exact g32p_row31_cosetGeneratorStep_7133 s
  · exact g32p_row31_cosetGeneratorStep_7134 s
  · exact g32p_row31_cosetGeneratorStep_7135 s

theorem g32p_row31_cosetBranchBlock_0445 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 445 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 445 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 445 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7120 s
  · exact g32p_row31_cosetBranchStep_7121 s
  · exact g32p_row31_cosetBranchStep_7122 s
  · exact g32p_row31_cosetBranchStep_7123 s
  · exact g32p_row31_cosetBranchStep_7124 s
  · exact g32p_row31_cosetBranchStep_7125 s
  · exact g32p_row31_cosetBranchStep_7126 s
  · exact g32p_row31_cosetBranchStep_7127 s
  · exact g32p_row31_cosetBranchStep_7128 s
  · exact g32p_row31_cosetBranchStep_7129 s
  · exact g32p_row31_cosetBranchStep_7130 s
  · exact g32p_row31_cosetBranchStep_7131 s
  · exact g32p_row31_cosetBranchStep_7132 s
  · exact g32p_row31_cosetBranchStep_7133 s
  · exact g32p_row31_cosetBranchStep_7134 s
  · exact g32p_row31_cosetBranchStep_7135 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7136 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7136) = g32p_row31_cosetRepresentatives 7136 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7136 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7136) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7136))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7136)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7136 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7136) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7136))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7136)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7137 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7137) = g32p_row31_cosetRepresentatives 7137 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7137 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7137) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7137))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7137)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7137 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7137) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7137))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7137)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7138 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7138) = g32p_row31_cosetRepresentatives 7138 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7138 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7138) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7138))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7138)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7138 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7138) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7138))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7138)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7139 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7139) = g32p_row31_cosetRepresentatives 7139 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7139 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7139) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7139))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7139)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7139 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7139) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7139))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7139)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7140 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7140) = g32p_row31_cosetRepresentatives 7140 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7140 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7140) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7140))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7140)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7140 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7140) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7140))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7140)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7141 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7141) = g32p_row31_cosetRepresentatives 7141 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7141 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7141) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7141))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7141)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7141 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7141) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7141))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7141)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7142 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7142) = g32p_row31_cosetRepresentatives 7142 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7142 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7142) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7142))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7142)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7142 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7142) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7142))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7142)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7143 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7143) = g32p_row31_cosetRepresentatives 7143 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7143 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7143) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7143))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7143)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7143 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7143) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7143))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7143)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7144 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7144) = g32p_row31_cosetRepresentatives 7144 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7144 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7144) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7144))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7144)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7144 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7144) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7144))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7144)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7145 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7145) = g32p_row31_cosetRepresentatives 7145 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7145 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7145) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7145))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7145)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7145 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7145) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7145))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7145)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7146 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7146) = g32p_row31_cosetRepresentatives 7146 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7146 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7146) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7146))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7146)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7146 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7146) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7146))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7146)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7147 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7147) = g32p_row31_cosetRepresentatives 7147 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7147 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7147) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7147))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7147)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7147 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7147) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7147))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7147)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7148 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7148) = g32p_row31_cosetRepresentatives 7148 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7148 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7148) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7148))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7148)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7148 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7148) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7148))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7148)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7149 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7149) = g32p_row31_cosetRepresentatives 7149 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7149 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7149) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7149))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7149)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7149 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7149) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7149))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7149)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7150 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7150) = g32p_row31_cosetRepresentatives 7150 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7150 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7150) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7150))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7150)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7150 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7150) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7150))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7150)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7151 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7151) = g32p_row31_cosetRepresentatives 7151 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7151 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7151) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7151))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7151)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7151 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7151) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7151))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7151)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0446 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 446 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 446 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7136
  · exact g32p_row31_cosetWord_7137
  · exact g32p_row31_cosetWord_7138
  · exact g32p_row31_cosetWord_7139
  · exact g32p_row31_cosetWord_7140
  · exact g32p_row31_cosetWord_7141
  · exact g32p_row31_cosetWord_7142
  · exact g32p_row31_cosetWord_7143
  · exact g32p_row31_cosetWord_7144
  · exact g32p_row31_cosetWord_7145
  · exact g32p_row31_cosetWord_7146
  · exact g32p_row31_cosetWord_7147
  · exact g32p_row31_cosetWord_7148
  · exact g32p_row31_cosetWord_7149
  · exact g32p_row31_cosetWord_7150
  · exact g32p_row31_cosetWord_7151

theorem g32p_row31_cosetGeneratorBlock_0446 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 446 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 446 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 446 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7136 s
  · exact g32p_row31_cosetGeneratorStep_7137 s
  · exact g32p_row31_cosetGeneratorStep_7138 s
  · exact g32p_row31_cosetGeneratorStep_7139 s
  · exact g32p_row31_cosetGeneratorStep_7140 s
  · exact g32p_row31_cosetGeneratorStep_7141 s
  · exact g32p_row31_cosetGeneratorStep_7142 s
  · exact g32p_row31_cosetGeneratorStep_7143 s
  · exact g32p_row31_cosetGeneratorStep_7144 s
  · exact g32p_row31_cosetGeneratorStep_7145 s
  · exact g32p_row31_cosetGeneratorStep_7146 s
  · exact g32p_row31_cosetGeneratorStep_7147 s
  · exact g32p_row31_cosetGeneratorStep_7148 s
  · exact g32p_row31_cosetGeneratorStep_7149 s
  · exact g32p_row31_cosetGeneratorStep_7150 s
  · exact g32p_row31_cosetGeneratorStep_7151 s

theorem g32p_row31_cosetBranchBlock_0446 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 446 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 446 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 446 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7136 s
  · exact g32p_row31_cosetBranchStep_7137 s
  · exact g32p_row31_cosetBranchStep_7138 s
  · exact g32p_row31_cosetBranchStep_7139 s
  · exact g32p_row31_cosetBranchStep_7140 s
  · exact g32p_row31_cosetBranchStep_7141 s
  · exact g32p_row31_cosetBranchStep_7142 s
  · exact g32p_row31_cosetBranchStep_7143 s
  · exact g32p_row31_cosetBranchStep_7144 s
  · exact g32p_row31_cosetBranchStep_7145 s
  · exact g32p_row31_cosetBranchStep_7146 s
  · exact g32p_row31_cosetBranchStep_7147 s
  · exact g32p_row31_cosetBranchStep_7148 s
  · exact g32p_row31_cosetBranchStep_7149 s
  · exact g32p_row31_cosetBranchStep_7150 s
  · exact g32p_row31_cosetBranchStep_7151 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row31_cosetWord_7152 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7152) = g32p_row31_cosetRepresentatives 7152 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7152 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7152) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7152))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7152)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7152 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7152) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7152))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7152)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7153 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7153) = g32p_row31_cosetRepresentatives 7153 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7153 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7153) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7153))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7153)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7153 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7153) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7153))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7153)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7154 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7154) = g32p_row31_cosetRepresentatives 7154 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7154 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7154) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7154))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7154)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7154 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7154) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7154))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7154)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7155 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7155) = g32p_row31_cosetRepresentatives 7155 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7155 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7155) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7155))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7155)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7155 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7155) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7155))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7155)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7156 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7156) = g32p_row31_cosetRepresentatives 7156 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7156 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7156) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7156))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7156)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7156 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7156) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7156))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7156)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7157 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7157) = g32p_row31_cosetRepresentatives 7157 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7157 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7157) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7157))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7157)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7157 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7157) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7157))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7157)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7158 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7158) = g32p_row31_cosetRepresentatives 7158 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7158 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7158) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7158))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7158)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7158 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7158) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7158))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7158)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7159 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7159) = g32p_row31_cosetRepresentatives 7159 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7159 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7159) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7159))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7159)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7159 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7159) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7159))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7159)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7160 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7160) = g32p_row31_cosetRepresentatives 7160 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7160 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7160) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7160))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7160)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7160 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7160) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7160))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7160)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7161 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7161) = g32p_row31_cosetRepresentatives 7161 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7161 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7161) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7161))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7161)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7161 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7161) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7161))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7161)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7162 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7162) = g32p_row31_cosetRepresentatives 7162 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7162 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7162) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7162))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7162)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7162 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7162) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7162))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7162)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7163 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7163) = g32p_row31_cosetRepresentatives 7163 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7163 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7163) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7163))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7163)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7163 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7163) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7163))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7163)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7164 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7164) = g32p_row31_cosetRepresentatives 7164 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7164 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7164) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7164))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7164)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7164 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7164) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7164))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7164)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7165 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7165) = g32p_row31_cosetRepresentatives 7165 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7165 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7165) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7165))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7165)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7165 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7165) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7165))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7165)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7166 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7166) = g32p_row31_cosetRepresentatives 7166 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7166 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7166) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7166))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7166)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7166 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7166) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7166))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7166)) := by
  decide +kernel

theorem g32p_row31_cosetWord_7167 :
    g32p_archiveIntegralWord (g32p_row31_cosetWords 7167) = g32p_row31_cosetRepresentatives 7167 := by
  decide +kernel

theorem g32p_row31_cosetGeneratorStep_7167 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives 7167) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s 7167))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s 7167)) := by
  decide +kernel

theorem g32p_row31_cosetBranchStep_7167 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives 7167) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s 7167))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s 7167)) := by
  decide +kernel

theorem g32p_row31_cosetWordBlock_0447 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row31_cosetWords (g32p_finBlockIndex 8640 447 r)) = g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 447 r) := by
  fin_cases r
  · exact g32p_row31_cosetWord_7152
  · exact g32p_row31_cosetWord_7153
  · exact g32p_row31_cosetWord_7154
  · exact g32p_row31_cosetWord_7155
  · exact g32p_row31_cosetWord_7156
  · exact g32p_row31_cosetWord_7157
  · exact g32p_row31_cosetWord_7158
  · exact g32p_row31_cosetWord_7159
  · exact g32p_row31_cosetWord_7160
  · exact g32p_row31_cosetWord_7161
  · exact g32p_row31_cosetWord_7162
  · exact g32p_row31_cosetWord_7163
  · exact g32p_row31_cosetWord_7164
  · exact g32p_row31_cosetWord_7165
  · exact g32p_row31_cosetWord_7166
  · exact g32p_row31_cosetWord_7167

theorem g32p_row31_cosetGeneratorBlock_0447 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 447 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetGeneratorNext s (g32p_finBlockIndex 8640 447 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetGeneratorFactor s (g32p_finBlockIndex 8640 447 r))) := by
  fin_cases r
  · exact g32p_row31_cosetGeneratorStep_7152 s
  · exact g32p_row31_cosetGeneratorStep_7153 s
  · exact g32p_row31_cosetGeneratorStep_7154 s
  · exact g32p_row31_cosetGeneratorStep_7155 s
  · exact g32p_row31_cosetGeneratorStep_7156 s
  · exact g32p_row31_cosetGeneratorStep_7157 s
  · exact g32p_row31_cosetGeneratorStep_7158 s
  · exact g32p_row31_cosetGeneratorStep_7159 s
  · exact g32p_row31_cosetGeneratorStep_7160 s
  · exact g32p_row31_cosetGeneratorStep_7161 s
  · exact g32p_row31_cosetGeneratorStep_7162 s
  · exact g32p_row31_cosetGeneratorStep_7163 s
  · exact g32p_row31_cosetGeneratorStep_7164 s
  · exact g32p_row31_cosetGeneratorStep_7165 s
  · exact g32p_row31_cosetGeneratorStep_7166 s
  · exact g32p_row31_cosetGeneratorStep_7167 s

theorem g32p_row31_cosetBranchBlock_0447 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row31_cosetBranchMatrices s) (g32p_row31_cosetRepresentatives (g32p_finBlockIndex 8640 447 r)) =
      HurwitzPrymRex_mmul (g32p_row31_cosetRepresentatives (g32p_row31_cosetBranchNext s (g32p_finBlockIndex 8640 447 r)))
        (g32p_row31_groupNodes (g32p_row31_cosetBranchFactor s (g32p_finBlockIndex 8640 447 r))) := by
  fin_cases r
  · exact g32p_row31_cosetBranchStep_7152 s
  · exact g32p_row31_cosetBranchStep_7153 s
  · exact g32p_row31_cosetBranchStep_7154 s
  · exact g32p_row31_cosetBranchStep_7155 s
  · exact g32p_row31_cosetBranchStep_7156 s
  · exact g32p_row31_cosetBranchStep_7157 s
  · exact g32p_row31_cosetBranchStep_7158 s
  · exact g32p_row31_cosetBranchStep_7159 s
  · exact g32p_row31_cosetBranchStep_7160 s
  · exact g32p_row31_cosetBranchStep_7161 s
  · exact g32p_row31_cosetBranchStep_7162 s
  · exact g32p_row31_cosetBranchStep_7163 s
  · exact g32p_row31_cosetBranchStep_7164 s
  · exact g32p_row31_cosetBranchStep_7165 s
  · exact g32p_row31_cosetBranchStep_7166 s
  · exact g32p_row31_cosetBranchStep_7167 s


end HodgeLean.Foundations.Program

end
