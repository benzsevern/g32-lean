import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked1044

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3840 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3840) = g32p_row13_cosetRepresentatives 3840 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3840 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3840) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3840))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3840)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3840 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3840) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3840))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3840)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3841 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3841) = g32p_row13_cosetRepresentatives 3841 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3841 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3841) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3841))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3841)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3841 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3841) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3841))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3841)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3842 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3842) = g32p_row13_cosetRepresentatives 3842 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3842 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3842) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3842))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3842)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3842 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3842) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3842))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3842)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3843 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3843) = g32p_row13_cosetRepresentatives 3843 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3843 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3843) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3843))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3843)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3843 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3843) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3843))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3843)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3844 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3844) = g32p_row13_cosetRepresentatives 3844 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3844 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3844) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3844))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3844)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3844 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3844) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3844))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3844)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3845 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3845) = g32p_row13_cosetRepresentatives 3845 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3845 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3845) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3845))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3845)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3845 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3845) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3845))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3845)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3846 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3846) = g32p_row13_cosetRepresentatives 3846 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3846 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3846) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3846))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3846)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3846 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3846) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3846))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3846)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3847 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3847) = g32p_row13_cosetRepresentatives 3847 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3847 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3847) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3847))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3847)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3847 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3847) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3847))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3847)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3848 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3848) = g32p_row13_cosetRepresentatives 3848 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3848 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3848) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3848))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3848)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3848 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3848) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3848))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3848)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3849 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3849) = g32p_row13_cosetRepresentatives 3849 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3849 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3849) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3849))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3849)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3849 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3849) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3849))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3849)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3850 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3850) = g32p_row13_cosetRepresentatives 3850 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3850 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3850) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3850))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3850)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3850 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3850) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3850))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3850)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3851 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3851) = g32p_row13_cosetRepresentatives 3851 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3851 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3851) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3851))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3851)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3851 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3851) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3851))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3851)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3852 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3852) = g32p_row13_cosetRepresentatives 3852 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3852 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3852) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3852))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3852)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3852 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3852) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3852))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3852)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3853 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3853) = g32p_row13_cosetRepresentatives 3853 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3853 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3853) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3853))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3853)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3853 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3853) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3853))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3853)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3854 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3854) = g32p_row13_cosetRepresentatives 3854 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3854 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3854) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3854))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3854)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3854 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3854) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3854))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3854)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3855 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3855) = g32p_row13_cosetRepresentatives 3855 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3855 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3855) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3855))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3855)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3855 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3855) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3855))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3855)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0240 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 240 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 240 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3840
  · exact g32p_row13_cosetWord_3841
  · exact g32p_row13_cosetWord_3842
  · exact g32p_row13_cosetWord_3843
  · exact g32p_row13_cosetWord_3844
  · exact g32p_row13_cosetWord_3845
  · exact g32p_row13_cosetWord_3846
  · exact g32p_row13_cosetWord_3847
  · exact g32p_row13_cosetWord_3848
  · exact g32p_row13_cosetWord_3849
  · exact g32p_row13_cosetWord_3850
  · exact g32p_row13_cosetWord_3851
  · exact g32p_row13_cosetWord_3852
  · exact g32p_row13_cosetWord_3853
  · exact g32p_row13_cosetWord_3854
  · exact g32p_row13_cosetWord_3855

theorem g32p_row13_cosetGeneratorBlock_0240 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 240 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 240 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 240 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3840 s
  · exact g32p_row13_cosetGeneratorStep_3841 s
  · exact g32p_row13_cosetGeneratorStep_3842 s
  · exact g32p_row13_cosetGeneratorStep_3843 s
  · exact g32p_row13_cosetGeneratorStep_3844 s
  · exact g32p_row13_cosetGeneratorStep_3845 s
  · exact g32p_row13_cosetGeneratorStep_3846 s
  · exact g32p_row13_cosetGeneratorStep_3847 s
  · exact g32p_row13_cosetGeneratorStep_3848 s
  · exact g32p_row13_cosetGeneratorStep_3849 s
  · exact g32p_row13_cosetGeneratorStep_3850 s
  · exact g32p_row13_cosetGeneratorStep_3851 s
  · exact g32p_row13_cosetGeneratorStep_3852 s
  · exact g32p_row13_cosetGeneratorStep_3853 s
  · exact g32p_row13_cosetGeneratorStep_3854 s
  · exact g32p_row13_cosetGeneratorStep_3855 s

theorem g32p_row13_cosetBranchBlock_0240 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 240 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 240 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 240 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3840 s
  · exact g32p_row13_cosetBranchStep_3841 s
  · exact g32p_row13_cosetBranchStep_3842 s
  · exact g32p_row13_cosetBranchStep_3843 s
  · exact g32p_row13_cosetBranchStep_3844 s
  · exact g32p_row13_cosetBranchStep_3845 s
  · exact g32p_row13_cosetBranchStep_3846 s
  · exact g32p_row13_cosetBranchStep_3847 s
  · exact g32p_row13_cosetBranchStep_3848 s
  · exact g32p_row13_cosetBranchStep_3849 s
  · exact g32p_row13_cosetBranchStep_3850 s
  · exact g32p_row13_cosetBranchStep_3851 s
  · exact g32p_row13_cosetBranchStep_3852 s
  · exact g32p_row13_cosetBranchStep_3853 s
  · exact g32p_row13_cosetBranchStep_3854 s
  · exact g32p_row13_cosetBranchStep_3855 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3856 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3856) = g32p_row13_cosetRepresentatives 3856 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3856 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3856) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3856))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3856)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3856 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3856) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3856))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3856)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3857 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3857) = g32p_row13_cosetRepresentatives 3857 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3857 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3857) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3857))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3857)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3857 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3857) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3857))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3857)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3858 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3858) = g32p_row13_cosetRepresentatives 3858 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3858 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3858) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3858))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3858)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3858 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3858) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3858))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3858)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3859 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3859) = g32p_row13_cosetRepresentatives 3859 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3859 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3859) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3859))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3859)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3859 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3859) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3859))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3859)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3860 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3860) = g32p_row13_cosetRepresentatives 3860 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3860 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3860) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3860))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3860)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3860 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3860) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3860))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3860)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3861 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3861) = g32p_row13_cosetRepresentatives 3861 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3861 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3861) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3861))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3861)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3861 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3861) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3861))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3861)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3862 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3862) = g32p_row13_cosetRepresentatives 3862 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3862 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3862) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3862))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3862)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3862 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3862) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3862))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3862)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3863 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3863) = g32p_row13_cosetRepresentatives 3863 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3863 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3863) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3863))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3863)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3863 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3863) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3863))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3863)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3864 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3864) = g32p_row13_cosetRepresentatives 3864 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3864 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3864) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3864))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3864)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3864 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3864) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3864))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3864)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3865 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3865) = g32p_row13_cosetRepresentatives 3865 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3865 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3865) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3865))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3865)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3865 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3865) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3865))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3865)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3866 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3866) = g32p_row13_cosetRepresentatives 3866 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3866 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3866) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3866))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3866)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3866 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3866) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3866))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3866)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3867 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3867) = g32p_row13_cosetRepresentatives 3867 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3867 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3867) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3867))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3867)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3867 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3867) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3867))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3867)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3868 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3868) = g32p_row13_cosetRepresentatives 3868 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3868 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3868) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3868))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3868)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3868 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3868) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3868))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3868)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3869 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3869) = g32p_row13_cosetRepresentatives 3869 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3869 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3869) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3869))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3869)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3869 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3869) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3869))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3869)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3870 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3870) = g32p_row13_cosetRepresentatives 3870 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3870 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3870) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3870))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3870)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3870 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3870) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3870))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3870)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3871 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3871) = g32p_row13_cosetRepresentatives 3871 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3871 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3871) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3871))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3871)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3871 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3871) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3871))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3871)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0241 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 241 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 241 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3856
  · exact g32p_row13_cosetWord_3857
  · exact g32p_row13_cosetWord_3858
  · exact g32p_row13_cosetWord_3859
  · exact g32p_row13_cosetWord_3860
  · exact g32p_row13_cosetWord_3861
  · exact g32p_row13_cosetWord_3862
  · exact g32p_row13_cosetWord_3863
  · exact g32p_row13_cosetWord_3864
  · exact g32p_row13_cosetWord_3865
  · exact g32p_row13_cosetWord_3866
  · exact g32p_row13_cosetWord_3867
  · exact g32p_row13_cosetWord_3868
  · exact g32p_row13_cosetWord_3869
  · exact g32p_row13_cosetWord_3870
  · exact g32p_row13_cosetWord_3871

theorem g32p_row13_cosetGeneratorBlock_0241 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 241 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 241 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 241 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3856 s
  · exact g32p_row13_cosetGeneratorStep_3857 s
  · exact g32p_row13_cosetGeneratorStep_3858 s
  · exact g32p_row13_cosetGeneratorStep_3859 s
  · exact g32p_row13_cosetGeneratorStep_3860 s
  · exact g32p_row13_cosetGeneratorStep_3861 s
  · exact g32p_row13_cosetGeneratorStep_3862 s
  · exact g32p_row13_cosetGeneratorStep_3863 s
  · exact g32p_row13_cosetGeneratorStep_3864 s
  · exact g32p_row13_cosetGeneratorStep_3865 s
  · exact g32p_row13_cosetGeneratorStep_3866 s
  · exact g32p_row13_cosetGeneratorStep_3867 s
  · exact g32p_row13_cosetGeneratorStep_3868 s
  · exact g32p_row13_cosetGeneratorStep_3869 s
  · exact g32p_row13_cosetGeneratorStep_3870 s
  · exact g32p_row13_cosetGeneratorStep_3871 s

theorem g32p_row13_cosetBranchBlock_0241 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 241 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 241 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 241 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3856 s
  · exact g32p_row13_cosetBranchStep_3857 s
  · exact g32p_row13_cosetBranchStep_3858 s
  · exact g32p_row13_cosetBranchStep_3859 s
  · exact g32p_row13_cosetBranchStep_3860 s
  · exact g32p_row13_cosetBranchStep_3861 s
  · exact g32p_row13_cosetBranchStep_3862 s
  · exact g32p_row13_cosetBranchStep_3863 s
  · exact g32p_row13_cosetBranchStep_3864 s
  · exact g32p_row13_cosetBranchStep_3865 s
  · exact g32p_row13_cosetBranchStep_3866 s
  · exact g32p_row13_cosetBranchStep_3867 s
  · exact g32p_row13_cosetBranchStep_3868 s
  · exact g32p_row13_cosetBranchStep_3869 s
  · exact g32p_row13_cosetBranchStep_3870 s
  · exact g32p_row13_cosetBranchStep_3871 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3872 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3872) = g32p_row13_cosetRepresentatives 3872 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3872 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3872) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3872))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3872)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3872 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3872) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3872))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3872)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3873 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3873) = g32p_row13_cosetRepresentatives 3873 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3873 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3873) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3873))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3873)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3873 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3873) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3873))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3873)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3874 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3874) = g32p_row13_cosetRepresentatives 3874 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3874 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3874) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3874))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3874)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3874 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3874) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3874))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3874)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3875 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3875) = g32p_row13_cosetRepresentatives 3875 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3875 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3875) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3875))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3875)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3875 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3875) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3875))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3875)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3876 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3876) = g32p_row13_cosetRepresentatives 3876 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3876 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3876) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3876))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3876)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3876 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3876) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3876))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3876)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3877 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3877) = g32p_row13_cosetRepresentatives 3877 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3877 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3877) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3877))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3877)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3877 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3877) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3877))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3877)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3878 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3878) = g32p_row13_cosetRepresentatives 3878 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3878 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3878) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3878))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3878)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3878 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3878) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3878))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3878)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3879 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3879) = g32p_row13_cosetRepresentatives 3879 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3879 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3879) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3879))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3879)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3879 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3879) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3879))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3879)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3880 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3880) = g32p_row13_cosetRepresentatives 3880 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3880 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3880) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3880))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3880)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3880 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3880) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3880))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3880)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3881 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3881) = g32p_row13_cosetRepresentatives 3881 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3881 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3881) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3881))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3881)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3881 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3881) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3881))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3881)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3882 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3882) = g32p_row13_cosetRepresentatives 3882 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3882 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3882) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3882))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3882)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3882 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3882) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3882))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3882)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3883 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3883) = g32p_row13_cosetRepresentatives 3883 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3883 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3883) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3883))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3883)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3883 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3883) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3883))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3883)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3884 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3884) = g32p_row13_cosetRepresentatives 3884 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3884 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3884) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3884))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3884)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3884 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3884) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3884))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3884)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3885 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3885) = g32p_row13_cosetRepresentatives 3885 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3885 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3885) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3885))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3885)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3885 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3885) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3885))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3885)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3886 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3886) = g32p_row13_cosetRepresentatives 3886 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3886 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3886) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3886))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3886)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3886 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3886) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3886))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3886)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3887 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3887) = g32p_row13_cosetRepresentatives 3887 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3887 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3887) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3887))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3887)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3887 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3887) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3887))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3887)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0242 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 242 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 242 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3872
  · exact g32p_row13_cosetWord_3873
  · exact g32p_row13_cosetWord_3874
  · exact g32p_row13_cosetWord_3875
  · exact g32p_row13_cosetWord_3876
  · exact g32p_row13_cosetWord_3877
  · exact g32p_row13_cosetWord_3878
  · exact g32p_row13_cosetWord_3879
  · exact g32p_row13_cosetWord_3880
  · exact g32p_row13_cosetWord_3881
  · exact g32p_row13_cosetWord_3882
  · exact g32p_row13_cosetWord_3883
  · exact g32p_row13_cosetWord_3884
  · exact g32p_row13_cosetWord_3885
  · exact g32p_row13_cosetWord_3886
  · exact g32p_row13_cosetWord_3887

theorem g32p_row13_cosetGeneratorBlock_0242 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 242 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 242 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 242 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3872 s
  · exact g32p_row13_cosetGeneratorStep_3873 s
  · exact g32p_row13_cosetGeneratorStep_3874 s
  · exact g32p_row13_cosetGeneratorStep_3875 s
  · exact g32p_row13_cosetGeneratorStep_3876 s
  · exact g32p_row13_cosetGeneratorStep_3877 s
  · exact g32p_row13_cosetGeneratorStep_3878 s
  · exact g32p_row13_cosetGeneratorStep_3879 s
  · exact g32p_row13_cosetGeneratorStep_3880 s
  · exact g32p_row13_cosetGeneratorStep_3881 s
  · exact g32p_row13_cosetGeneratorStep_3882 s
  · exact g32p_row13_cosetGeneratorStep_3883 s
  · exact g32p_row13_cosetGeneratorStep_3884 s
  · exact g32p_row13_cosetGeneratorStep_3885 s
  · exact g32p_row13_cosetGeneratorStep_3886 s
  · exact g32p_row13_cosetGeneratorStep_3887 s

theorem g32p_row13_cosetBranchBlock_0242 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 242 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 242 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 242 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3872 s
  · exact g32p_row13_cosetBranchStep_3873 s
  · exact g32p_row13_cosetBranchStep_3874 s
  · exact g32p_row13_cosetBranchStep_3875 s
  · exact g32p_row13_cosetBranchStep_3876 s
  · exact g32p_row13_cosetBranchStep_3877 s
  · exact g32p_row13_cosetBranchStep_3878 s
  · exact g32p_row13_cosetBranchStep_3879 s
  · exact g32p_row13_cosetBranchStep_3880 s
  · exact g32p_row13_cosetBranchStep_3881 s
  · exact g32p_row13_cosetBranchStep_3882 s
  · exact g32p_row13_cosetBranchStep_3883 s
  · exact g32p_row13_cosetBranchStep_3884 s
  · exact g32p_row13_cosetBranchStep_3885 s
  · exact g32p_row13_cosetBranchStep_3886 s
  · exact g32p_row13_cosetBranchStep_3887 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3888 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3888) = g32p_row13_cosetRepresentatives 3888 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3888 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3888) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3888))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3888)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3888 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3888) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3888))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3888)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3889 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3889) = g32p_row13_cosetRepresentatives 3889 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3889 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3889) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3889))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3889)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3889 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3889) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3889))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3889)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3890 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3890) = g32p_row13_cosetRepresentatives 3890 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3890 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3890) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3890))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3890)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3890 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3890) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3890))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3890)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3891 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3891) = g32p_row13_cosetRepresentatives 3891 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3891 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3891) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3891))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3891)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3891 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3891) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3891))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3891)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3892 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3892) = g32p_row13_cosetRepresentatives 3892 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3892 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3892) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3892))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3892)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3892 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3892) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3892))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3892)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3893 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3893) = g32p_row13_cosetRepresentatives 3893 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3893 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3893) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3893))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3893)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3893 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3893) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3893))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3893)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3894 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3894) = g32p_row13_cosetRepresentatives 3894 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3894 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3894) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3894))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3894)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3894 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3894) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3894))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3894)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3895 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3895) = g32p_row13_cosetRepresentatives 3895 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3895 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3895) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3895))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3895)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3895 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3895) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3895))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3895)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3896 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3896) = g32p_row13_cosetRepresentatives 3896 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3896 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3896) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3896))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3896)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3896 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3896) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3896))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3896)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3897 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3897) = g32p_row13_cosetRepresentatives 3897 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3897 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3897) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3897))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3897)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3897 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3897) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3897))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3897)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3898 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3898) = g32p_row13_cosetRepresentatives 3898 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3898 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3898) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3898))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3898)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3898 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3898) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3898))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3898)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3899 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3899) = g32p_row13_cosetRepresentatives 3899 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3899 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3899) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3899))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3899)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3899 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3899) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3899))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3899)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3900 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3900) = g32p_row13_cosetRepresentatives 3900 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3900 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3900) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3900))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3900)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3900 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3900) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3900))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3900)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3901 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3901) = g32p_row13_cosetRepresentatives 3901 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3901 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3901) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3901))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3901)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3901 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3901) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3901))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3901)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3902 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3902) = g32p_row13_cosetRepresentatives 3902 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3902 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3902) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3902))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3902)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3902 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3902) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3902))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3902)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3903 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3903) = g32p_row13_cosetRepresentatives 3903 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3903 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3903) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3903))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3903)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3903 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3903) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3903))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3903)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0243 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 243 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 243 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3888
  · exact g32p_row13_cosetWord_3889
  · exact g32p_row13_cosetWord_3890
  · exact g32p_row13_cosetWord_3891
  · exact g32p_row13_cosetWord_3892
  · exact g32p_row13_cosetWord_3893
  · exact g32p_row13_cosetWord_3894
  · exact g32p_row13_cosetWord_3895
  · exact g32p_row13_cosetWord_3896
  · exact g32p_row13_cosetWord_3897
  · exact g32p_row13_cosetWord_3898
  · exact g32p_row13_cosetWord_3899
  · exact g32p_row13_cosetWord_3900
  · exact g32p_row13_cosetWord_3901
  · exact g32p_row13_cosetWord_3902
  · exact g32p_row13_cosetWord_3903

theorem g32p_row13_cosetGeneratorBlock_0243 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 243 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 243 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 243 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3888 s
  · exact g32p_row13_cosetGeneratorStep_3889 s
  · exact g32p_row13_cosetGeneratorStep_3890 s
  · exact g32p_row13_cosetGeneratorStep_3891 s
  · exact g32p_row13_cosetGeneratorStep_3892 s
  · exact g32p_row13_cosetGeneratorStep_3893 s
  · exact g32p_row13_cosetGeneratorStep_3894 s
  · exact g32p_row13_cosetGeneratorStep_3895 s
  · exact g32p_row13_cosetGeneratorStep_3896 s
  · exact g32p_row13_cosetGeneratorStep_3897 s
  · exact g32p_row13_cosetGeneratorStep_3898 s
  · exact g32p_row13_cosetGeneratorStep_3899 s
  · exact g32p_row13_cosetGeneratorStep_3900 s
  · exact g32p_row13_cosetGeneratorStep_3901 s
  · exact g32p_row13_cosetGeneratorStep_3902 s
  · exact g32p_row13_cosetGeneratorStep_3903 s

theorem g32p_row13_cosetBranchBlock_0243 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 243 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 243 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 243 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3888 s
  · exact g32p_row13_cosetBranchStep_3889 s
  · exact g32p_row13_cosetBranchStep_3890 s
  · exact g32p_row13_cosetBranchStep_3891 s
  · exact g32p_row13_cosetBranchStep_3892 s
  · exact g32p_row13_cosetBranchStep_3893 s
  · exact g32p_row13_cosetBranchStep_3894 s
  · exact g32p_row13_cosetBranchStep_3895 s
  · exact g32p_row13_cosetBranchStep_3896 s
  · exact g32p_row13_cosetBranchStep_3897 s
  · exact g32p_row13_cosetBranchStep_3898 s
  · exact g32p_row13_cosetBranchStep_3899 s
  · exact g32p_row13_cosetBranchStep_3900 s
  · exact g32p_row13_cosetBranchStep_3901 s
  · exact g32p_row13_cosetBranchStep_3902 s
  · exact g32p_row13_cosetBranchStep_3903 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3904 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3904) = g32p_row13_cosetRepresentatives 3904 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3904 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3904) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3904))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3904)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3904 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3904) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3904))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3904)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3905 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3905) = g32p_row13_cosetRepresentatives 3905 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3905 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3905) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3905))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3905)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3905 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3905) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3905))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3905)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3906 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3906) = g32p_row13_cosetRepresentatives 3906 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3906 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3906) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3906))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3906)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3906 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3906) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3906))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3906)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3907 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3907) = g32p_row13_cosetRepresentatives 3907 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3907 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3907) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3907))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3907)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3907 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3907) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3907))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3907)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3908 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3908) = g32p_row13_cosetRepresentatives 3908 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3908 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3908) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3908))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3908)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3908 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3908) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3908))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3908)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3909 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3909) = g32p_row13_cosetRepresentatives 3909 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3909 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3909) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3909))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3909)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3909 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3909) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3909))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3909)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3910 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3910) = g32p_row13_cosetRepresentatives 3910 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3910 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3910) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3910))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3910)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3910 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3910) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3910))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3910)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3911 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3911) = g32p_row13_cosetRepresentatives 3911 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3911 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3911) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3911))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3911)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3911 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3911) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3911))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3911)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3912 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3912) = g32p_row13_cosetRepresentatives 3912 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3912 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3912) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3912))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3912)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3912 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3912) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3912))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3912)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3913 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3913) = g32p_row13_cosetRepresentatives 3913 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3913 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3913) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3913))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3913)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3913 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3913) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3913))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3913)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3914 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3914) = g32p_row13_cosetRepresentatives 3914 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3914 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3914) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3914))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3914)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3914 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3914) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3914))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3914)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3915 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3915) = g32p_row13_cosetRepresentatives 3915 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3915 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3915) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3915))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3915)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3915 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3915) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3915))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3915)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3916 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3916) = g32p_row13_cosetRepresentatives 3916 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3916 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3916) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3916))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3916)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3916 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3916) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3916))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3916)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3917 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3917) = g32p_row13_cosetRepresentatives 3917 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3917 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3917) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3917))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3917)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3917 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3917) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3917))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3917)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3918 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3918) = g32p_row13_cosetRepresentatives 3918 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3918 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3918) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3918))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3918)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3918 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3918) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3918))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3918)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3919 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3919) = g32p_row13_cosetRepresentatives 3919 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3919 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3919) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3919))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3919)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3919 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3919) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3919))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3919)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0244 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 244 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 244 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3904
  · exact g32p_row13_cosetWord_3905
  · exact g32p_row13_cosetWord_3906
  · exact g32p_row13_cosetWord_3907
  · exact g32p_row13_cosetWord_3908
  · exact g32p_row13_cosetWord_3909
  · exact g32p_row13_cosetWord_3910
  · exact g32p_row13_cosetWord_3911
  · exact g32p_row13_cosetWord_3912
  · exact g32p_row13_cosetWord_3913
  · exact g32p_row13_cosetWord_3914
  · exact g32p_row13_cosetWord_3915
  · exact g32p_row13_cosetWord_3916
  · exact g32p_row13_cosetWord_3917
  · exact g32p_row13_cosetWord_3918
  · exact g32p_row13_cosetWord_3919

theorem g32p_row13_cosetGeneratorBlock_0244 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 244 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 244 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 244 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3904 s
  · exact g32p_row13_cosetGeneratorStep_3905 s
  · exact g32p_row13_cosetGeneratorStep_3906 s
  · exact g32p_row13_cosetGeneratorStep_3907 s
  · exact g32p_row13_cosetGeneratorStep_3908 s
  · exact g32p_row13_cosetGeneratorStep_3909 s
  · exact g32p_row13_cosetGeneratorStep_3910 s
  · exact g32p_row13_cosetGeneratorStep_3911 s
  · exact g32p_row13_cosetGeneratorStep_3912 s
  · exact g32p_row13_cosetGeneratorStep_3913 s
  · exact g32p_row13_cosetGeneratorStep_3914 s
  · exact g32p_row13_cosetGeneratorStep_3915 s
  · exact g32p_row13_cosetGeneratorStep_3916 s
  · exact g32p_row13_cosetGeneratorStep_3917 s
  · exact g32p_row13_cosetGeneratorStep_3918 s
  · exact g32p_row13_cosetGeneratorStep_3919 s

theorem g32p_row13_cosetBranchBlock_0244 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 244 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 244 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 244 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3904 s
  · exact g32p_row13_cosetBranchStep_3905 s
  · exact g32p_row13_cosetBranchStep_3906 s
  · exact g32p_row13_cosetBranchStep_3907 s
  · exact g32p_row13_cosetBranchStep_3908 s
  · exact g32p_row13_cosetBranchStep_3909 s
  · exact g32p_row13_cosetBranchStep_3910 s
  · exact g32p_row13_cosetBranchStep_3911 s
  · exact g32p_row13_cosetBranchStep_3912 s
  · exact g32p_row13_cosetBranchStep_3913 s
  · exact g32p_row13_cosetBranchStep_3914 s
  · exact g32p_row13_cosetBranchStep_3915 s
  · exact g32p_row13_cosetBranchStep_3916 s
  · exact g32p_row13_cosetBranchStep_3917 s
  · exact g32p_row13_cosetBranchStep_3918 s
  · exact g32p_row13_cosetBranchStep_3919 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3920 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3920) = g32p_row13_cosetRepresentatives 3920 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3920 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3920) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3920))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3920)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3920 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3920) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3920))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3920)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3921 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3921) = g32p_row13_cosetRepresentatives 3921 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3921 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3921) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3921))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3921)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3921 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3921) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3921))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3921)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3922 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3922) = g32p_row13_cosetRepresentatives 3922 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3922 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3922) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3922))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3922)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3922 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3922) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3922))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3922)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3923 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3923) = g32p_row13_cosetRepresentatives 3923 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3923 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3923) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3923))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3923)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3923 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3923) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3923))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3923)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3924 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3924) = g32p_row13_cosetRepresentatives 3924 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3924 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3924) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3924))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3924)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3924 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3924) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3924))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3924)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3925 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3925) = g32p_row13_cosetRepresentatives 3925 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3925 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3925) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3925))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3925)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3925 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3925) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3925))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3925)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3926 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3926) = g32p_row13_cosetRepresentatives 3926 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3926 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3926) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3926))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3926)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3926 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3926) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3926))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3926)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3927 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3927) = g32p_row13_cosetRepresentatives 3927 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3927 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3927) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3927))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3927)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3927 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3927) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3927))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3927)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3928 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3928) = g32p_row13_cosetRepresentatives 3928 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3928 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3928) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3928))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3928)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3928 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3928) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3928))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3928)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3929 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3929) = g32p_row13_cosetRepresentatives 3929 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3929 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3929) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3929))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3929)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3929 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3929) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3929))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3929)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3930 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3930) = g32p_row13_cosetRepresentatives 3930 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3930 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3930) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3930))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3930)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3930 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3930) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3930))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3930)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3931 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3931) = g32p_row13_cosetRepresentatives 3931 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3931 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3931) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3931))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3931)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3931 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3931) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3931))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3931)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3932 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3932) = g32p_row13_cosetRepresentatives 3932 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3932 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3932) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3932))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3932)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3932 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3932) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3932))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3932)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3933 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3933) = g32p_row13_cosetRepresentatives 3933 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3933 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3933) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3933))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3933)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3933 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3933) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3933))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3933)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3934 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3934) = g32p_row13_cosetRepresentatives 3934 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3934 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3934) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3934))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3934)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3934 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3934) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3934))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3934)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3935 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3935) = g32p_row13_cosetRepresentatives 3935 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3935 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3935) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3935))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3935)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3935 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3935) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3935))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3935)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0245 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 245 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 245 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3920
  · exact g32p_row13_cosetWord_3921
  · exact g32p_row13_cosetWord_3922
  · exact g32p_row13_cosetWord_3923
  · exact g32p_row13_cosetWord_3924
  · exact g32p_row13_cosetWord_3925
  · exact g32p_row13_cosetWord_3926
  · exact g32p_row13_cosetWord_3927
  · exact g32p_row13_cosetWord_3928
  · exact g32p_row13_cosetWord_3929
  · exact g32p_row13_cosetWord_3930
  · exact g32p_row13_cosetWord_3931
  · exact g32p_row13_cosetWord_3932
  · exact g32p_row13_cosetWord_3933
  · exact g32p_row13_cosetWord_3934
  · exact g32p_row13_cosetWord_3935

theorem g32p_row13_cosetGeneratorBlock_0245 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 245 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 245 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 245 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3920 s
  · exact g32p_row13_cosetGeneratorStep_3921 s
  · exact g32p_row13_cosetGeneratorStep_3922 s
  · exact g32p_row13_cosetGeneratorStep_3923 s
  · exact g32p_row13_cosetGeneratorStep_3924 s
  · exact g32p_row13_cosetGeneratorStep_3925 s
  · exact g32p_row13_cosetGeneratorStep_3926 s
  · exact g32p_row13_cosetGeneratorStep_3927 s
  · exact g32p_row13_cosetGeneratorStep_3928 s
  · exact g32p_row13_cosetGeneratorStep_3929 s
  · exact g32p_row13_cosetGeneratorStep_3930 s
  · exact g32p_row13_cosetGeneratorStep_3931 s
  · exact g32p_row13_cosetGeneratorStep_3932 s
  · exact g32p_row13_cosetGeneratorStep_3933 s
  · exact g32p_row13_cosetGeneratorStep_3934 s
  · exact g32p_row13_cosetGeneratorStep_3935 s

theorem g32p_row13_cosetBranchBlock_0245 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 245 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 245 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 245 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3920 s
  · exact g32p_row13_cosetBranchStep_3921 s
  · exact g32p_row13_cosetBranchStep_3922 s
  · exact g32p_row13_cosetBranchStep_3923 s
  · exact g32p_row13_cosetBranchStep_3924 s
  · exact g32p_row13_cosetBranchStep_3925 s
  · exact g32p_row13_cosetBranchStep_3926 s
  · exact g32p_row13_cosetBranchStep_3927 s
  · exact g32p_row13_cosetBranchStep_3928 s
  · exact g32p_row13_cosetBranchStep_3929 s
  · exact g32p_row13_cosetBranchStep_3930 s
  · exact g32p_row13_cosetBranchStep_3931 s
  · exact g32p_row13_cosetBranchStep_3932 s
  · exact g32p_row13_cosetBranchStep_3933 s
  · exact g32p_row13_cosetBranchStep_3934 s
  · exact g32p_row13_cosetBranchStep_3935 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3936 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3936) = g32p_row13_cosetRepresentatives 3936 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3936 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3936) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3936))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3936)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3936 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3936) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3936))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3936)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3937 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3937) = g32p_row13_cosetRepresentatives 3937 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3937 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3937) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3937))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3937)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3937 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3937) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3937))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3937)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3938 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3938) = g32p_row13_cosetRepresentatives 3938 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3938 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3938) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3938))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3938)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3938 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3938) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3938))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3938)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3939 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3939) = g32p_row13_cosetRepresentatives 3939 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3939 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3939) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3939))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3939)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3939 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3939) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3939))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3939)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3940 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3940) = g32p_row13_cosetRepresentatives 3940 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3940 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3940) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3940))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3940)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3940 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3940) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3940))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3940)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3941 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3941) = g32p_row13_cosetRepresentatives 3941 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3941 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3941) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3941))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3941)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3941 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3941) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3941))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3941)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3942 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3942) = g32p_row13_cosetRepresentatives 3942 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3942 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3942) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3942))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3942)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3942 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3942) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3942))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3942)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3943 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3943) = g32p_row13_cosetRepresentatives 3943 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3943 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3943) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3943))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3943)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3943 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3943) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3943))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3943)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3944 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3944) = g32p_row13_cosetRepresentatives 3944 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3944 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3944) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3944))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3944)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3944 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3944) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3944))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3944)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3945 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3945) = g32p_row13_cosetRepresentatives 3945 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3945 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3945) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3945))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3945)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3945 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3945) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3945))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3945)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3946 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3946) = g32p_row13_cosetRepresentatives 3946 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3946 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3946) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3946))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3946)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3946 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3946) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3946))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3946)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3947 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3947) = g32p_row13_cosetRepresentatives 3947 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3947 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3947) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3947))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3947)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3947 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3947) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3947))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3947)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3948 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3948) = g32p_row13_cosetRepresentatives 3948 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3948 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3948) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3948))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3948)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3948 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3948) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3948))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3948)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3949 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3949) = g32p_row13_cosetRepresentatives 3949 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3949 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3949) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3949))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3949)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3949 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3949) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3949))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3949)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3950 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3950) = g32p_row13_cosetRepresentatives 3950 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3950 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3950) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3950))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3950)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3950 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3950) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3950))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3950)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3951 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3951) = g32p_row13_cosetRepresentatives 3951 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3951 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3951) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3951))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3951)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3951 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3951) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3951))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3951)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0246 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 246 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 246 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3936
  · exact g32p_row13_cosetWord_3937
  · exact g32p_row13_cosetWord_3938
  · exact g32p_row13_cosetWord_3939
  · exact g32p_row13_cosetWord_3940
  · exact g32p_row13_cosetWord_3941
  · exact g32p_row13_cosetWord_3942
  · exact g32p_row13_cosetWord_3943
  · exact g32p_row13_cosetWord_3944
  · exact g32p_row13_cosetWord_3945
  · exact g32p_row13_cosetWord_3946
  · exact g32p_row13_cosetWord_3947
  · exact g32p_row13_cosetWord_3948
  · exact g32p_row13_cosetWord_3949
  · exact g32p_row13_cosetWord_3950
  · exact g32p_row13_cosetWord_3951

theorem g32p_row13_cosetGeneratorBlock_0246 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 246 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 246 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 246 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3936 s
  · exact g32p_row13_cosetGeneratorStep_3937 s
  · exact g32p_row13_cosetGeneratorStep_3938 s
  · exact g32p_row13_cosetGeneratorStep_3939 s
  · exact g32p_row13_cosetGeneratorStep_3940 s
  · exact g32p_row13_cosetGeneratorStep_3941 s
  · exact g32p_row13_cosetGeneratorStep_3942 s
  · exact g32p_row13_cosetGeneratorStep_3943 s
  · exact g32p_row13_cosetGeneratorStep_3944 s
  · exact g32p_row13_cosetGeneratorStep_3945 s
  · exact g32p_row13_cosetGeneratorStep_3946 s
  · exact g32p_row13_cosetGeneratorStep_3947 s
  · exact g32p_row13_cosetGeneratorStep_3948 s
  · exact g32p_row13_cosetGeneratorStep_3949 s
  · exact g32p_row13_cosetGeneratorStep_3950 s
  · exact g32p_row13_cosetGeneratorStep_3951 s

theorem g32p_row13_cosetBranchBlock_0246 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 246 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 246 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 246 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3936 s
  · exact g32p_row13_cosetBranchStep_3937 s
  · exact g32p_row13_cosetBranchStep_3938 s
  · exact g32p_row13_cosetBranchStep_3939 s
  · exact g32p_row13_cosetBranchStep_3940 s
  · exact g32p_row13_cosetBranchStep_3941 s
  · exact g32p_row13_cosetBranchStep_3942 s
  · exact g32p_row13_cosetBranchStep_3943 s
  · exact g32p_row13_cosetBranchStep_3944 s
  · exact g32p_row13_cosetBranchStep_3945 s
  · exact g32p_row13_cosetBranchStep_3946 s
  · exact g32p_row13_cosetBranchStep_3947 s
  · exact g32p_row13_cosetBranchStep_3948 s
  · exact g32p_row13_cosetBranchStep_3949 s
  · exact g32p_row13_cosetBranchStep_3950 s
  · exact g32p_row13_cosetBranchStep_3951 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3952 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3952) = g32p_row13_cosetRepresentatives 3952 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3952 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3952) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3952))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3952)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3952 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3952) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3952))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3952)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3953 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3953) = g32p_row13_cosetRepresentatives 3953 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3953 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3953) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3953))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3953)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3953 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3953) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3953))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3953)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3954 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3954) = g32p_row13_cosetRepresentatives 3954 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3954 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3954) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3954))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3954)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3954 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3954) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3954))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3954)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3955 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3955) = g32p_row13_cosetRepresentatives 3955 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3955 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3955) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3955))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3955)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3955 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3955) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3955))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3955)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3956 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3956) = g32p_row13_cosetRepresentatives 3956 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3956 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3956) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3956))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3956)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3956 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3956) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3956))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3956)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3957 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3957) = g32p_row13_cosetRepresentatives 3957 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3957 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3957) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3957))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3957)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3957 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3957) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3957))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3957)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3958 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3958) = g32p_row13_cosetRepresentatives 3958 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3958 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3958) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3958))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3958)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3958 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3958) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3958))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3958)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3959 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3959) = g32p_row13_cosetRepresentatives 3959 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3959 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3959) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3959))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3959)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3959 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3959) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3959))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3959)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3960 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3960) = g32p_row13_cosetRepresentatives 3960 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3960 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3960) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3960))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3960)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3960 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3960) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3960))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3960)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3961 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3961) = g32p_row13_cosetRepresentatives 3961 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3961 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3961) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3961))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3961)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3961 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3961) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3961))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3961)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3962 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3962) = g32p_row13_cosetRepresentatives 3962 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3962 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3962) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3962))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3962)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3962 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3962) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3962))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3962)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3963 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3963) = g32p_row13_cosetRepresentatives 3963 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3963 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3963) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3963))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3963)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3963 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3963) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3963))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3963)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3964 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3964) = g32p_row13_cosetRepresentatives 3964 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3964 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3964) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3964))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3964)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3964 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3964) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3964))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3964)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3965 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3965) = g32p_row13_cosetRepresentatives 3965 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3965 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3965) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3965))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3965)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3965 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3965) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3965))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3965)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3966 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3966) = g32p_row13_cosetRepresentatives 3966 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3966 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3966) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3966))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3966)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3966 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3966) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3966))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3966)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3967 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3967) = g32p_row13_cosetRepresentatives 3967 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3967 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3967) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3967))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3967)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3967 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3967) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3967))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3967)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0247 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 247 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 247 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3952
  · exact g32p_row13_cosetWord_3953
  · exact g32p_row13_cosetWord_3954
  · exact g32p_row13_cosetWord_3955
  · exact g32p_row13_cosetWord_3956
  · exact g32p_row13_cosetWord_3957
  · exact g32p_row13_cosetWord_3958
  · exact g32p_row13_cosetWord_3959
  · exact g32p_row13_cosetWord_3960
  · exact g32p_row13_cosetWord_3961
  · exact g32p_row13_cosetWord_3962
  · exact g32p_row13_cosetWord_3963
  · exact g32p_row13_cosetWord_3964
  · exact g32p_row13_cosetWord_3965
  · exact g32p_row13_cosetWord_3966
  · exact g32p_row13_cosetWord_3967

theorem g32p_row13_cosetGeneratorBlock_0247 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 247 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 247 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 247 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3952 s
  · exact g32p_row13_cosetGeneratorStep_3953 s
  · exact g32p_row13_cosetGeneratorStep_3954 s
  · exact g32p_row13_cosetGeneratorStep_3955 s
  · exact g32p_row13_cosetGeneratorStep_3956 s
  · exact g32p_row13_cosetGeneratorStep_3957 s
  · exact g32p_row13_cosetGeneratorStep_3958 s
  · exact g32p_row13_cosetGeneratorStep_3959 s
  · exact g32p_row13_cosetGeneratorStep_3960 s
  · exact g32p_row13_cosetGeneratorStep_3961 s
  · exact g32p_row13_cosetGeneratorStep_3962 s
  · exact g32p_row13_cosetGeneratorStep_3963 s
  · exact g32p_row13_cosetGeneratorStep_3964 s
  · exact g32p_row13_cosetGeneratorStep_3965 s
  · exact g32p_row13_cosetGeneratorStep_3966 s
  · exact g32p_row13_cosetGeneratorStep_3967 s

theorem g32p_row13_cosetBranchBlock_0247 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 247 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 247 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 247 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3952 s
  · exact g32p_row13_cosetBranchStep_3953 s
  · exact g32p_row13_cosetBranchStep_3954 s
  · exact g32p_row13_cosetBranchStep_3955 s
  · exact g32p_row13_cosetBranchStep_3956 s
  · exact g32p_row13_cosetBranchStep_3957 s
  · exact g32p_row13_cosetBranchStep_3958 s
  · exact g32p_row13_cosetBranchStep_3959 s
  · exact g32p_row13_cosetBranchStep_3960 s
  · exact g32p_row13_cosetBranchStep_3961 s
  · exact g32p_row13_cosetBranchStep_3962 s
  · exact g32p_row13_cosetBranchStep_3963 s
  · exact g32p_row13_cosetBranchStep_3964 s
  · exact g32p_row13_cosetBranchStep_3965 s
  · exact g32p_row13_cosetBranchStep_3966 s
  · exact g32p_row13_cosetBranchStep_3967 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3968 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3968) = g32p_row13_cosetRepresentatives 3968 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3968 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3968) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3968))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3968)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3968 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3968) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3968))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3968)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3969 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3969) = g32p_row13_cosetRepresentatives 3969 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3969 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3969) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3969))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3969)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3969 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3969) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3969))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3969)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3970 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3970) = g32p_row13_cosetRepresentatives 3970 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3970 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3970) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3970))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3970)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3970 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3970) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3970))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3970)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3971 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3971) = g32p_row13_cosetRepresentatives 3971 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3971 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3971) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3971))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3971)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3971 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3971) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3971))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3971)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3972 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3972) = g32p_row13_cosetRepresentatives 3972 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3972 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3972) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3972))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3972)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3972 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3972) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3972))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3972)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3973 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3973) = g32p_row13_cosetRepresentatives 3973 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3973 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3973) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3973))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3973)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3973 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3973) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3973))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3973)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3974 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3974) = g32p_row13_cosetRepresentatives 3974 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3974 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3974) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3974))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3974)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3974 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3974) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3974))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3974)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3975 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3975) = g32p_row13_cosetRepresentatives 3975 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3975 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3975) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3975))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3975)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3975 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3975) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3975))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3975)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3976 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3976) = g32p_row13_cosetRepresentatives 3976 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3976 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3976) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3976))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3976)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3976 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3976) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3976))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3976)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3977 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3977) = g32p_row13_cosetRepresentatives 3977 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3977 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3977) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3977))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3977)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3977 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3977) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3977))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3977)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3978 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3978) = g32p_row13_cosetRepresentatives 3978 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3978 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3978) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3978))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3978)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3978 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3978) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3978))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3978)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3979 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3979) = g32p_row13_cosetRepresentatives 3979 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3979 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3979) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3979))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3979)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3979 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3979) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3979))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3979)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3980 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3980) = g32p_row13_cosetRepresentatives 3980 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3980 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3980) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3980))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3980)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3980 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3980) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3980))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3980)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3981 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3981) = g32p_row13_cosetRepresentatives 3981 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3981 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3981) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3981))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3981)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3981 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3981) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3981))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3981)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3982 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3982) = g32p_row13_cosetRepresentatives 3982 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3982 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3982) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3982))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3982)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3982 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3982) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3982))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3982)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3983 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3983) = g32p_row13_cosetRepresentatives 3983 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3983 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3983) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3983))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3983)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3983 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3983) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3983))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3983)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0248 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 248 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 248 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3968
  · exact g32p_row13_cosetWord_3969
  · exact g32p_row13_cosetWord_3970
  · exact g32p_row13_cosetWord_3971
  · exact g32p_row13_cosetWord_3972
  · exact g32p_row13_cosetWord_3973
  · exact g32p_row13_cosetWord_3974
  · exact g32p_row13_cosetWord_3975
  · exact g32p_row13_cosetWord_3976
  · exact g32p_row13_cosetWord_3977
  · exact g32p_row13_cosetWord_3978
  · exact g32p_row13_cosetWord_3979
  · exact g32p_row13_cosetWord_3980
  · exact g32p_row13_cosetWord_3981
  · exact g32p_row13_cosetWord_3982
  · exact g32p_row13_cosetWord_3983

theorem g32p_row13_cosetGeneratorBlock_0248 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 248 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 248 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 248 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3968 s
  · exact g32p_row13_cosetGeneratorStep_3969 s
  · exact g32p_row13_cosetGeneratorStep_3970 s
  · exact g32p_row13_cosetGeneratorStep_3971 s
  · exact g32p_row13_cosetGeneratorStep_3972 s
  · exact g32p_row13_cosetGeneratorStep_3973 s
  · exact g32p_row13_cosetGeneratorStep_3974 s
  · exact g32p_row13_cosetGeneratorStep_3975 s
  · exact g32p_row13_cosetGeneratorStep_3976 s
  · exact g32p_row13_cosetGeneratorStep_3977 s
  · exact g32p_row13_cosetGeneratorStep_3978 s
  · exact g32p_row13_cosetGeneratorStep_3979 s
  · exact g32p_row13_cosetGeneratorStep_3980 s
  · exact g32p_row13_cosetGeneratorStep_3981 s
  · exact g32p_row13_cosetGeneratorStep_3982 s
  · exact g32p_row13_cosetGeneratorStep_3983 s

theorem g32p_row13_cosetBranchBlock_0248 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 248 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 248 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 248 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3968 s
  · exact g32p_row13_cosetBranchStep_3969 s
  · exact g32p_row13_cosetBranchStep_3970 s
  · exact g32p_row13_cosetBranchStep_3971 s
  · exact g32p_row13_cosetBranchStep_3972 s
  · exact g32p_row13_cosetBranchStep_3973 s
  · exact g32p_row13_cosetBranchStep_3974 s
  · exact g32p_row13_cosetBranchStep_3975 s
  · exact g32p_row13_cosetBranchStep_3976 s
  · exact g32p_row13_cosetBranchStep_3977 s
  · exact g32p_row13_cosetBranchStep_3978 s
  · exact g32p_row13_cosetBranchStep_3979 s
  · exact g32p_row13_cosetBranchStep_3980 s
  · exact g32p_row13_cosetBranchStep_3981 s
  · exact g32p_row13_cosetBranchStep_3982 s
  · exact g32p_row13_cosetBranchStep_3983 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_3984 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3984) = g32p_row13_cosetRepresentatives 3984 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3984 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3984) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3984))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3984)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3984 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3984) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3984))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3984)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3985 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3985) = g32p_row13_cosetRepresentatives 3985 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3985 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3985) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3985))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3985)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3985 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3985) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3985))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3985)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3986 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3986) = g32p_row13_cosetRepresentatives 3986 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3986 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3986) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3986))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3986)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3986 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3986) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3986))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3986)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3987 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3987) = g32p_row13_cosetRepresentatives 3987 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3987 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3987) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3987))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3987)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3987 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3987) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3987))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3987)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3988 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3988) = g32p_row13_cosetRepresentatives 3988 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3988 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3988) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3988))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3988)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3988 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3988) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3988))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3988)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3989 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3989) = g32p_row13_cosetRepresentatives 3989 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3989 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3989) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3989))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3989)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3989 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3989) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3989))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3989)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3990 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3990) = g32p_row13_cosetRepresentatives 3990 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3990 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3990) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3990))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3990)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3990 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3990) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3990))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3990)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3991 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3991) = g32p_row13_cosetRepresentatives 3991 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3991 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3991) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3991))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3991)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3991 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3991) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3991))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3991)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3992 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3992) = g32p_row13_cosetRepresentatives 3992 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3992 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3992) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3992))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3992)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3992 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3992) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3992))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3992)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3993 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3993) = g32p_row13_cosetRepresentatives 3993 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3993 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3993) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3993))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3993)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3993 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3993) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3993))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3993)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3994 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3994) = g32p_row13_cosetRepresentatives 3994 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3994 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3994) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3994))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3994)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3994 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3994) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3994))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3994)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3995 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3995) = g32p_row13_cosetRepresentatives 3995 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3995 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3995) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3995))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3995)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3995 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3995) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3995))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3995)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3996 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3996) = g32p_row13_cosetRepresentatives 3996 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3996 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3996) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3996))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3996)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3996 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3996) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3996))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3996)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3997 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3997) = g32p_row13_cosetRepresentatives 3997 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3997 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3997) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3997))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3997)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3997 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3997) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3997))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3997)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3998 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3998) = g32p_row13_cosetRepresentatives 3998 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3998 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3998) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3998))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3998)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3998 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3998) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3998))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3998)) := by
  decide +kernel

theorem g32p_row13_cosetWord_3999 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 3999) = g32p_row13_cosetRepresentatives 3999 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_3999 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 3999) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 3999))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 3999)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_3999 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 3999) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 3999))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 3999)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0249 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 249 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 249 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_3984
  · exact g32p_row13_cosetWord_3985
  · exact g32p_row13_cosetWord_3986
  · exact g32p_row13_cosetWord_3987
  · exact g32p_row13_cosetWord_3988
  · exact g32p_row13_cosetWord_3989
  · exact g32p_row13_cosetWord_3990
  · exact g32p_row13_cosetWord_3991
  · exact g32p_row13_cosetWord_3992
  · exact g32p_row13_cosetWord_3993
  · exact g32p_row13_cosetWord_3994
  · exact g32p_row13_cosetWord_3995
  · exact g32p_row13_cosetWord_3996
  · exact g32p_row13_cosetWord_3997
  · exact g32p_row13_cosetWord_3998
  · exact g32p_row13_cosetWord_3999

theorem g32p_row13_cosetGeneratorBlock_0249 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 249 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 249 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 249 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_3984 s
  · exact g32p_row13_cosetGeneratorStep_3985 s
  · exact g32p_row13_cosetGeneratorStep_3986 s
  · exact g32p_row13_cosetGeneratorStep_3987 s
  · exact g32p_row13_cosetGeneratorStep_3988 s
  · exact g32p_row13_cosetGeneratorStep_3989 s
  · exact g32p_row13_cosetGeneratorStep_3990 s
  · exact g32p_row13_cosetGeneratorStep_3991 s
  · exact g32p_row13_cosetGeneratorStep_3992 s
  · exact g32p_row13_cosetGeneratorStep_3993 s
  · exact g32p_row13_cosetGeneratorStep_3994 s
  · exact g32p_row13_cosetGeneratorStep_3995 s
  · exact g32p_row13_cosetGeneratorStep_3996 s
  · exact g32p_row13_cosetGeneratorStep_3997 s
  · exact g32p_row13_cosetGeneratorStep_3998 s
  · exact g32p_row13_cosetGeneratorStep_3999 s

theorem g32p_row13_cosetBranchBlock_0249 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 249 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 249 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 249 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_3984 s
  · exact g32p_row13_cosetBranchStep_3985 s
  · exact g32p_row13_cosetBranchStep_3986 s
  · exact g32p_row13_cosetBranchStep_3987 s
  · exact g32p_row13_cosetBranchStep_3988 s
  · exact g32p_row13_cosetBranchStep_3989 s
  · exact g32p_row13_cosetBranchStep_3990 s
  · exact g32p_row13_cosetBranchStep_3991 s
  · exact g32p_row13_cosetBranchStep_3992 s
  · exact g32p_row13_cosetBranchStep_3993 s
  · exact g32p_row13_cosetBranchStep_3994 s
  · exact g32p_row13_cosetBranchStep_3995 s
  · exact g32p_row13_cosetBranchStep_3996 s
  · exact g32p_row13_cosetBranchStep_3997 s
  · exact g32p_row13_cosetBranchStep_3998 s
  · exact g32p_row13_cosetBranchStep_3999 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4000 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4000) = g32p_row13_cosetRepresentatives 4000 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4000 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4000) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4000))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4000)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4000 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4000) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4000))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4000)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4001 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4001) = g32p_row13_cosetRepresentatives 4001 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4001 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4001) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4001))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4001)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4001 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4001) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4001))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4001)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4002 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4002) = g32p_row13_cosetRepresentatives 4002 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4002 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4002) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4002))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4002)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4002 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4002) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4002))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4002)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4003 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4003) = g32p_row13_cosetRepresentatives 4003 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4003 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4003) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4003))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4003)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4003 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4003) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4003))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4003)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4004 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4004) = g32p_row13_cosetRepresentatives 4004 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4004 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4004) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4004))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4004)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4004 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4004) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4004))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4004)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4005 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4005) = g32p_row13_cosetRepresentatives 4005 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4005 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4005) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4005))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4005)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4005 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4005) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4005))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4005)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4006 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4006) = g32p_row13_cosetRepresentatives 4006 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4006 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4006) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4006))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4006)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4006 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4006) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4006))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4006)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4007 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4007) = g32p_row13_cosetRepresentatives 4007 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4007 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4007) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4007))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4007)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4007 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4007) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4007))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4007)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4008 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4008) = g32p_row13_cosetRepresentatives 4008 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4008 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4008) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4008))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4008)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4008 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4008) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4008))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4008)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4009 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4009) = g32p_row13_cosetRepresentatives 4009 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4009 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4009) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4009))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4009)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4009 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4009) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4009))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4009)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4010 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4010) = g32p_row13_cosetRepresentatives 4010 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4010 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4010) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4010))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4010)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4010 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4010) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4010))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4010)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4011 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4011) = g32p_row13_cosetRepresentatives 4011 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4011 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4011) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4011))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4011)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4011 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4011) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4011))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4011)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4012 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4012) = g32p_row13_cosetRepresentatives 4012 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4012 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4012) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4012))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4012)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4012 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4012) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4012))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4012)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4013 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4013) = g32p_row13_cosetRepresentatives 4013 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4013 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4013) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4013))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4013)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4013 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4013) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4013))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4013)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4014 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4014) = g32p_row13_cosetRepresentatives 4014 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4014 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4014) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4014))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4014)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4014 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4014) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4014))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4014)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4015 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4015) = g32p_row13_cosetRepresentatives 4015 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4015 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4015) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4015))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4015)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4015 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4015) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4015))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4015)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0250 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 250 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 250 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4000
  · exact g32p_row13_cosetWord_4001
  · exact g32p_row13_cosetWord_4002
  · exact g32p_row13_cosetWord_4003
  · exact g32p_row13_cosetWord_4004
  · exact g32p_row13_cosetWord_4005
  · exact g32p_row13_cosetWord_4006
  · exact g32p_row13_cosetWord_4007
  · exact g32p_row13_cosetWord_4008
  · exact g32p_row13_cosetWord_4009
  · exact g32p_row13_cosetWord_4010
  · exact g32p_row13_cosetWord_4011
  · exact g32p_row13_cosetWord_4012
  · exact g32p_row13_cosetWord_4013
  · exact g32p_row13_cosetWord_4014
  · exact g32p_row13_cosetWord_4015

theorem g32p_row13_cosetGeneratorBlock_0250 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 250 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 250 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 250 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4000 s
  · exact g32p_row13_cosetGeneratorStep_4001 s
  · exact g32p_row13_cosetGeneratorStep_4002 s
  · exact g32p_row13_cosetGeneratorStep_4003 s
  · exact g32p_row13_cosetGeneratorStep_4004 s
  · exact g32p_row13_cosetGeneratorStep_4005 s
  · exact g32p_row13_cosetGeneratorStep_4006 s
  · exact g32p_row13_cosetGeneratorStep_4007 s
  · exact g32p_row13_cosetGeneratorStep_4008 s
  · exact g32p_row13_cosetGeneratorStep_4009 s
  · exact g32p_row13_cosetGeneratorStep_4010 s
  · exact g32p_row13_cosetGeneratorStep_4011 s
  · exact g32p_row13_cosetGeneratorStep_4012 s
  · exact g32p_row13_cosetGeneratorStep_4013 s
  · exact g32p_row13_cosetGeneratorStep_4014 s
  · exact g32p_row13_cosetGeneratorStep_4015 s

theorem g32p_row13_cosetBranchBlock_0250 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 250 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 250 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 250 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4000 s
  · exact g32p_row13_cosetBranchStep_4001 s
  · exact g32p_row13_cosetBranchStep_4002 s
  · exact g32p_row13_cosetBranchStep_4003 s
  · exact g32p_row13_cosetBranchStep_4004 s
  · exact g32p_row13_cosetBranchStep_4005 s
  · exact g32p_row13_cosetBranchStep_4006 s
  · exact g32p_row13_cosetBranchStep_4007 s
  · exact g32p_row13_cosetBranchStep_4008 s
  · exact g32p_row13_cosetBranchStep_4009 s
  · exact g32p_row13_cosetBranchStep_4010 s
  · exact g32p_row13_cosetBranchStep_4011 s
  · exact g32p_row13_cosetBranchStep_4012 s
  · exact g32p_row13_cosetBranchStep_4013 s
  · exact g32p_row13_cosetBranchStep_4014 s
  · exact g32p_row13_cosetBranchStep_4015 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4016 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4016) = g32p_row13_cosetRepresentatives 4016 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4016 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4016) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4016))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4016)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4016 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4016) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4016))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4016)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4017 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4017) = g32p_row13_cosetRepresentatives 4017 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4017 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4017) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4017))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4017)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4017 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4017) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4017))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4017)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4018 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4018) = g32p_row13_cosetRepresentatives 4018 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4018 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4018) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4018))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4018)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4018 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4018) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4018))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4018)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4019 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4019) = g32p_row13_cosetRepresentatives 4019 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4019 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4019) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4019))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4019)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4019 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4019) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4019))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4019)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4020 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4020) = g32p_row13_cosetRepresentatives 4020 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4020 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4020) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4020))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4020)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4020 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4020) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4020))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4020)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4021 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4021) = g32p_row13_cosetRepresentatives 4021 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4021 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4021) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4021))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4021)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4021 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4021) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4021))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4021)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4022 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4022) = g32p_row13_cosetRepresentatives 4022 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4022 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4022) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4022))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4022)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4022 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4022) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4022))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4022)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4023 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4023) = g32p_row13_cosetRepresentatives 4023 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4023 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4023) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4023))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4023)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4023 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4023) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4023))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4023)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4024 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4024) = g32p_row13_cosetRepresentatives 4024 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4024 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4024) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4024))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4024)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4024 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4024) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4024))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4024)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4025 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4025) = g32p_row13_cosetRepresentatives 4025 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4025 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4025) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4025))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4025)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4025 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4025) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4025))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4025)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4026 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4026) = g32p_row13_cosetRepresentatives 4026 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4026 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4026) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4026))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4026)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4026 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4026) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4026))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4026)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4027 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4027) = g32p_row13_cosetRepresentatives 4027 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4027 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4027) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4027))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4027)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4027 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4027) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4027))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4027)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4028 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4028) = g32p_row13_cosetRepresentatives 4028 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4028 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4028) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4028))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4028)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4028 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4028) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4028))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4028)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4029 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4029) = g32p_row13_cosetRepresentatives 4029 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4029 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4029) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4029))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4029)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4029 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4029) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4029))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4029)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4030 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4030) = g32p_row13_cosetRepresentatives 4030 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4030 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4030) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4030))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4030)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4030 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4030) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4030))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4030)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4031 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4031) = g32p_row13_cosetRepresentatives 4031 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4031 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4031) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4031))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4031)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4031 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4031) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4031))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4031)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0251 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 251 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 251 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4016
  · exact g32p_row13_cosetWord_4017
  · exact g32p_row13_cosetWord_4018
  · exact g32p_row13_cosetWord_4019
  · exact g32p_row13_cosetWord_4020
  · exact g32p_row13_cosetWord_4021
  · exact g32p_row13_cosetWord_4022
  · exact g32p_row13_cosetWord_4023
  · exact g32p_row13_cosetWord_4024
  · exact g32p_row13_cosetWord_4025
  · exact g32p_row13_cosetWord_4026
  · exact g32p_row13_cosetWord_4027
  · exact g32p_row13_cosetWord_4028
  · exact g32p_row13_cosetWord_4029
  · exact g32p_row13_cosetWord_4030
  · exact g32p_row13_cosetWord_4031

theorem g32p_row13_cosetGeneratorBlock_0251 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 251 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 251 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 251 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4016 s
  · exact g32p_row13_cosetGeneratorStep_4017 s
  · exact g32p_row13_cosetGeneratorStep_4018 s
  · exact g32p_row13_cosetGeneratorStep_4019 s
  · exact g32p_row13_cosetGeneratorStep_4020 s
  · exact g32p_row13_cosetGeneratorStep_4021 s
  · exact g32p_row13_cosetGeneratorStep_4022 s
  · exact g32p_row13_cosetGeneratorStep_4023 s
  · exact g32p_row13_cosetGeneratorStep_4024 s
  · exact g32p_row13_cosetGeneratorStep_4025 s
  · exact g32p_row13_cosetGeneratorStep_4026 s
  · exact g32p_row13_cosetGeneratorStep_4027 s
  · exact g32p_row13_cosetGeneratorStep_4028 s
  · exact g32p_row13_cosetGeneratorStep_4029 s
  · exact g32p_row13_cosetGeneratorStep_4030 s
  · exact g32p_row13_cosetGeneratorStep_4031 s

theorem g32p_row13_cosetBranchBlock_0251 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 251 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 251 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 251 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4016 s
  · exact g32p_row13_cosetBranchStep_4017 s
  · exact g32p_row13_cosetBranchStep_4018 s
  · exact g32p_row13_cosetBranchStep_4019 s
  · exact g32p_row13_cosetBranchStep_4020 s
  · exact g32p_row13_cosetBranchStep_4021 s
  · exact g32p_row13_cosetBranchStep_4022 s
  · exact g32p_row13_cosetBranchStep_4023 s
  · exact g32p_row13_cosetBranchStep_4024 s
  · exact g32p_row13_cosetBranchStep_4025 s
  · exact g32p_row13_cosetBranchStep_4026 s
  · exact g32p_row13_cosetBranchStep_4027 s
  · exact g32p_row13_cosetBranchStep_4028 s
  · exact g32p_row13_cosetBranchStep_4029 s
  · exact g32p_row13_cosetBranchStep_4030 s
  · exact g32p_row13_cosetBranchStep_4031 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4032 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4032) = g32p_row13_cosetRepresentatives 4032 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4032 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4032) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4032))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4032)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4032 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4032) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4032))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4032)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4033 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4033) = g32p_row13_cosetRepresentatives 4033 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4033 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4033) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4033))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4033)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4033 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4033) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4033))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4033)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4034 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4034) = g32p_row13_cosetRepresentatives 4034 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4034 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4034) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4034))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4034)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4034 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4034) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4034))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4034)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4035 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4035) = g32p_row13_cosetRepresentatives 4035 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4035 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4035) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4035))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4035)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4035 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4035) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4035))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4035)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4036 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4036) = g32p_row13_cosetRepresentatives 4036 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4036 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4036) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4036))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4036)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4036 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4036) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4036))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4036)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4037 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4037) = g32p_row13_cosetRepresentatives 4037 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4037 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4037) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4037))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4037)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4037 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4037) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4037))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4037)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4038 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4038) = g32p_row13_cosetRepresentatives 4038 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4038 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4038) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4038))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4038)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4038 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4038) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4038))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4038)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4039 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4039) = g32p_row13_cosetRepresentatives 4039 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4039 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4039) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4039))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4039)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4039 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4039) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4039))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4039)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4040 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4040) = g32p_row13_cosetRepresentatives 4040 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4040 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4040) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4040))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4040)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4040 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4040) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4040))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4040)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4041 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4041) = g32p_row13_cosetRepresentatives 4041 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4041 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4041) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4041))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4041)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4041 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4041) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4041))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4041)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4042 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4042) = g32p_row13_cosetRepresentatives 4042 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4042 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4042) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4042))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4042)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4042 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4042) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4042))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4042)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4043 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4043) = g32p_row13_cosetRepresentatives 4043 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4043 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4043) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4043))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4043)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4043 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4043) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4043))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4043)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4044 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4044) = g32p_row13_cosetRepresentatives 4044 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4044 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4044) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4044))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4044)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4044 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4044) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4044))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4044)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4045 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4045) = g32p_row13_cosetRepresentatives 4045 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4045 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4045) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4045))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4045)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4045 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4045) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4045))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4045)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4046 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4046) = g32p_row13_cosetRepresentatives 4046 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4046 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4046) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4046))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4046)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4046 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4046) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4046))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4046)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4047 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4047) = g32p_row13_cosetRepresentatives 4047 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4047 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4047) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4047))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4047)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4047 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4047) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4047))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4047)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0252 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 252 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 252 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4032
  · exact g32p_row13_cosetWord_4033
  · exact g32p_row13_cosetWord_4034
  · exact g32p_row13_cosetWord_4035
  · exact g32p_row13_cosetWord_4036
  · exact g32p_row13_cosetWord_4037
  · exact g32p_row13_cosetWord_4038
  · exact g32p_row13_cosetWord_4039
  · exact g32p_row13_cosetWord_4040
  · exact g32p_row13_cosetWord_4041
  · exact g32p_row13_cosetWord_4042
  · exact g32p_row13_cosetWord_4043
  · exact g32p_row13_cosetWord_4044
  · exact g32p_row13_cosetWord_4045
  · exact g32p_row13_cosetWord_4046
  · exact g32p_row13_cosetWord_4047

theorem g32p_row13_cosetGeneratorBlock_0252 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 252 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 252 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 252 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4032 s
  · exact g32p_row13_cosetGeneratorStep_4033 s
  · exact g32p_row13_cosetGeneratorStep_4034 s
  · exact g32p_row13_cosetGeneratorStep_4035 s
  · exact g32p_row13_cosetGeneratorStep_4036 s
  · exact g32p_row13_cosetGeneratorStep_4037 s
  · exact g32p_row13_cosetGeneratorStep_4038 s
  · exact g32p_row13_cosetGeneratorStep_4039 s
  · exact g32p_row13_cosetGeneratorStep_4040 s
  · exact g32p_row13_cosetGeneratorStep_4041 s
  · exact g32p_row13_cosetGeneratorStep_4042 s
  · exact g32p_row13_cosetGeneratorStep_4043 s
  · exact g32p_row13_cosetGeneratorStep_4044 s
  · exact g32p_row13_cosetGeneratorStep_4045 s
  · exact g32p_row13_cosetGeneratorStep_4046 s
  · exact g32p_row13_cosetGeneratorStep_4047 s

theorem g32p_row13_cosetBranchBlock_0252 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 252 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 252 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 252 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4032 s
  · exact g32p_row13_cosetBranchStep_4033 s
  · exact g32p_row13_cosetBranchStep_4034 s
  · exact g32p_row13_cosetBranchStep_4035 s
  · exact g32p_row13_cosetBranchStep_4036 s
  · exact g32p_row13_cosetBranchStep_4037 s
  · exact g32p_row13_cosetBranchStep_4038 s
  · exact g32p_row13_cosetBranchStep_4039 s
  · exact g32p_row13_cosetBranchStep_4040 s
  · exact g32p_row13_cosetBranchStep_4041 s
  · exact g32p_row13_cosetBranchStep_4042 s
  · exact g32p_row13_cosetBranchStep_4043 s
  · exact g32p_row13_cosetBranchStep_4044 s
  · exact g32p_row13_cosetBranchStep_4045 s
  · exact g32p_row13_cosetBranchStep_4046 s
  · exact g32p_row13_cosetBranchStep_4047 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4048 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4048) = g32p_row13_cosetRepresentatives 4048 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4048 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4048) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4048))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4048)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4048 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4048) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4048))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4048)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4049 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4049) = g32p_row13_cosetRepresentatives 4049 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4049 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4049) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4049))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4049)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4049 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4049) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4049))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4049)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4050 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4050) = g32p_row13_cosetRepresentatives 4050 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4050 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4050) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4050))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4050)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4050 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4050) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4050))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4050)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4051 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4051) = g32p_row13_cosetRepresentatives 4051 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4051 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4051) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4051))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4051)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4051 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4051) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4051))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4051)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4052 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4052) = g32p_row13_cosetRepresentatives 4052 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4052 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4052) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4052))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4052)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4052 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4052) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4052))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4052)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4053 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4053) = g32p_row13_cosetRepresentatives 4053 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4053 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4053) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4053))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4053)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4053 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4053) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4053))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4053)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4054 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4054) = g32p_row13_cosetRepresentatives 4054 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4054 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4054) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4054))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4054)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4054 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4054) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4054))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4054)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4055 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4055) = g32p_row13_cosetRepresentatives 4055 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4055 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4055) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4055))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4055)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4055 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4055) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4055))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4055)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4056 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4056) = g32p_row13_cosetRepresentatives 4056 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4056 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4056) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4056))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4056)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4056 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4056) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4056))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4056)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4057 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4057) = g32p_row13_cosetRepresentatives 4057 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4057 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4057) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4057))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4057)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4057 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4057) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4057))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4057)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4058 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4058) = g32p_row13_cosetRepresentatives 4058 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4058 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4058) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4058))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4058)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4058 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4058) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4058))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4058)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4059 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4059) = g32p_row13_cosetRepresentatives 4059 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4059 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4059) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4059))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4059)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4059 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4059) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4059))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4059)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4060 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4060) = g32p_row13_cosetRepresentatives 4060 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4060 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4060) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4060))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4060)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4060 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4060) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4060))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4060)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4061 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4061) = g32p_row13_cosetRepresentatives 4061 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4061 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4061) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4061))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4061)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4061 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4061) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4061))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4061)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4062 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4062) = g32p_row13_cosetRepresentatives 4062 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4062 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4062) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4062))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4062)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4062 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4062) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4062))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4062)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4063 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4063) = g32p_row13_cosetRepresentatives 4063 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4063 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4063) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4063))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4063)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4063 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4063) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4063))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4063)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0253 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 253 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 253 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4048
  · exact g32p_row13_cosetWord_4049
  · exact g32p_row13_cosetWord_4050
  · exact g32p_row13_cosetWord_4051
  · exact g32p_row13_cosetWord_4052
  · exact g32p_row13_cosetWord_4053
  · exact g32p_row13_cosetWord_4054
  · exact g32p_row13_cosetWord_4055
  · exact g32p_row13_cosetWord_4056
  · exact g32p_row13_cosetWord_4057
  · exact g32p_row13_cosetWord_4058
  · exact g32p_row13_cosetWord_4059
  · exact g32p_row13_cosetWord_4060
  · exact g32p_row13_cosetWord_4061
  · exact g32p_row13_cosetWord_4062
  · exact g32p_row13_cosetWord_4063

theorem g32p_row13_cosetGeneratorBlock_0253 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 253 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 253 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 253 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4048 s
  · exact g32p_row13_cosetGeneratorStep_4049 s
  · exact g32p_row13_cosetGeneratorStep_4050 s
  · exact g32p_row13_cosetGeneratorStep_4051 s
  · exact g32p_row13_cosetGeneratorStep_4052 s
  · exact g32p_row13_cosetGeneratorStep_4053 s
  · exact g32p_row13_cosetGeneratorStep_4054 s
  · exact g32p_row13_cosetGeneratorStep_4055 s
  · exact g32p_row13_cosetGeneratorStep_4056 s
  · exact g32p_row13_cosetGeneratorStep_4057 s
  · exact g32p_row13_cosetGeneratorStep_4058 s
  · exact g32p_row13_cosetGeneratorStep_4059 s
  · exact g32p_row13_cosetGeneratorStep_4060 s
  · exact g32p_row13_cosetGeneratorStep_4061 s
  · exact g32p_row13_cosetGeneratorStep_4062 s
  · exact g32p_row13_cosetGeneratorStep_4063 s

theorem g32p_row13_cosetBranchBlock_0253 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 253 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 253 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 253 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4048 s
  · exact g32p_row13_cosetBranchStep_4049 s
  · exact g32p_row13_cosetBranchStep_4050 s
  · exact g32p_row13_cosetBranchStep_4051 s
  · exact g32p_row13_cosetBranchStep_4052 s
  · exact g32p_row13_cosetBranchStep_4053 s
  · exact g32p_row13_cosetBranchStep_4054 s
  · exact g32p_row13_cosetBranchStep_4055 s
  · exact g32p_row13_cosetBranchStep_4056 s
  · exact g32p_row13_cosetBranchStep_4057 s
  · exact g32p_row13_cosetBranchStep_4058 s
  · exact g32p_row13_cosetBranchStep_4059 s
  · exact g32p_row13_cosetBranchStep_4060 s
  · exact g32p_row13_cosetBranchStep_4061 s
  · exact g32p_row13_cosetBranchStep_4062 s
  · exact g32p_row13_cosetBranchStep_4063 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4064 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4064) = g32p_row13_cosetRepresentatives 4064 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4064 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4064) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4064))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4064)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4064 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4064) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4064))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4064)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4065 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4065) = g32p_row13_cosetRepresentatives 4065 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4065 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4065) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4065))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4065)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4065 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4065) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4065))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4065)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4066 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4066) = g32p_row13_cosetRepresentatives 4066 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4066 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4066) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4066))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4066)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4066 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4066) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4066))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4066)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4067 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4067) = g32p_row13_cosetRepresentatives 4067 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4067 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4067) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4067))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4067)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4067 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4067) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4067))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4067)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4068 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4068) = g32p_row13_cosetRepresentatives 4068 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4068 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4068) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4068))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4068)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4068 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4068) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4068))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4068)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4069 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4069) = g32p_row13_cosetRepresentatives 4069 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4069 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4069) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4069))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4069)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4069 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4069) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4069))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4069)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4070 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4070) = g32p_row13_cosetRepresentatives 4070 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4070 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4070) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4070))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4070)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4070 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4070) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4070))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4070)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4071 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4071) = g32p_row13_cosetRepresentatives 4071 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4071 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4071) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4071))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4071)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4071 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4071) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4071))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4071)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4072 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4072) = g32p_row13_cosetRepresentatives 4072 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4072 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4072) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4072))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4072)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4072 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4072) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4072))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4072)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4073 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4073) = g32p_row13_cosetRepresentatives 4073 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4073 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4073) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4073))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4073)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4073 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4073) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4073))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4073)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4074 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4074) = g32p_row13_cosetRepresentatives 4074 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4074 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4074) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4074))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4074)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4074 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4074) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4074))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4074)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4075 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4075) = g32p_row13_cosetRepresentatives 4075 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4075 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4075) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4075))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4075)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4075 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4075) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4075))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4075)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4076 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4076) = g32p_row13_cosetRepresentatives 4076 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4076 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4076) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4076))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4076)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4076 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4076) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4076))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4076)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4077 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4077) = g32p_row13_cosetRepresentatives 4077 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4077 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4077) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4077))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4077)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4077 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4077) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4077))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4077)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4078 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4078) = g32p_row13_cosetRepresentatives 4078 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4078 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4078) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4078))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4078)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4078 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4078) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4078))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4078)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4079 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4079) = g32p_row13_cosetRepresentatives 4079 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4079 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4079) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4079))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4079)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4079 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4079) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4079))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4079)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0254 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 254 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 254 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4064
  · exact g32p_row13_cosetWord_4065
  · exact g32p_row13_cosetWord_4066
  · exact g32p_row13_cosetWord_4067
  · exact g32p_row13_cosetWord_4068
  · exact g32p_row13_cosetWord_4069
  · exact g32p_row13_cosetWord_4070
  · exact g32p_row13_cosetWord_4071
  · exact g32p_row13_cosetWord_4072
  · exact g32p_row13_cosetWord_4073
  · exact g32p_row13_cosetWord_4074
  · exact g32p_row13_cosetWord_4075
  · exact g32p_row13_cosetWord_4076
  · exact g32p_row13_cosetWord_4077
  · exact g32p_row13_cosetWord_4078
  · exact g32p_row13_cosetWord_4079

theorem g32p_row13_cosetGeneratorBlock_0254 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 254 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 254 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 254 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4064 s
  · exact g32p_row13_cosetGeneratorStep_4065 s
  · exact g32p_row13_cosetGeneratorStep_4066 s
  · exact g32p_row13_cosetGeneratorStep_4067 s
  · exact g32p_row13_cosetGeneratorStep_4068 s
  · exact g32p_row13_cosetGeneratorStep_4069 s
  · exact g32p_row13_cosetGeneratorStep_4070 s
  · exact g32p_row13_cosetGeneratorStep_4071 s
  · exact g32p_row13_cosetGeneratorStep_4072 s
  · exact g32p_row13_cosetGeneratorStep_4073 s
  · exact g32p_row13_cosetGeneratorStep_4074 s
  · exact g32p_row13_cosetGeneratorStep_4075 s
  · exact g32p_row13_cosetGeneratorStep_4076 s
  · exact g32p_row13_cosetGeneratorStep_4077 s
  · exact g32p_row13_cosetGeneratorStep_4078 s
  · exact g32p_row13_cosetGeneratorStep_4079 s

theorem g32p_row13_cosetBranchBlock_0254 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 254 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 254 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 254 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4064 s
  · exact g32p_row13_cosetBranchStep_4065 s
  · exact g32p_row13_cosetBranchStep_4066 s
  · exact g32p_row13_cosetBranchStep_4067 s
  · exact g32p_row13_cosetBranchStep_4068 s
  · exact g32p_row13_cosetBranchStep_4069 s
  · exact g32p_row13_cosetBranchStep_4070 s
  · exact g32p_row13_cosetBranchStep_4071 s
  · exact g32p_row13_cosetBranchStep_4072 s
  · exact g32p_row13_cosetBranchStep_4073 s
  · exact g32p_row13_cosetBranchStep_4074 s
  · exact g32p_row13_cosetBranchStep_4075 s
  · exact g32p_row13_cosetBranchStep_4076 s
  · exact g32p_row13_cosetBranchStep_4077 s
  · exact g32p_row13_cosetBranchStep_4078 s
  · exact g32p_row13_cosetBranchStep_4079 s


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_cosetWord_4080 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4080) = g32p_row13_cosetRepresentatives 4080 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4080 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4080) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4080))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4080)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4080 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4080) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4080))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4080)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4081 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4081) = g32p_row13_cosetRepresentatives 4081 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4081 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4081) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4081))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4081)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4081 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4081) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4081))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4081)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4082 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4082) = g32p_row13_cosetRepresentatives 4082 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4082 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4082) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4082))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4082)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4082 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4082) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4082))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4082)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4083 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4083) = g32p_row13_cosetRepresentatives 4083 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4083 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4083) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4083))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4083)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4083 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4083) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4083))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4083)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4084 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4084) = g32p_row13_cosetRepresentatives 4084 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4084 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4084) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4084))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4084)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4084 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4084) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4084))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4084)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4085 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4085) = g32p_row13_cosetRepresentatives 4085 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4085 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4085) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4085))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4085)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4085 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4085) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4085))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4085)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4086 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4086) = g32p_row13_cosetRepresentatives 4086 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4086 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4086) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4086))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4086)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4086 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4086) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4086))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4086)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4087 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4087) = g32p_row13_cosetRepresentatives 4087 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4087 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4087) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4087))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4087)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4087 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4087) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4087))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4087)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4088 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4088) = g32p_row13_cosetRepresentatives 4088 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4088 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4088) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4088))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4088)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4088 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4088) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4088))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4088)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4089 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4089) = g32p_row13_cosetRepresentatives 4089 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4089 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4089) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4089))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4089)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4089 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4089) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4089))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4089)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4090 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4090) = g32p_row13_cosetRepresentatives 4090 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4090 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4090) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4090))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4090)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4090 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4090) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4090))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4090)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4091 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4091) = g32p_row13_cosetRepresentatives 4091 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4091 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4091) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4091))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4091)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4091 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4091) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4091))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4091)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4092 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4092) = g32p_row13_cosetRepresentatives 4092 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4092 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4092) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4092))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4092)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4092 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4092) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4092))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4092)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4093 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4093) = g32p_row13_cosetRepresentatives 4093 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4093 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4093) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4093))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4093)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4093 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4093) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4093))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4093)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4094 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4094) = g32p_row13_cosetRepresentatives 4094 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4094 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4094) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4094))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4094)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4094 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4094) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4094))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4094)) := by
  decide +kernel

theorem g32p_row13_cosetWord_4095 :
    g32p_archiveIntegralWord (g32p_row13_cosetWords 4095) = g32p_row13_cosetRepresentatives 4095 := by
  decide +kernel

theorem g32p_row13_cosetGeneratorStep_4095 : ∀ s : Fin 4,
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives 4095) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s 4095))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s 4095)) := by
  decide +kernel

theorem g32p_row13_cosetBranchStep_4095 : ∀ s : Fin 3,
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives 4095) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s 4095))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s 4095)) := by
  decide +kernel

theorem g32p_row13_cosetWordBlock_0255 (r : Fin 16) :
    g32p_archiveIntegralWord (g32p_row13_cosetWords (g32p_finBlockIndex 6480 255 r)) = g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 255 r) := by
  fin_cases r
  · exact g32p_row13_cosetWord_4080
  · exact g32p_row13_cosetWord_4081
  · exact g32p_row13_cosetWord_4082
  · exact g32p_row13_cosetWord_4083
  · exact g32p_row13_cosetWord_4084
  · exact g32p_row13_cosetWord_4085
  · exact g32p_row13_cosetWord_4086
  · exact g32p_row13_cosetWord_4087
  · exact g32p_row13_cosetWord_4088
  · exact g32p_row13_cosetWord_4089
  · exact g32p_row13_cosetWord_4090
  · exact g32p_row13_cosetWord_4091
  · exact g32p_row13_cosetWord_4092
  · exact g32p_row13_cosetWord_4093
  · exact g32p_row13_cosetWord_4094
  · exact g32p_row13_cosetWord_4095

theorem g32p_row13_cosetGeneratorBlock_0255 (s : Fin 4) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 255 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetGeneratorNext s (g32p_finBlockIndex 6480 255 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetGeneratorFactor s (g32p_finBlockIndex 6480 255 r))) := by
  fin_cases r
  · exact g32p_row13_cosetGeneratorStep_4080 s
  · exact g32p_row13_cosetGeneratorStep_4081 s
  · exact g32p_row13_cosetGeneratorStep_4082 s
  · exact g32p_row13_cosetGeneratorStep_4083 s
  · exact g32p_row13_cosetGeneratorStep_4084 s
  · exact g32p_row13_cosetGeneratorStep_4085 s
  · exact g32p_row13_cosetGeneratorStep_4086 s
  · exact g32p_row13_cosetGeneratorStep_4087 s
  · exact g32p_row13_cosetGeneratorStep_4088 s
  · exact g32p_row13_cosetGeneratorStep_4089 s
  · exact g32p_row13_cosetGeneratorStep_4090 s
  · exact g32p_row13_cosetGeneratorStep_4091 s
  · exact g32p_row13_cosetGeneratorStep_4092 s
  · exact g32p_row13_cosetGeneratorStep_4093 s
  · exact g32p_row13_cosetGeneratorStep_4094 s
  · exact g32p_row13_cosetGeneratorStep_4095 s

theorem g32p_row13_cosetBranchBlock_0255 (s : Fin 3) (r : Fin 16) :
    HurwitzPrymRex_mmul (g32p_row13_cosetBranchMatrices s) (g32p_row13_cosetRepresentatives (g32p_finBlockIndex 6480 255 r)) =
      HurwitzPrymRex_mmul (g32p_row13_cosetRepresentatives (g32p_row13_cosetBranchNext s (g32p_finBlockIndex 6480 255 r)))
        (g32p_row13_groupNodes (g32p_row13_cosetBranchFactor s (g32p_finBlockIndex 6480 255 r))) := by
  fin_cases r
  · exact g32p_row13_cosetBranchStep_4080 s
  · exact g32p_row13_cosetBranchStep_4081 s
  · exact g32p_row13_cosetBranchStep_4082 s
  · exact g32p_row13_cosetBranchStep_4083 s
  · exact g32p_row13_cosetBranchStep_4084 s
  · exact g32p_row13_cosetBranchStep_4085 s
  · exact g32p_row13_cosetBranchStep_4086 s
  · exact g32p_row13_cosetBranchStep_4087 s
  · exact g32p_row13_cosetBranchStep_4088 s
  · exact g32p_row13_cosetBranchStep_4089 s
  · exact g32p_row13_cosetBranchStep_4090 s
  · exact g32p_row13_cosetBranchStep_4091 s
  · exact g32p_row13_cosetBranchStep_4092 s
  · exact g32p_row13_cosetBranchStep_4093 s
  · exact g32p_row13_cosetBranchStep_4094 s
  · exact g32p_row13_cosetBranchStep_4095 s


end HodgeLean.Foundations.Program

end
